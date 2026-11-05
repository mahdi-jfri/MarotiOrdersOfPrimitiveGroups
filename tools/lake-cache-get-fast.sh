#!/usr/bin/env bash
# lake-cache-get-fast.sh — restore CFSG's oleans, and those of its dependencies, from the public
# Lake artifact cache, in minutes instead of the hours `lake cache get` takes.
#
# Linux x86_64 only for now: CFSG's lakefile does not declare `platformIndependent = true`, so
# Lake files CFSG's cache under the platform it was built on (x86_64-unknown-linux-gnu). The
# script stops with an error on any other platform; there, `lake build` compiles CFSG itself.
#
# Usage: bash lake-cache-get-fast.sh <cfsg-checkout>
#
# Reads PUBLIC_ARTIFACT_ENDPOINT / PUBLIC_REVISION_ENDPOINT from the environment, defaulting to
# the public cache. The endpoints are public, anonymous and not secret, so this runs from a
# checkout with no setup.
#
# Looks up every package of the manifest at its own revision: CFSG at HEAD, backtracking up to
# LAKE_CACHE_MAX_REVS revisions from HEAD (default 100; 0 means the complete available history),
# and each dependency at its manifest revision, under its GitHub owner/name.
#
# On an unclean outcome it discards the fetch and leaves Lake's cache as it was, so the build
# proceeds exactly as if the cache were switched off.
#
# License and attribution
#
# This script is a modified version of lake-cache-get.sh from the TauCeti project's
# TauCetiTools (https://github.com/TauCetiProject/TauCetiTools,
# tauceti_tools/assets/scripts/lake-cache-get.sh), by the TauCeti project contributors,
# licensed under the Apache License, Version 2.0. Axiom Math modified it to fetch CFSG and
# every dependency, download in parallel with each archive's hash checked, unpack every module
# with one leantar run, write Lake's cache records directly, and refuse platforms other than
# Linux x86_64. The modifications are also licensed under the Apache License, Version 2.0.
#
# Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file
# except in compliance with the License. A copy of the License is published beside this script
# at https://cfsg-downloads.axiommath.workers.dev/lake/LICENSE-Apache-2.0.txt and at
# https://www.apache.org/licenses/LICENSE-2.0. Unless required by applicable law or agreed to
# in writing, software distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for
# the specific language governing permissions and limitations under the License.
#
# SPDX-License-Identifier: Apache-2.0
set -euo pipefail

if [ "$(uname -s)" != Linux ] || [ "$(uname -m)" != x86_64 ]; then
  echo "::error::CFSG's Lake cache serves Linux x86_64 only for now; this machine is $(uname -s) $(uname -m)." >&2
  echo "::error::Run \`lake build\` without the cache to compile CFSG on this platform." >&2
  exit 1
fi

PROJECT_DIR="$(cd "${1:?usage: lake-cache-get-fast.sh <cfsg-checkout>}" && pwd)"
export PUBLIC_ARTIFACT_ENDPOINT="${PUBLIC_ARTIFACT_ENDPOINT:-https://cfsg-downloads.axiommath.workers.dev/lake/artifacts}"
export PUBLIC_REVISION_ENDPOINT="${PUBLIC_REVISION_ENDPOINT:-https://cfsg-downloads.axiommath.workers.dev/lake/revisions}"
export LAKE_CACHE_MAX_REVS="${LAKE_CACHE_MAX_REVS:-100}"
case "$LAKE_CACHE_MAX_REVS" in
  ''|*[!0-9]*) echo "::error::LAKE_CACHE_MAX_REVS must be a natural number"; exit 1 ;;
esac
cd "$PROJECT_DIR"
[ -f lake-manifest.json ] || { echo "::error::$PROJECT_DIR has no lake-manifest.json"; exit 1; }

CACHE="$(lake env printenv LAKE_CACHE_DIR)"
if [ -z "$CACHE" ]; then
  echo "::notice::Lake's cache is switched off (LAKE_CACHE_DIR is empty); nothing to do"
  exit 0
fi
LEANTAR="$(lean --print-prefix)/bin/leantar"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/lake-cache-get.XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

echo 'def main : IO Unit := IO.println System.Platform.target' > "$WORK/platform.lean"
PLATFORM="$(lean --run "$WORK/platform.lean" 2>/dev/null || true)"
[ -n "$PLATFORM" ] || echo "::warning::could not ask Lean for its platform; only platform-independent caches can be found"

python3 - "$CACHE" "$LEANTAR" "$PLATFORM" "$WORK" <<'PY'
import json, multiprocessing, os, re, shutil, struct, subprocess, sys
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

CACHE, LEANTAR, PLATFORM, WORK = Path(sys.argv[1]), sys.argv[2], sys.argv[3], Path(sys.argv[4])
ARTIFACTS = os.environ["PUBLIC_ARTIFACT_ENDPOINT"]
REVISIONS = os.environ["PUBLIC_REVISION_ENDPOINT"]
MAX_REVS = int(os.environ["LAKE_CACHE_MAX_REVS"])
STAGE = Path(f"{CACHE}.cfsg-get.{os.getpid()}")
STACK_KB = 1024 * 1024
M, R, MASK = 0xC6A4A7935BD1E995, 47, (1 << 64) - 1

def lake_hash(path):
    data = Path(path).read_bytes()
    h = (11 ^ (len(data) * M)) & MASK
    n = len(data) // 8 * 8
    for (k,) in struct.iter_unpack("<Q", memoryview(data)[:n]):
        k = (k * M) & MASK
        k ^= k >> R
        h = ((h ^ ((k * M) & MASK)) * M) & MASK
    if n < len(data):
        h = ((h ^ int.from_bytes(data[n:], "little")) * M) & MASK
    h ^= h >> R
    h = (h * M) & MASK
    k = ((h ^ (h >> R)) * M) & MASK
    k ^= k >> R
    k ^= M
    return f"{((1723 ^ k) * M) & MASK:016x}"

def corrupt(path):
    return lake_hash(path) != os.path.basename(path).split(".", 1)[0]

# Discarding the staging cache must never fail. Rename first (atomic, and unaffected by
# concurrent writes under the old path), then delete the renamed copy best-effort.
def discard_cache(d):
    if not d.exists():
        return
    tmp = Path(f"{d}.discard.{os.getpid()}")
    try:
        d.rename(tmp)
    except OSError:
        tmp = d
    subprocess.run(["rm", "-rf", str(tmp)])

def fetch(url, dst):
    return subprocess.run(["curl", "-sfL", "--retry", "3", "-o", str(dst), url]).returncode == 0

def fetch_all(pairs):
    missing = []
    for i in range(0, len(pairs), 5000):
        part = pairs[i:i + 5000]
        cfg = WORK / "batch.curl"
        cfg.write_text("".join(f'url = "{url}"\noutput = "{f}.part"\n' for url, f in part))
        subprocess.run(["curl", "-Z", "--parallel-max", "64", "-sfL", "--retry", "5", "-K", str(cfg)])
        for _, f in part:
            if os.path.exists(f"{f}.part"):
                os.replace(f"{f}.part", f)
            else:
                missing.append(f)
    return missing

for d in CACHE.parent.glob(f"{CACHE.name}.cfsg-get.*"):
    try:
        os.kill(int(d.name.rsplit(".", 1)[1]), 0)
    except ProcessLookupError:
        discard_cache(d)
    except (ValueError, PermissionError):
        pass
(STAGE / "artifacts").mkdir(parents=True)

man = json.loads(Path("lake-manifest.json").read_text())
toolchain = Path("lean-toolchain").read_text().strip().replace("/", "--").replace(":", "---")
head = ["git", "rev-list", "HEAD"] + (["-n", str(MAX_REVS)] if MAX_REVS else [])
pkgs = [(man["name"], "AxiomMath/CFSG", subprocess.run(head, capture_output=True, text=True).stdout.split(),
         Path("."))]
for p in man.get("packages", []):
    g = re.match(r"(?:https?://|git@)github\.com[/:]([^/]+)/([^/]+?)(?:\.git)?/?$", p.get("url") or "")
    pkgs.append((p["name"], f"{g.group(1)}/{g.group(2)}" if g else f"lake-deps/{p['name']}", [p["rev"]],
                 Path(".lake/packages") / p["name"]))

need, lists, maps = [], {}, []
for name, repo, commits, pdir in pkgs:
    variants = [f"{repo}/tc/{toolchain}", repo]
    if PLATFORM:
        variants = [f"{repo}/pt/{PLATFORM}/tc/{toolchain}", variants[0], f"{repo}/pt/{PLATFORM}", repo]
    (STAGE / "revisions" / name).mkdir(parents=True, exist_ok=True)
    found = WORK / f"{name}.jsonl"
    base = next((f"{REVISIONS}/{v}/{c}" for c in commits for v in variants
                 if fetch(f"{REVISIONS}/{v}/{c}.jsonl", found)), None)
    if base is None:
        print(f"::notice::nothing published for {name} at its revision; lake build will compile it")
        continue
    mapfile = STAGE / "revisions" / name / f"{base.rsplit('/', 1)[1]}.jsonl"
    shutil.move(found, mapfile)
    maps.append((name, mapfile.name))
    values = {v for v in (json.loads(l)[1] for l in mapfile.read_text().splitlines()[1:]) if isinstance(v, str)}
    for v in values:
        if not (CACHE / "artifacts" / v).exists():
            need.append((f"{ARTIFACTS}/{repo}/{v.split('.', 1)[0]}.art", str(STAGE / "artifacts" / v)))
    mods = WORK / f"{name}.modules.jsonl"
    if fetch(f"{base}.modules.jsonl", mods):
        lists[name] = (mods, pdir)
    else:
        print(f"::notice::no module list published for {name}; lake build will unpack it")
    print(f"{name}: {len(values)} artifacts ({repo} at {base.rsplit('/', 1)[1][:12]})", flush=True)

clean = True
if need:
    print(f"downloading {len(need)} artifacts ...", flush=True)
    missing = set(fetch_all(need))
    with ProcessPoolExecutor(mp_context=multiprocessing.get_context("fork")) as ex:
        arrived = [f for _, f in need if f not in missing]
        badlist = [f for f, b in zip(arrived, ex.map(corrupt, arrived, chunksize=64)) if b]
    # Fetch the missing and corrupt artifacts again, a few times, before giving up.
    for attempt in range(5):
        retry = [(u, f) for u, f in need if f in missing or f in badlist]
        if not retry:
            break
        print(f"refetching {len(retry)} artifacts (attempt {attempt + 1}) ...", flush=True)
        for _, f in retry:
            if os.path.exists(f):
                os.remove(f)
        missing = set(fetch_all(retry))
        badlist = [f for _, f in retry if f not in missing and corrupt(f)]
    bad = len(badlist)
    clean = not missing and not bad
    if not clean:
        print(f"{len(missing)} artifacts missing, {bad} failed their hash check")
if not clean:
    print(f"::warning::the fetch did not complete cleanly; discarding it and leaving Lake's cache ({CACHE}) as it was")
    discard_cache(STAGE)
    sys.exit(0)

for d, _, fs in os.walk(STAGE):
    for f in fs:
        src = os.path.join(d, f)
        dst = CACHE / os.path.relpath(src, STAGE)
        if not dst.exists():
            dst.parent.mkdir(parents=True, exist_ok=True)
            os.replace(src, dst)
discard_cache(STAGE)

for name, fn in maps:
    out = CACHE / "outputs" / name
    out.mkdir(parents=True, exist_ok=True)
    for line in (CACHE / "revisions" / name / fn).read_text().splitlines()[1:]:
        dep, val = json.loads(line)[:2]
        rec = out / f"{dep}.json"
        if not rec.exists():
            rec.write_text(json.dumps(val))

spec = []
for mods, pdir in lists.values():
    build = (pdir / ".lake" / "build").resolve()
    for dep, rel, ltar in (json.loads(l) for l in mods.read_text().splitlines()):
        d = os.path.dirname(rel)
        dirs = [str(build / "lib" / "lean" / d), str(build / "ir" / d)]
        for x in dirs:
            os.makedirs(x, exist_ok=True)
        spec.append({"file": str(CACHE / "artifacts" / ltar), "base": dirs, "hash": dep})
print(f"unpacking {len(spec)} modules ...", flush=True)
raised = f'ulimit -s {STACK_KB} 2>/dev/null || ulimit -s hard; exec "$@"'
r = subprocess.run(["/bin/sh", "-c", raised, "sh", LEANTAR, "-x", "-j", "-"], input=json.dumps(spec),
                   capture_output=True, text=True, env=dict(os.environ, RUST_MIN_STACK=str(STACK_KB * 1024)))
if r.returncode:
    print(f"::warning::leantar exited {r.returncode}; lake build will unpack what it left: {r.stderr.strip()[-300:]}")

subprocess.run(["/bin/sh", "-c", raised, "sh", "lake", "build", "--no-build"], capture_output=True)
PY
echo "now run: lake build"
