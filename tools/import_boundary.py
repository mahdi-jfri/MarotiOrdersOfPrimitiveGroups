#!/usr/bin/env python3
"""Fail if the `Maroti` library imports, directly or transitively, a module of AxiomMath/CFSG that
proves the classification of finite simple groups.

Adapted from AxiomMath/CFSGCorollary, Checks/ImportBoundary.lean, Apache-2.0. The import graph is
read from the source headers, which list the same imports as the `.olean` files. Every kind of
import is followed (`public`, private, `meta`, `all`), so the check also covers modules that a
Lean process importing `Maroti` would not load.
"""
import re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PKGS = ROOT / '.lake' / 'packages'
SEARCH = [ROOT] + sorted(p for p in PKGS.iterdir() if p.is_dir())
FORBIDDEN = [
    'CFSG.Certified.Classification', 'CFSG.Statement', 'CFSG.Assembly.Catalog',
    'CFSG.Assembly.Disconnected', 'CFSG.Assembly.LowTwoRank', 'CFSG.Assembly.Dichotomy',
    'CFSG.Assembly.ComponentType', 'CFSG.Assembly.Quasithin', 'CFSG.Assembly.RankThreeEven',
    'CFSG.Assembly.LargeEven',
]
IMPORT = re.compile(r'^[ \t]*(?:(?:public|meta|private)[ \t]+)*import[ \t]+(?:all[ \t]+)?([\w.«»\']+)', re.M)

def source(mod):
    rel = Path(*mod.split('.')).with_suffix('.lean')
    for d in SEARCH:
        if (d / rel).exists():
            return d / rel
    return None

def header(text):
    # The imports come before the first declaration; stop at the first line that is not part of
    # the header (comments, `module`, `prelude` and imports).
    end = re.search(r'^(?!\s*$|\s*--|\s*/-|\s*-/|\s*(?:(?:public|meta|private)\s+)*import\b|module\b|prelude\b)', text, re.M)
    return text[:end.start()] if end else text

seen, todo, missing = set(), ['Maroti'], []
while todo:
    m = todo.pop()
    if m in seen:
        continue
    seen.add(m)
    f = source(m)
    if f is None:
        if not m.startswith(('Init', 'Std', 'Lean', 'Lake')):
            missing.append(m)
        continue
    todo += [d for d in IMPORT.findall(header(f.read_text(errors='ignore'))) if d not in seen]

bad = [m for m in FORBIDDEN if m in seen]
if bad:
    sys.exit(f'IMPORT BOUNDARY FAILED: the Maroti library imports {bad}, part of the proof of the classification')
if missing:
    sys.exit(f'IMPORT BOUNDARY FAILED: no source found for {missing[:10]}')
print(f'import boundary: {len(seen)} modules reachable from Maroti, none of them proves the classification')
