# Code adapted from other projects

One line per file: our file, the source repository and path, and its license.

- `tools/lake-cache-get-fast.sh`: AxiomMath/CFSG's cache download script
  (https://cfsg-downloads.axiommath.workers.dev/lake/), itself adapted from TauCeti's tools.
  Apache-2.0. Changed so that missing or corrupt artifacts are fetched again before giving up.
- `Checks/ImportBoundary.lean`: AxiomMath/CFSGCorollary, `Checks/ImportBoundary.lean`, Apache-2.0.
  Adapted for the `Maroti` library and `Maroti.theorem_1_1_of_families`.
