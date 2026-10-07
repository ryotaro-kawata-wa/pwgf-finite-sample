# Lean reproduction entry point

Please follow the root README. Use `scripts/verify_release.py` with the root
`verification/lean-release-manifest.json` to run the full release audit.
`scripts/verify.py` alone is the canonical build and 4,274-declaration axiom audit;
it does not execute the separate 57 diagnostic files.

The pinned toolchain is Lean 4.32.1 and the pinned mathlib commit is
`520045ab14e26149ee970e2e617ca04b09bde5d6`. Dependencies retain their own licenses.
Project code in this directory is MIT licensed.

The formalization contains 661 modules. The aggregate theorem endpoints include
`source_mf_local_geometry`, `varianceCosine_printed_proposition`, and the general
source tracking/objective applications. See
`../verification/manuscript-correspondence.json` for the exact names, hypotheses,
paper labels and exclusions. Kernel checking and manual manuscript review are
separate claims.

No earlier integration driver or stale checkpoint instructions are needed to
reproduce this release. New runs write new receipt directories and update
`verification/latest.json`; previously recorded receipts remain unchanged.
