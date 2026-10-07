# Finite-Sample Approximation of Hessian-Guided Perturbed Wasserstein Gradient Flows

Ryotaro Kawata · Atsushi Nitanda · Taiji Suzuki

Kawata: The University of Tokyo. Nitanda: Agency for Science,
Technology and Research (A*STAR); Nanyang Technological University. Suzuki:
The University of Tokyo; RIKEN Center for Advanced Intelligence
Project. Correspondence to Kawata: kawata-ryotaro725@g.ecc.u-tokyo.ac.jp.

This repository contains the paper sources, Lean formalization and numerical
reproducibility materials. Read the [complete paper PDF](paper/manuscript.pdf);
its source entry point is `paper/main_arxiv.tex`.
The public repository is
[ryotaro-kawata-wa/pwgf-finite-sample](https://github.com/ryotaro-kawata-wa/pwgf-finite-sample).
The [corrected source release](https://github.com/ryotaro-kawata-wa/pwgf-finite-sample/releases/tag/v2026.10.07.1)
provides the arXiv source ZIP and the verified repository bundle. It removes one
input of an empty placeholder that caused a missing-file error on arXiv; all
147 pages retain identical text and rendering. The unchanged nine numerical-state
archives and their hash manifest remain in the
[initial release](https://github.com/ryotaro-kawata-wa/pwgf-finite-sample/releases/tag/v2026.10.07).
The code is MIT licensed; the manuscript's distribution license is separate.
See `CODE_LICENSE_SCOPE.md`.

The [citation evidence report](verification/citations/index.html) contains the
individual existence checks for all 42 bibliography entries, with screenshots,
primary-source links and file hashes (41 distinct works; 37 cited entries).

## Paper

```sh
cd paper
latexmk -norc -pdf -no-shell-escape -recorder -interaction=nonstopmode -halt-on-error -outdir=build main_arxiv.tex
```

The paper is A4, one column, 11pt, with all appendices. The prepared PDF has
147 pages. Local compilation used TeX Live 2026. The arXiv source ZIP contains
the active sources, figures and generated `main_arxiv.bbl`; arXiv's own build
and preview remain a submission-time check.

## Lean

Install the toolchain pinned in `lean/lean-toolchain` using elan. Keep
`lean/lake-manifest.json` unchanged. From the repository root:

```sh
cd lean
lake exe cache get
cd ..
python3 lean/scripts/verify_release.py --checkpoint local-reproduction --manifest verification/lean-release-manifest.json --allow-archive --workers 2
```

The driver builds 661 modules, checks the types and axiom dependencies of all
4,274 registered declarations, and runs 57 boundary-diagnostic files. It rejects
missing, extra, duplicate or forbidden axiom records. Allowed foundational
axioms are `propext`, `Classical.choice` and `Quot.sound`.

The count includes definitions and instances; it is not a theorem count or a
claim that every auxiliary definition has its own audit query. The general
tracking theorem, variance-plus-cosine example and four MF local-geometry items
retain their explicit assumptions. The MF solution class is the specified
intrinsic AC characteristic class, with law uniqueness in that same class.
Curvature directions are continuous sphere-tangent fields with nonzero product
L2 norm, including smooth fields. Unconditional WGF existence and representation
of arbitrary weak PDE solutions are not proved.

`verification/manuscript-correspondence.json` records the separate source review
and exact old-to-new source mapping. The small `arxiv/` directory is a frozen
baseline used by the canonical source-hash guards; `paper/` is the current
publication manuscript. Please retain both when reproducing the formal audit.
Editing a checked input requires a new correspondence review and manifest,
rather than deleting or bypassing the hash check.

## Numerical experiments

See `experiments/README.md` for the isolated Python environment, all nine jobs,
independent saved-state audit and figure regeneration. `experiments/original/`
preserves the original reported scalar data and figures. `experiments/results/`
contains the fresh reproduction and explicit cross-platform differences.
Large fresh states are separate per-job assets listed in
`experiments/verification/raw-state-assets.json`.

The finite experiments are checked separately from Lean. They do not establish
the asymptotic theorem or its trajectory assumptions. Exact cross-platform
trajectory equality is not claimed; one of fifteen main-grid event schedules
differs by one 0.1-time-unit inspection step.

## Provenance

`verification/export-provenance.json` records the source commit and selected
inputs. `verification/lean-release-manifest.json` binds the reviewed manuscript
to the checked Lean inputs. Executed receipts are in `lean/verification/`.
`SHA256SUMS.json` covers the distributed regular files; use
`python3 scripts/check_bundle.py` to verify them before making edits.

This repository starts with the selected publication files and does not contain
the private development repository's Git history. Dependency caches and raw
state archives are excluded from Git; the states are separate release assets.
The corrected source has been compiled locally; arXiv server reprocessing is
not yet confirmed. No DOI or arXiv identifier is claimed; citation metadata will
be updated when an identifier is assigned.
