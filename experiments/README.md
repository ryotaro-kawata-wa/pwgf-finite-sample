# Numerical reproduction

The unchanged finite-dimensional experiment code was rerun on 2026-10-06 using
Python 3.12.4, NumPy 1.26.4 and Matplotlib 3.8.4 in an isolated virtual environment.
All nine jobs completed: three seeds, each with the main grid, half integration
step, and half trigger-inspection interval. The runtime and dependency lock are
recorded in `verification/environment.json` and `requirements-lock.txt`.

## Recorded results and limits

`original/` is the verbatim original anonymous submission package. Its numerical
values and figures are still those displayed in the manuscript. Its nine large
state files were absent from the repository and have not been reconstructed.
Its own verifier confirms the preserved scalar files and figures only.

`results/` contains the new scalar trajectories, events, metadata, analysis and
regenerated figures. Raw states are distributed in nine separate archives;
`verification/raw-state-assets.json` records their hashes and contents. These
are fresh states, not recovered original states.

Download all nine state ZIPs and `raw-state-assets.json` from the
[2026-10-07 public release](https://github.com/ryotaro-kawata-wa/pwgf-finite-sample/releases/tag/v2026.10.07).
Please check each archive's SHA-256 against the manifest before extraction.
The archives are separate release assets and are not included in a Git clone.

The original 14 unit tests passed. An additional saved-state audit recomputed
294 arrays, 93 Hessians and 72 covariance comparisons. It also replayed 93 jumps
using the recorded random seeds. The objective, gradient and Hessian formulas
are checked independently of the implementation; RNG replay deliberately uses
the production coupling code and is labeled separately. The audit does not
reconstruct unrecorded states at every trigger-inspection time.

The integration-refinement check passed (maximum relative path change
2.54e-8). Exact agreement with the original platform is not claimed: 14 of the
15 main-grid conditions have the same stop and jump times. For seed 2 and
N=8192, the second jump is at 29.1 instead of 29.0, and stopping is at 39.1 instead
of 39.0. The largest absolute change in the returned objective-gap statistic is
3.84e-6. Full differences are in `verification/reproduction-comparison.json`.
The original Linux x86-64/MKL and new macOS arm64 backends differ; this is a
plausible source of numerical sensitivity, not a proven causal diagnosis.

`compare_reproduction.py --out verification/local-comparison.json` recomputes
the original-versus-fresh summary from the included reports. It records input
hashes and requires the complete fifteen-condition grid and nine-job audit.

These finite simulations illustrate the paper's model and diagnostics. They
do not prove the asymptotic rates or the assumptions of the Lean theorems.

## Reproduce in a new environment

From this directory, using Python 3.12.4 (other platforms may differ numerically):

```sh
python3.12 -m venv .venv
.venv/bin/python -m pip install -r requirements-lock.txt
.venv/bin/python -m unittest discover -s source -p 'test_*.py' -v
.venv/bin/python -m unittest discover -s report -p 'test_*.py' -v
.venv/bin/python -u source/run_adaptive_protocol.py --out runs --workers 3
.venv/bin/python audit_states.py --runs runs --out verification/local-state-audit.json
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 .venv/bin/python report/render_source.py --root . --out local-report
```

The nine jobs took about 18 minutes with three workers in the recorded run;
hardware and BLAS implementation affect runtime. Please allow several GiB for
raw states and use a new output directory for each run. The active renderer
exits unsuccessfully on a failed refinement check and rejects Python `-O`.

To audit the distributed states instead of rerunning, verify the archive hashes
and extract the nine state archives into this directory. They create `runs/`
with the matching scalar records and metadata. Then run `audit_states.py` and
the renderer as above, after restoring the shared protocol record:

```sh
cp results/runs/protocol_status.json runs/protocol_status.json
```

Existing output receipts are never overwritten by the
audit. The `results/` copy remains the recorded, unchanged reproduction.

MIT applies to project-authored code. The manuscript and third-party material
have separate licensing; see the publication license-scope document.
