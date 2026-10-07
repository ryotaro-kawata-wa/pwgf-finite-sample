# Matrix-factorization sanity check: anonymous reproduction package

This package contains execution and reproduction instructions, numerical source, archived scalar results, and figures. Manuscript and protocol notes are maintained locally and excluded from the submission archive. [HANDOFF.md](HANDOFF.md) records interpretation limits. The original run identifier is `20260925T120936Z_adaptive_K32768`.

## Contents and integrity

- `source/`: frozen numerical code, tests, and adaptive configuration. Edits remove host-name collection from output metadata and the runtime hash dependency on excluded protocol notes; model, coupling, seeds, controller, and integration are unchanged.
- `runs/`: all nine jobs' scalar trajectories, event logs, summaries, configurations, and anonymized metadata.
- `report/analysis.json`, `summary.csv`: archived numerical analysis and the 15 main conditions.
- `report/render_source.py`: the final renderer with its report-generation function translated to English and its paper-citation sentence removed. Numerical analysis, audits, and figure-generation functions are unchanged. The full analysis command writes `REPORT.md` and `adaptive_report.html`.
- `report/figures/`: the original five PDFs and five PNGs, unchanged.
- `report/figure_manifest.json`: original figure/input hashes, unchanged.
- `PROVENANCE.json`: original-to-anonymized hash mapping and hashes of optional state files.
- `ORIGINAL_ENVIRONMENT.json`: original Python/NumPy/Matplotlib versions, MKL backend, and 22 observed scientific-package builds, including package hashes. This is a selected dependency record, not a complete environment lock.
- `VERIFICATION.json`: the checks performed on the distribution, including their scope and limitations.
- `MANIFEST.json`: full SHA-256 and size of each file in this distribution, excluding itself.

From this package's root, run the standard-library-only integrity check:

```sh
python tools/verify.py
python tools/check_results.py
```

The original figure manifest and `source_sha256` fields in recorded metadata refer to the **original execution inputs**. Twelve files have anonymized/documentation derivatives, recorded in `PROVENANCE.json`; the obsolete plotting snapshot and protocol notes are omitted. The renderer's only changed function generates the English report. `MANIFEST.json` refers to the files actually shipped here. Do not compare an anonymized file directly against its original hash and conclude that the numerical data changed. No scalar result, event, original figure, or archived analysis has been altered. `.gitattributes` disables automatic line-ending conversion so that the original CSV bytes and all authenticated hashes survive Git checkout on another platform.

## Environment

The original run used Python **3.12.4**, NumPy **1.26.4** with **MKL 2023.1**, Matplotlib **3.8.4**, Linux x86-64, and one BLAS/OpenMP thread per worker. For portable execution and plotting, create an isolated environment with Python 3.12.4 and install the pinned Python packages:

```sh
python -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
export OPENBLAS_NUM_THREADS=1
export OMP_NUM_THREADS=1
export MKL_NUM_THREADS=1
python -m unittest discover -s source -p 'test_*.py'
```

No external dataset, model download, GPU, or credentials are needed. These pip requirements do **not** recreate the original MKL-backed Conda build. For a closer numerical reproduction on Linux x86-64, use the observed exact build identifiers and official channels in `ORIGINAL_ENVIRONMENT.json`. We have not tested constructing a new environment from that selected record. Python-package pins alone do not pin BLAS/LAPACK binaries or hardware. Near-zero eigenspaces and SVD null-space completions can change across platforms, so seeds do not guarantee bitwise trajectory reproduction across environments. Compare the event schedules and the individual-trial diagnostics, not only a summary average. Do not silently discard or replace a discrepant trial.

## Redraw the recorded figures (no simulation rerun)

```sh
python tools/replot.py --out replot-output
```

The output directory must not already exist. This calls the original plotting functions on the archived scalar records and analysis. It writes all five PDFs and five PNGs with new timestamp/hash names and a new figure manifest. It **does not** recompute state-based audits or return-state alignment diagnostics. Those conclusions remain archived analysis until the state audits are rerun.

Original filenames use `YYYYMMDD-HHMMSSJST_<first 12 SHA256 hex digits>`. Full hashes are in `report/figure_manifest.json`; PDF metadata and PNG text metadata contain the source `analysis.json` hash. Newly generated timestamps and PDF metadata imply new file hashes even if the plotted values are unchanged. Use original hashes for file integrity, and archived data plus renderer for plot reproduction.

## Full numerical rerun

The following starts all three trials at all three resolutions. It creates a fresh source snapshot and `rerun/runs` directory, and then repeats the numerical audits and analysis before making figures:

```sh
(
set -eu
mkdir rerun
cp -R source rerun/source
python rerun/source/run_adaptive_protocol.py --out rerun/runs --workers 3
python report/render_source.py --root rerun --out rerun/report
)
```

All output directories are exclusive and existing results are not overwritten. The original nine jobs each took approximately 6.6–17.5 minutes with up to three simultaneous CPU workers; runtime and memory requirements depend on the machine. `--workers 1` uses less concurrent memory. All original compressed state snapshots together occupy 2,547,767,593 bytes; a rerun also needs memory for particle arrays and temporary snapshots. New output hashes can differ because metadata, timing, library versions, or floating-point paths differ. The new renderer's run identifier is the new root directory's name.

## Optional original state snapshots

The lightweight package does not contain `runs/*/trial_*/states.npz`. Their full hashes are in `PROVENANCE.json` and the original figure manifest. A full rerun regenerates states, but does not promise the same compressed-file bytes. Without the original states or a rerun, one can verify and redraw the saved scalar data, but cannot independently recompute all saved-state checks.

To analyze a copy with all original, hash-verified states installed at the recorded relative paths:

```sh
python tools/verify.py
python report/render_source.py --root . --out original-state-reaudit
```

The `--out` directory must be new. The recorded figure bytes should still be preserved separately.

## Anonymous packaging

```sh
python tools/package.py --out dist
```

This creates a timestamped ZIP whose filename ends in 12 digits of its own SHA-256; the command also prints the full hash. It includes **only** manifest-listed files and `MANIFEST.json`, under a relative `matrix-sanity/` root. It does not package Git history, Git author information, SSH settings, local audit folders, generated reruns, or arbitrary neighboring files. ZIP entry timestamps and permissions are normalized and no user/group identity is written. Local manuscript and protocol notes are excluded, and the report generator contains no paper citation. Experimental dates, software version records, and RNG seeds are retained.

To include the nine original states, point `--states-root` at a directory containing their original `runs/.../states.npz` layout:

```sh
python tools/package.py --out dist --states-root /path/to/original-run
```

Each state must match its recorded original SHA-256. The full archive's manifest is expanded accordingly. This option deliberately does not relabel a numerically similar rerun as the original data.

The verifier rejects CJK text in distributed filenames and text files, including decoded JSON Unicode escapes. It also checks home-directory paths, email addresses, nonempty host-name metadata, and configured private strings, with Unicode normalization and case-insensitive matching. Additional private strings can be provided through repeated `--deny TOKEN` options or `--deny-file /path/to/private-deny-list.txt`. Both verification and packaging also automatically load an optional sibling `.submission-private/deny.txt` file. Private deny lists must stay outside this package and are never included by the manifest-based exporter. The local working repository ignores that private directory.

These checks are practical checks, not a guarantee of anonymity under every inference or a substitute for checking the venue's submission rules. The original figures contain generic software metadata and no author field. Do not upload the parent working repository or an older ZIP; export a fresh ZIP after verification.

If you edit packaged instructions or tooling, deliberately update `MANIFEST.json` to the new file hashes before exporting; packaging fails on stale hashes. Keep local-only documents listed in `PROVENANCE.json` outside the manifest; verification rejects their accidental inclusion. Keep the original figure manifest and the original numerical artifacts unchanged. The local commit stores this distribution for review, while the exported ZIP carries no commit identity.
