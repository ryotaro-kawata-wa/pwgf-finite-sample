"""Three fixed seeds, three resolutions, at most three single-thread workers."""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

from adaptive import Config, write_json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--workers", type=int, choices=(1, 2, 3), default=3)
    args = parser.parse_args()
    source = Path(__file__).resolve().parent
    base = json.loads((source / "adaptive_config.json").read_text())
    variants = {"main": base,
        "integration_half": {**base, "dt": base["dt"] / 2},
        "trigger_half": {**base, "dt": base["dt"] / 2,
                         "check_interval": base["check_interval"] / 2}}
    for values in variants.values():
        Config(**values)
    args.out.mkdir(parents=True, exist_ok=False)
    root = args.out.resolve()
    for variant, values in variants.items():
        write_json(root / (variant + "_config.json"), values)
    status = {"status": "running", "trials": [0, 1, 2], "workers": args.workers,
        "variants": variants, "completed": [], "failed": [],
        "source_sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in sorted(source.iterdir()) if p.is_file()}}
    status_path = root / "protocol_status.json"
    write_json(status_path, status)
    env = {**os.environ, "OPENBLAS_NUM_THREADS": "1", "OMP_NUM_THREADS": "1", "MKL_NUM_THREADS": "1"}

    def job(trial, variant):
        started = time.monotonic()
        folder = root / variant
        folder.mkdir(exist_ok=True)
        command = [sys.executable, "-u", str(source / "adaptive.py"), "--config",
            str(root / (variant + "_config.json")), "--trial", str(trial),
            "--out", str(folder / f"trial_{trial:03d}")]
        print(json.dumps({"event": "start", "trial": trial, "variant": variant}), flush=True)
        with (folder / f"trial_{trial:03d}.log").open("x") as log:
            subprocess.run(command, cwd=source, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
        return {"trial": trial, "variant": variant, "seconds": time.monotonic() - started}

    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        pending = {pool.submit(job, trial, variant): (trial, variant)
                   for variant in variants for trial in status["trials"]}
        for future in as_completed(pending):
            trial, variant = pending[future]
            try:
                result = future.result()
                status["completed"].append(result)
                print(json.dumps({"event": "complete", **result}), flush=True)
            except Exception as error:
                failure = {"trial": trial, "variant": variant, "error": repr(error)}
                status["failed"].append(failure)
                print(json.dumps({"event": "failed", **failure}), flush=True)
            write_json(status_path, status)
    status["status"] = "failed" if status["failed"] else "complete"
    write_json(status_path, status)
    if status["failed"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
