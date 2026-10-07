#!/usr/bin/env python3
"""Verify registered claims, boundary files and the exact release manuscript."""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

from verify import parse_axiom_output


LEAN = Path(__file__).resolve().parents[1]
ROOT = LEAN.parent


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def checked_manifest(path: Path) -> dict:
    data = json.loads(path.read_text())
    if not isinstance(data.get("files"), dict) or not data["files"]:
        raise RuntimeError("The release manifest must enumerate its checked inputs")
    for name, expected in data["files"].items():
        relative = Path(name)
        if relative.is_absolute() or ".." in relative.parts:
            raise RuntimeError(f"Invalid manifest path: {name}")
        source = ROOT / relative
        if not source.resolve().is_relative_to(ROOT.resolve()):
            raise RuntimeError(f"Manifest input escapes the release tree: {name}")
        if sha256(source) != expected:
            raise RuntimeError(f"Release input does not match its reviewed hash: {name}")
    return data


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checkpoint", required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--workers", type=int, choices=(1, 2, 3, 4), default=2)
    parser.add_argument("--allow-archive", action="store_true")
    args = parser.parse_args()
    if not re.fullmatch(r"[a-z0-9][a-z0-9_-]{0,63}", args.checkpoint):
        parser.error("Please use a short lowercase checkpoint name")
    manifest_path = args.manifest.resolve()
    manifest_hash = sha256(manifest_path)
    manifest = checked_manifest(manifest_path)
    required = {
        str(p.relative_to(ROOT)) for p in LEAN.glob("PaperFormalization/**/*.lean")
    } | {
        "lean/PaperFormalization.lean", "lean/lean-toolchain", "lean/lakefile.toml",
        "lean/lake-manifest.json", "lean/verification_targets.json",
        "lean/source_snapshot.json", "lean/scripts/verify.py",
        "lean/scripts/verify_release.py", "lean/scripts/test_verify.py",
    }
    checks = sorted((LEAN / "checks").glob("*.lean"))
    required |= {str(p.relative_to(ROOT)) for p in checks}
    if not checks or not required <= set(manifest["files"]):
        raise RuntimeError("The release manifest omits a proof, verifier or diagnostic input")
    review = manifest.get("manuscript_review", {})
    if (not isinstance(review, dict) or not review.get("path")
            or manifest["files"].get(review["path"]) != review.get("sha256")):
        raise RuntimeError("The manuscript review must be an enumerated, hash-checked release input")
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    out = LEAN / "verification" / f"{stamp}_{args.checkpoint}-release"
    out.mkdir(parents=True, exist_ok=False)
    started = time.monotonic()
    receipt = {
        "status": "running", "started_utc": stamp,
        "release_manifest_sha256": manifest_hash,
        "input_sha256": manifest["files"],
        "manuscript_review": manifest["manuscript_review"],
        "commands": [], "diagnostics": [],
        "scope": "Registered Lean declarations and all included boundary files; manual manuscript correspondence is a separate review. Numerical reproduction is not certified by this receipt.",
    }

    def save() -> None:
        (out / "release-receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")

    def execute(command: list[str], log: Path) -> dict:
        tick = time.monotonic()
        with log.open("w") as handle:
            result = subprocess.run(command, cwd=LEAN, stdout=handle, stderr=subprocess.STDOUT)
        return {"command": command, "returncode": result.returncode,
                "seconds": time.monotonic() - tick, "log": log.name}

    save()
    try:
        test = execute([sys.executable, "-m", "unittest", "discover", "-s", "scripts",
                        "-p", "test_verify.py", "-v"], out / "parser-tests.txt")
        receipt["commands"].append(test)
        if test["returncode"]:
            raise RuntimeError("Axiom parser regression tests failed")
        command = [sys.executable, "scripts/verify.py", "--checkpoint", args.checkpoint]
        if args.allow_archive:
            command.append("--allow-archive")
        print("Running aggregate verification", flush=True)
        aggregate = execute(command, out / "aggregate.txt")
        receipt["commands"].append(aggregate)
        if aggregate["returncode"]:
            raise RuntimeError("Aggregate verification failed; please inspect aggregate.txt")
        canonical = json.loads((LEAN / "verification/latest.json").read_text())
        if canonical["status"] != "passed" or canonical["checkpoint"] != args.checkpoint:
            raise RuntimeError("Unexpected canonical receipt")
        canonical_dir = LEAN / canonical["verification_directory"]
        parse_axiom_output((canonical_dir / "axioms.txt").read_text(), canonical["declarations"])
        receipt["canonical_receipt"] = str((canonical_dir / "receipt.json").relative_to(LEAN))
        receipt["registered_declarations"] = len(canonical["declarations"])
        receipt["modules"] = len(list(LEAN.glob("PaperFormalization/**/*.lean")))
        lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
        print(f"Running {len(checks)} diagnostic files", flush=True)
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            jobs = {
                pool.submit(execute, [lake, "env", "lean", str(path.relative_to(LEAN))],
                            out / (path.stem + ".txt")): path
                for path in checks
            }
            for future in as_completed(jobs):
                record = future.result()
                record["source"] = str(jobs[future].relative_to(ROOT))
                receipt["diagnostics"].append(record)
                save()
                print(f"Checked {len(receipt['diagnostics'])}/{len(checks)}: {jobs[future].name}", flush=True)
        failed = [r["source"] for r in receipt["diagnostics"] if r["returncode"]]
        if failed:
            raise RuntimeError(f"Boundary diagnostics failed: {failed}")
        if sha256(manifest_path) != manifest_hash or checked_manifest(manifest_path) != manifest:
            raise RuntimeError("Release inputs changed while verification was running")
        receipt["inputs_unchanged_after_verification"] = True
        receipt["diagnostics"].sort(key=lambda r: r["source"])
        receipt["status"] = "passed"
        print(f"Release verification passed: {out / 'release-receipt.json'}", flush=True)
        return 0
    except BaseException as error:
        receipt["status"] = "failed" if isinstance(error, Exception) else "interrupted"
        receipt["error"] = str(error)
        raise
    finally:
        receipt["elapsed_seconds"] = time.monotonic() - started
        save()


if __name__ == "__main__":
    raise SystemExit(main())
