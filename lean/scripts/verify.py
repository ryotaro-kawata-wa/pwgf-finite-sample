#!/usr/bin/env python3
"""Build the verified library and audit its named claims; keep durable receipts."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def parse_axiom_output(output: str, targets: list[str]) -> dict[str, list[str]]:
    """Please reject duplicate records before constructing the dependency map.

    A later allowed record must never hide an earlier forbidden dependency.
    Both forms of Lean's output participate in the same uniqueness check.
    """
    records = [
        (match.start(), match.group(1),
         sorted(a.strip() for a in match.group(2).split(",") if a.strip()))
        for match in re.finditer(r"'([^']+)' depends on axioms:\s*\[(.*?)\]", output, re.S)
    ]
    records.extend(
        (match.start(), match.group(1), [])
        for match in re.finditer(r"'([^']+)' does not depend on any axioms", output)
    )
    dependencies: dict[str, list[str]] = {}
    for _, name, axioms in sorted(records):
        if name in dependencies:
            raise RuntimeError(f"Duplicate axiom audit record: {name}")
        dependencies[name] = axioms
    if set(dependencies) != set(targets):
        missing = sorted(set(targets) - set(dependencies))
        extra = sorted(set(dependencies) - set(targets))
        raise RuntimeError(f"Axiom output coverage mismatch; missing={missing}, extra={extra}")
    unexpected = {
        name: sorted(set(axioms) - ALLOWED_AXIOMS)
        for name, axioms in dependencies.items() if set(axioms) - ALLOWED_AXIOMS
    }
    if unexpected:
        raise RuntimeError(f"Unapproved axiom dependencies: {unexpected}")
    return dependencies


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path: Path, value: dict) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")
    temporary.replace(path)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checkpoint", required=True)
    parser.add_argument("--allow-archive", action="store_true",
                        help="Allow a source archive without its own Git HEAD; record input hashes instead")
    args = parser.parse_args()
    if not re.fullmatch(r"[a-z0-9][a-z0-9_-]{0,63}", args.checkpoint):
        parser.error("checkpoint must use 1-64 lowercase letters, digits, underscores or hyphens")
    lake_candidate = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    lake = Path(lake_candidate).absolute()
    if not lake.is_file() or not os.access(lake, os.X_OK):
        raise RuntimeError("Lake not found; install the pinned toolchain using elan")
    targets = json.loads((ROOT / "verification_targets.json").read_text())["declarations"]
    if not targets or len(targets) != len(set(targets)) or any(
        not isinstance(name, str) or not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*(\.[A-Za-z][A-Za-z0-9_]*)+", name)
        for name in targets
    ):
        raise RuntimeError("Invalid or empty verification target list")
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    out = ROOT / "verification" / f"{stamp}_{args.checkpoint}"
    out.mkdir(parents=True, exist_ok=False)
    env = os.environ.copy()
    env["PATH"] = str(lake.parent) + os.pathsep + env.get("PATH", "")
    receipt = {
        "checkpoint": args.checkpoint,
        "started_utc": stamp,
        "status": "running",
        "verification_directory": str(out.relative_to(ROOT)),
        "declarations": targets,
        "allowed_foundational_axioms": sorted(ALLOWED_AXIOMS),
        "commands": [],
        "scope": "Build and axiom audit of the listed Lean declarations under their explicit hypotheses. Manuscript correspondence and exclusions are documented in the claim-specific source reviews; this receipt alone does not certify the entire manuscript.",
    }

    def save() -> None:
        write_json(out / "receipt.json", receipt)
        write_json(ROOT / "verification/latest.json", receipt)

    def run(arguments: list[str], filename: str) -> str:
        command = [str(lake), *arguments]
        record = {"arguments": ["lake", *arguments], "output": filename, "status": "running"}
        receipt["commands"].append(record)
        save()
        print("Running:", " ".join(record["arguments"]), flush=True)
        with (out / filename).open("w") as log:
            result = subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
        record.update(returncode=result.returncode, status="passed" if result.returncode == 0 else "failed")
        save()
        output = (out / filename).read_text()
        if result.returncode:
            print(output, file=sys.stderr)
            raise RuntimeError(f"Command failed ({result.returncode}); see {out / filename}")
        return output

    save()
    try:
        snapshot = json.loads((ROOT / "source_snapshot.json").read_text())
        for entry in [snapshot, *snapshot.get("supporting_sources", [])]:
            relative_source = Path(entry["source_path"])
            if relative_source.is_absolute() or ".." in relative_source.parts:
                raise RuntimeError("Source snapshot path must stay within the repository")
            source = ROOT.parent / relative_source
            if digest(source) != entry["sha256"]:
                raise RuntimeError(
                    f"Manuscript source changed: {relative_source}; review the correspondence first")
        receipt["source_snapshot"] = snapshot
        git_root = subprocess.run(["git", "rev-parse", "--show-toplevel"],
                                  cwd=ROOT, text=True, capture_output=True)
        own_checkout = (git_root.returncode == 0 and
                        Path(git_root.stdout.strip()).resolve() == ROOT.parent.resolve())
        if own_checkout:
            receipt["git_head_at_verification"] = subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
            receipt["source_identity_kind"] = "git-checkout-with-input-hashes"
        elif args.allow_archive:
            receipt["git_head_at_verification"] = None
            receipt["source_identity_kind"] = "source-archive-with-input-hashes"
        else:
            raise RuntimeError("An independent Git checkout is required; use --allow-archive for an extracted source bundle")
        receipt["toolchain"] = (ROOT / "lean-toolchain").read_text().strip()
        pinned = json.loads((ROOT / "lake-manifest.json").read_text())
        receipt["dependency_revisions"] = {
            package["name"]: package.get("rev") for package in pinned["packages"]
        }
        receipt["input_sha256"] = {
            str(path.relative_to(ROOT)): digest(path)
            for path in sorted([
                ROOT / "lean-toolchain", ROOT / "lakefile.toml", ROOT / "lake-manifest.json",
                ROOT / "PaperFormalization.lean", ROOT / "verification_targets.json",
                ROOT / "scripts/verify.py", ROOT / "source_snapshot.json", *ROOT.glob("PaperFormalization/**/*.lean"),
            ])
        }
        version_output = run(["env", "lean", "--version"], "toolchain.txt")
        actual_version = re.search(r"\bversion\s+([^,\s)]+)", version_output)
        expected_version = receipt["toolchain"].rsplit(":", 1)[-1].removeprefix("v")
        if actual_version is None or actual_version.group(1) != expected_version:
            raise RuntimeError(f"Lean version does not match the pinned toolchain: {version_output.strip()}")
        run(["build", "PaperFormalization"], "build.txt")
        actual_dependencies = {}
        for package in pinned["packages"]:
            name = package["name"]
            actual = subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=ROOT / ".lake/packages" / name,
                text=True).strip()
            if actual != package.get("rev"):
                raise RuntimeError(f"Dependency revision mismatch: {name}")
            actual_dependencies[name] = actual
        receipt["actual_dependency_revisions"] = actual_dependencies
        audit = out / "AxiomAudit.lean"
        audit.write_text("import PaperFormalization\n\n" + "\n".join(
            f"#check {name}\n#print axioms {name}" for name in targets) + "\n")
        output = run(["env", "lean", str(audit.relative_to(ROOT))], "axioms.txt")
        receipt["axiom_dependencies"] = parse_axiom_output(output, targets)
        after = {name: digest(ROOT / name) for name in receipt["input_sha256"]}
        if after != receipt["input_sha256"]:
            raise RuntimeError("Proof or verification inputs changed during the run")
        for entry in [snapshot, *snapshot.get("supporting_sources", [])]:
            if digest(ROOT.parent / entry["source_path"]) != entry["sha256"]:
                raise RuntimeError("Manuscript snapshot changed during the run")
        receipt["inputs_unchanged_after_verification"] = True
        receipt["status"] = "passed"
        print(f"Verified {len(targets)} declarations; receipt: {out / 'receipt.json'}", flush=True)
        return 0
    except BaseException as error:
        receipt["status"] = "failed" if isinstance(error, Exception) else "interrupted"
        receipt["error"] = str(error)
        raise
    finally:
        save()


if __name__ == "__main__":
    sys.exit(main())
