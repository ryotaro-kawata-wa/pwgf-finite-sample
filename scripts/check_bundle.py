#!/usr/bin/env python3
"""Verify distributed file hashes without executing any project code."""
import hashlib
import json
from pathlib import Path


def main():
    root = Path(__file__).resolve().parents[1]
    records = json.loads((root / "SHA256SUMS.json").read_text())["files"]
    for name, expected in records.items():
        relative = Path(name)
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError(f"Unsafe manifest path: {name}")
        path = root / relative
        if not path.is_file() or path.is_symlink() or not path.resolve().is_relative_to(root):
            raise ValueError(f"Missing or unsafe file: {name}")
        h = hashlib.sha256()
        with path.open("rb") as handle:
            for block in iter(lambda: handle.read(1024 * 1024), b""):
                h.update(block)
        if h.hexdigest() != expected:
            raise ValueError(f"Hash mismatch: {name}")
    print(f"Verified {len(records)} distributed files")


if __name__ == "__main__":
    main()
