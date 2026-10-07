"""Export only manifest-listed files to a zip with no Git or host metadata."""

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import tempfile
import zipfile

from verify import ROOT, check_anonymity, digest, load_denials, safe_file, verify


def entry(name):
    info = zipfile.ZipInfo("matrix-sanity/" + name, date_time=(1980, 1, 1, 0, 0, 0))
    info.create_system = 3
    info.external_attr = 0o100644 << 16
    info.compress_type = zipfile.ZIP_DEFLATED
    return info


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True, help="directory for a new archive")
    parser.add_argument("--states-root", type=Path, help="optional root containing original runs/*/trial_*/states.npz")
    parser.add_argument("--deny", action="append", default=[])
    parser.add_argument("--deny-file", type=Path, help="private token file outside the distribution")
    args = parser.parse_args()
    denials = load_denials(args.deny, args.deny_file)
    verify(deny=denials)
    manifest = json.loads((ROOT / "MANIFEST.json").read_text(encoding="utf-8"))
    files = {name: safe_file(ROOT, name) for name in manifest["files"]}
    if args.states_root is not None:
        expected = json.loads((ROOT / "PROVENANCE.json").read_text(encoding="utf-8"))["states"]["sha256"]
        for name, sha in expected.items():
            path = safe_file(args.states_root.resolve(), name)
            if digest(path) != sha:
                raise ValueError("state hash mismatch: " + name)
            check_anonymity(path, denials)
            files[name] = path
            manifest["files"][name] = {"sha256": sha, "bytes": path.stat().st_size}
    args.out.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(prefix=".building-", suffix=".zip", dir=args.out, delete=False) as temp:
        pending = Path(temp.name)
    try:
        with zipfile.ZipFile(pending, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=6) as archive:
            for name in sorted(files):
                # Stream large optional snapshots without loading them into memory.
                with files[name].open("rb") as source, archive.open(entry(name), "w", force_zip64=True) as target:
                    for block in iter(lambda: source.read(1024 * 1024), b""):
                        target.write(block)
            archive.writestr(entry("MANIFEST.json"), json.dumps(manifest, indent=2, sort_keys=True) + "\n")
        sha = digest(pending)
        stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        mode = "full" if args.states_root else "light"
        final = args.out / f"matrix-sanity_{mode}_{stamp}_{sha[:12]}.zip"
        # Exclusive creation: never replace a previous archive.
        with final.open("xb") as target, pending.open("rb") as source:
            for block in iter(lambda: source.read(1024 * 1024), b""):
                target.write(block)
        print(json.dumps({"archive": str(final), "sha256": sha,
                          "bytes": final.stat().st_size, "mode": mode}, indent=2))
    finally:
        pending.unlink(missing_ok=True)


if __name__ == "__main__":
    main()
