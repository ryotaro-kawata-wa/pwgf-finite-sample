"""Verify the manifest, original-figure provenance, and anonymous text metadata."""

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import unicodedata


ROOT = Path(__file__).resolve().parents[1]
CJK = re.compile(r"[\u2e80-\u303f\u3040-\u30ff\u31f0-\u31ff\u3400-\u4dbf"
                 r"\u4e00-\u9fff\uf900-\ufaff\uff66-\uff9f\U00020000-\U000323af]")


def load_denials(tokens=(), deny_file=None):
    """Private deny lists stay outside the distribution and are never exported."""
    private = ROOT.parent / ".submission-private" / "deny.txt"
    paths = [private] if private.is_file() else []
    if deny_file is not None:
        paths.append(Path(deny_file))
    result = list(tokens)
    for path in paths:
        if path.resolve().is_relative_to(ROOT):
            raise ValueError("a private deny list must be outside the package")
        result.extend(path.read_text(encoding="utf-8").splitlines())
    return tuple(dict.fromkeys(unicodedata.normalize("NFKC", t.strip()).casefold()
                               for t in result if t.strip()))


def check_text(text, deny=()):
    normalized = unicodedata.normalize("NFKC", text).casefold()
    if CJK.search(normalized):
        raise ValueError("non-English CJK text found in distribution")
    if any(token in normalized for token in deny):
        # Do not echo a matched private token or a potentially identifying path.
        raise ValueError("private token found in distribution")


def digest(path):
    result = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            result.update(block)
    return result.hexdigest()


def safe_file(root, name):
    relative = PurePosixPath(name)
    if relative.is_absolute() or ".." in relative.parts or "\\" in name:
        raise ValueError("unsafe manifest path")
    path = root.joinpath(*relative.parts)
    if path.is_symlink() or not path.is_file() or not path.resolve().is_relative_to(root.resolve()):
        raise ValueError("missing, symlinked, or external file: " + name)
    for parent in path.parents:
        if parent == root:
            break
        if parent.is_symlink():
            raise ValueError("symlinked parent: " + name)
    return path


def check_anonymity(path, deny=()):
    check_text(path.name, deny)
    # Stream optional large numeric snapshots; do not load them into memory.
    if path.suffix.lower() == ".npz":
        needles = [token.encode("utf-8").lower() for token in deny if token]
        if needles:
            overlap = max(map(len, needles)) - 1
            tail = b""
            with path.open("rb") as handle:
                for block in iter(lambda: handle.read(1024 * 1024), b""):
                    data = tail + block.lower()
                    if any(token in data for token in needles):
                        raise ValueError("private token found in distribution")
                    tail = data[-overlap:] if overlap else b""
        return
    data = path.read_bytes()
    for token in deny:
        if token and token.encode("utf-8").lower() in data.lower():
            raise ValueError("private token found in distribution")
    if path.suffix.lower() in {".py", ".md", ".json", ".csv", ".txt"}:
        text = data.decode("utf-8")
        check_text(text, deny)
        if path.suffix.lower() == ".json":
            # Decode JSON Unicode escapes before checking private tokens and CJK.
            check_text(json.dumps(json.loads(text), ensure_ascii=False), deny)
        # Construct patterns without putting a literal home path in this source.
        home_pattern = r"/" + r"(?:Users|home)/[^\s/\"']+"
        email_pattern = r"[\w.+-]+" + "@" + r"[\w-]+(?:\.[\w-]+)+"
        host_pattern = r'"host' + r'name"\s*:\s*"[^\"]+"'
        if any(re.search(pattern, text) for pattern in (home_pattern, email_pattern, host_pattern)):
            raise ValueError("possible private text metadata in " + path.name)


def verify(root=ROOT, deny=()):
    deny = load_denials(deny)
    root = root.resolve()
    manifest = json.loads((root / "MANIFEST.json").read_text(encoding="utf-8"))
    if manifest["schema"] != 1 or not isinstance(manifest["files"], dict):
        raise ValueError("unsupported manifest")
    for name, item in manifest["files"].items():
        check_text(name, deny)
        path = safe_file(root, name)
        if path.stat().st_size != item["bytes"] or digest(path) != item["sha256"]:
            raise ValueError("file integrity mismatch: " + name)
        check_anonymity(path, deny)
    check_anonymity(root / "MANIFEST.json", deny)
    original = json.loads((root / "report/figure_manifest.json").read_text(encoding="utf-8"))
    provenance = json.loads((root / "PROVENANCE.json").read_text(encoding="utf-8"))
    if set(provenance.get("excluded_from_submission", [])) & manifest["files"].keys():
        raise ValueError("local-only documentation must not be distributed")
    if digest(root / "report/figure_manifest.json") != provenance["original_figure_manifest_sha256"]:
        raise ValueError("original figure manifest changed")
    changed = {r["path"]: r for r in provenance["anonymization"]}
    omitted = provenance.get("omitted_original_files", {})
    states_missing = 0
    for name, original_sha in original["inputs"].items():
        if name in omitted:
            if omitted[name]["sha256"] != original_sha:
                raise ValueError("omitted-file provenance mismatch")
            continue
        if name in changed:
            entry = changed[name]
            expected = entry["packaged_sha256"]
            if original_sha != entry["original_sha256"]:
                raise ValueError("anonymization provenance mismatch: " + name)
        else:
            expected = original_sha
        path = root / name
        if not path.exists() and name in provenance["states"]["sha256"]:
            states_missing += 1
            continue
        if digest(safe_file(root, name)) != expected:
            raise ValueError("original-input provenance mismatch: " + name)
    for name, key in [("analysis.json", "analysis_sha256"),
                      ("render_source.py", "render_source_sha256"),
                      ("summary.csv", "summary_csv_sha256")]:
        derivative = changed.get("report/" + name)
        expected = original[key]
        if derivative is not None:
            if derivative["original_sha256"] != expected:
                raise ValueError("report derivative provenance mismatch")
            expected = derivative["packaged_sha256"]
        if digest(root / "report" / name) != expected:
            raise ValueError("original report changed: " + name)
    for item in original["figures"]:
        path = safe_file(root / "report", item["path"])
        if digest(path) != item["sha256"] or not path.stem.endswith(item["sha256"][:12]):
            raise ValueError("figure hash or filename mismatch")
    return {"verified_files": len(manifest["files"]),
            "verified_original_figures": len(original["figures"]),
            "optional_state_files_missing": states_missing,
            "anonymity_check": "CJK, text metadata, and configured private tokens checked"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--deny", action="append", default=[], help="additional private token to reject")
    parser.add_argument("--deny-file", type=Path, help="private token file outside the distribution")
    args = parser.parse_args()
    print(json.dumps(verify(args.root, load_denials(args.deny, args.deny_file)), indent=2))


if __name__ == "__main__":
    main()
