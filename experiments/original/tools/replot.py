"""Redraw archived figures from scalar records and the archived analysis."""

import argparse
import importlib.util
import json
from pathlib import Path

from verify import ROOT, digest, verify


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True, help="new, nonexistent output directory")
    args = parser.parse_args()
    verify()
    renderer = ROOT / "report/render_source.py"
    spec = importlib.util.spec_from_file_location("archived_renderer", renderer)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    analysis_path = ROOT / "report/analysis.json"
    analysis = json.loads(analysis_path.read_text(encoding="utf-8"))
    runs = {("main", trial): module.load_run(ROOT / "runs/main" / f"trial_{trial:03d}")
            for trial in analysis["trials"]}
    args.out.mkdir(parents=True, exist_ok=False)
    records = module.figures(analysis, runs, args.out, digest(analysis_path))
    manifest = {"mode": "redraw from archived scalar data; no state audits recomputed",
                "analysis_sha256": digest(analysis_path),
                "render_source_sha256": digest(renderer), "figures": records}
    (args.out / "figure_manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"figures_written": len(records), "mode": manifest["mode"]}))


if __name__ == "__main__":
    main()
