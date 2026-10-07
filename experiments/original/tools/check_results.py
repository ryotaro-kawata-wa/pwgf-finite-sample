"""Cross-check reported scalar diagnostics against archived CSV/JSON records."""

import csv
import json
import math

from verify import ROOT


def close(actual, expected, label):
    if not math.isclose(actual, expected, rel_tol=1e-12, abs_tol=1e-14):
        raise ValueError("numerical mismatch: " + label)


def main():
    analysis = json.loads((ROOT / "report/analysis.json").read_text(encoding="utf-8"))
    if len(analysis["conditions"]) != 15:
        raise ValueError("expected all 15 conditions")
    for condition in analysis["conditions"]:
        trial, n = condition["trial"], condition["n"]
        folder = ROOT / "runs/main" / f"trial_{trial:03d}"
        with (folder / "trajectory.csv").open(newline="", encoding="utf-8") as handle:
            rows = [r for r in csv.DictReader(handle) if int(r["n"]) == n and r["tracking_rms"]]
        summary = json.loads((folder / "summary.json").read_text(encoding="utf-8"))
        output = next(r for r in summary["outputs"] if r["n"] == n)
        close(max(float(r["spikiness"]) for r in rows if r["spikiness"]),
              condition["A_sp_recorded"], "recorded spikiness")
        close(max(float(r["tracking_rms"]) for r in rows), condition["path_max_r"], "peak r")
        close(max(float(r["objective_gap"]) for r in rows), condition["path_max_F_gap"], "peak F gap")
        close(float(rows[-1]["tracking_rms"]), condition["common_active_end_r"], "end r")
        close(abs(output["returned"]["objective"] - summary["population"]["returned"]["objective"]),
              condition["return_objective_gap"], "returned F gap")
        close(output["return_tracking_rms"], condition["return_tracking_rms"], "archived return r")
        for row in rows:
            close(abs(float(row["empirical_objective"]) - float(row["population_objective"])),
                  float(row["objective_gap"]), "trajectory F gap")
    if sum(c["return_tracking_rms"] > 1 for c in analysis["conditions"]) != 6:
        raise ValueError("large-discrepancy count differs")
    checks = {
        "integration_refinement": {"max_returned_state_rms_difference": 4.20e-10,
                                   "max_path_r_relative_difference": 2.54e-8},
        "trigger_refinement": {"max_returned_state_rms_difference": 4.95e-4,
                               "max_return_objective_difference": 4.89e-6}}
    for group, limits in checks.items():
        for key, limit in limits.items():
            if max(r[key] for r in analysis[group]) > limit:
                raise ValueError("archived refinement bound differs: " + key)
    print(json.dumps({"conditions_checked": 15, "scalar_records_match": True,
                      "scope": "scalar records and archived refinement summaries; no NPZ recomputation"}, indent=2))


if __name__ == "__main__":
    main()
