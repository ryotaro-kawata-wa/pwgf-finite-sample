#!/usr/bin/env python3
"""Compare recorded platforms without treating platform equality as a test."""
import argparse
import hashlib
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    root = Path(__file__).resolve().parent
    parser.add_argument("--original", type=Path, default=root / "original/report/analysis.json")
    parser.add_argument("--fresh", type=Path, default=root / "results/report/analysis.json")
    parser.add_argument("--audit", type=Path, default=root / "verification/state-audit.json")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if args.out.exists():
        parser.error("Please select a new output path")
    old, fresh, audit = [json.loads(p.read_text()) for p in (args.original, args.fresh, args.audit)]
    before = {(r["trial"], r["n"]): r for r in old["conditions"]}
    after = {(r["trial"], r["n"]): r for r in fresh["conditions"]}
    if len(before) != 15 or before.keys() != after.keys() or len(fresh["conditions"]) != 15:
        raise ValueError("Please compare the complete fifteen-condition main grid")
    if audit["status"] != "passed" or len(audit["jobs"]) != 9:
        raise ValueError("A passed nine-job state audit is required")
    names = ("path_max_r", "common_active_end_r", "return_tracking_rms", "return_objective_gap", "A_sp_recorded")
    conditions, changed = [], []
    for key in sorted(before):
        a, b = before[key], after[key]
        row = {"trial": key[0], "n": key[1],
               "same_stop_time": a["stop_time"] == b["stop_time"],
               "same_jump_times": a["jump_times"] == b["jump_times"],
               "absolute_differences": {name: abs(a[name] - b[name]) for name in names}}
        conditions.append(row)
        if not row["same_stop_time"] or not row["same_jump_times"]:
            changed.append({"trial": key[0], "n": key[1],
                            "original_stop_time": a["stop_time"], "fresh_stop_time": b["stop_time"],
                            "original_jump_times": a["jump_times"], "fresh_jump_times": b["jump_times"]})
    result = {
        "input_sha256": {name: hashlib.sha256(p.read_bytes()).hexdigest()
                         for name, p in [("original", args.original), ("fresh", args.fresh), ("audit", args.audit)]},
        "integration_refinement_pass": fresh["integration_refinement_pass"],
        "all_nine_state_audits_passed": all(r["status"] == "passed" for r in audit["jobs"].values()),
        "conditions": conditions, "changed_event_conditions": changed,
        "max_absolute_differences": {name: max(r["absolute_differences"][name] for r in conditions) for name in names},
        "matching_stop_times": sum(r["same_stop_time"] for r in conditions),
        "matching_jump_schedules": sum(r["same_jump_times"] for r in conditions),
        "max_integration_path_relative_difference": max(r["max_path_r_relative_difference"] for r in fresh["integration_refinement"]),
        "max_integration_spikiness_difference": max(r["max_spikiness_difference"] for r in fresh["integration_refinement"]),
        "state_audit_totals": {name: sum(r[name] for r in audit["jobs"].values())
                               for name in ("saved_arrays", "independent_hessians", "replayed_jumps", "covariance_checks", "comparisons")},
        "max_recomputed_covariance_relative_error": max(r["max_covariance_relative_error"] for r in audit["jobs"].values()),
        "scope": "This compares the supplied executed reports, not raw trajectory identity across platforms. Independent mathematical checks and same-code RNG replay remain separate.",
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, allow_nan=False) + "\n")
    if not result["integration_refinement_pass"] or not result["all_nine_state_audits_passed"]:
        raise SystemExit("An execution or state audit failed; please inspect the report")
    print(f"Compared 15 conditions: {len(changed)} changed event schedule(s)")


if __name__ == "__main__":
    main()
