"""Audit all adaptive trials, then export timestamped, content-hashed figures."""

import argparse
import base64
import csv
from datetime import datetime, timezone
import hashlib
import html
import json
from pathlib import Path
import shutil
from zoneinfo import ZoneInfo

import numpy as np

# Please keep audit assertions enabled; optimized Python would skip them.
if not __debug__:
    raise RuntimeError("Please run this audit without Python -O or PYTHONOPTIMIZE")


def digest(path):
    result = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            result.update(chunk)
    return result.hexdigest()


def read_csv(path):
    with path.open(newline="") as handle:
        result = []
        for row in csv.DictReader(handle):
            result.append({k: v if k == "phase" else None if v == "" else float(v)
                           for k, v in row.items()})
        return result


def load_run(folder):
    metadata = json.loads((folder / "metadata.json").read_text())
    if metadata["status"] != "complete":
        raise ValueError("incomplete run: " + str(folder))
    return {"folder": folder, "metadata": metadata,
        "rows": read_csv(folder / "trajectory.csv"),
        "prows": read_csv(folder / "population.csv"),
        "events": json.loads((folder / "events.json").read_text()),
        "summary": json.loads((folder / "summary.json").read_text())}


def event_series(run):
    return {"population": run["events"]["population"], **run["events"]["empirical"]}


def audit_run(run):
    cfg, summary = run["metadata"]["config"], run["summary"]
    checks = {"controller_checks": 0, "coupling_max_relative_error": 0.,
              "polar_max_relative_error": 0., "unmatched_attempts": 0}
    with np.load(run["folder"] / "states.npz") as states:
        indices = states["indices"]
        checks["unique_initial_atoms_at_max_n"] = len(np.unique(indices))
        for name, events in event_series(run).items():
            out = summary["population"] if name == "population" else next(
                o for o in summary["outputs"] if o["n"] == int(name))
            prefix = "population" if name == "population" else "x_" + name
            last = -float("inf")
            for j, event in enumerate(events, 1):
                assert event["attempt"] == j
                assert event["time"] - last > cfg["wait_time"] - 1e-12
                assert event["pre_diagnostics"]["gradient_rms"] <= cfg["gradient_threshold"]
                last = event["time"]
                if "evaluation" in event:
                    e = event["evaluation"]
                    assert abs(e["time"] - event["time"] - cfg["wait_time"]) < 1e-10
                    decrease = event["pre_diagnostics"]["objective"] - e["objective"]
                    assert abs(decrease - e["decrease"]) < 1e-12
                    assert e["accepted"] == (decrease > cfg["decrease_threshold"])
                cd = event.get("coupling_diagnostics", {})
                checks["coupling_max_relative_error"] = max(checks["coupling_max_relative_error"],
                    cd.get("reduced_covariance_relative_error", 0.))
                checks["polar_max_relative_error"] = max(checks["polar_max_relative_error"],
                    cd.get("polar_relative_error", 0.))
                checks["unmatched_attempts"] += event.get("coupling") == "independent_unmatched"
                checks["controller_checks"] += 1
            if out["status"] == "stopped":
                assert events and not events[-1]["evaluation"]["accepted"]
                candidate = states[f"{prefix}_attempt_{len(events):03d}_pre"]
                assert np.array_equal(candidate, states[prefix + "_returned"])
                assert abs(out["returned"]["objective"] - events[-1]["pre_diagnostics"]["objective"]) < 1e-12
            if name != "population":
                stop = min(out["stop_time"] or cfg["end_time"],
                           summary["population"]["stop_time"] or cfg["end_time"])
                rows = [r for r in run["rows"] if r["n"] == int(name)]
                assert all(r["time"] <= stop + 1e-10 for r in rows if r["tracking_rms"] is not None)
                # Deterministic flow and shared fields preserve identical initial labels.
                _, first, inverse = np.unique(indices[:int(name)], return_index=True, return_inverse=True)
                actual = states[prefix + "_actual"]
                assert np.array_equal(actual, actual[first][inverse])
                for event in events:
                    phases = {r["phase"] for r in rows if abs(r["time"] - event["time"]) < 1e-10}
                    assert {"pre_jump", "post_jump"} <= phases
        assert checks["coupling_max_relative_error"] < 1e-10
        assert checks["polar_max_relative_error"] < 1e-10
    checks["passed"] = True
    return checks


def refinement(first, second):
    result = {"matching_event_counts": True, "max_event_time_difference": 0.,
              "max_stop_time_difference": 0., "max_returned_state_rms_difference": 0.,
              "max_return_objective_difference": 0., "max_return_tracking_rms_difference": 0.,
              "max_path_r_relative_difference": 0., "max_path_r_absolute_difference": 0.,
              "max_spikiness_difference": 0., "max_objective_gap_difference": 0.,
              "events": []}
    for name, left in event_series(first).items():
        right = event_series(second)[name]
        result["matching_event_counts"] &= len(left) == len(right)
        for a, b in zip(left, right):
            delta = abs(a["time"] - b["time"])
            result["max_event_time_difference"] = max(result["max_event_time_difference"], delta)
            result["events"].append({"system": name, "attempt": a["attempt"],
                                      "first_time": a["time"], "second_time": b["time"]})
    with np.load(first["folder"] / "states.npz") as left, np.load(second["folder"] / "states.npz") as right:
        assert np.array_equal(left["indices"], right["indices"])
        for key in left.files:
            if key.endswith("_returned") and key in right.files:
                diff = (left[key] - right[key]).reshape(len(left[key]), -1)
                rms = float(np.sqrt(np.mean(np.sum(diff * diff, axis=1))))
                result["max_returned_state_rms_difference"] = max(result["max_returned_state_rms_difference"], rms)
    for a, b in zip(first["summary"]["outputs"], second["summary"]["outputs"]):
        assert a["n"] == b["n"]
        if a["stop_time"] is not None and b["stop_time"] is not None:
            result["max_stop_time_difference"] = max(result["max_stop_time_difference"], abs(a["stop_time"] - b["stop_time"]))
        if "returned" in a and "returned" in b:
            result["max_return_objective_difference"] = max(result["max_return_objective_difference"],
                abs(a["returned"]["objective"] - b["returned"]["objective"]))
            result["max_return_tracking_rms_difference"] = max(result["max_return_tracking_rms_difference"],
                abs(a["return_tracking_rms"] - b["return_tracking_rms"]))
    # Common stored phases; jump-time differences are reported separately.
    indexed = {(r["n"], round(r["time"], 8), r["phase"]): r for r in second["rows"]}
    for a in first["rows"]:
        b = indexed.get((a["n"], round(a["time"], 8), a["phase"]))
        if b is None or a["tracking_rms"] is None or b["tracking_rms"] is None:
            continue
        delta = abs(a["tracking_rms"] - b["tracking_rms"])
        result["max_path_r_absolute_difference"] = max(result["max_path_r_absolute_difference"], delta)
        if max(a["tracking_rms"], b["tracking_rms"]) > 1e-10:
            result["max_path_r_relative_difference"] = max(result["max_path_r_relative_difference"],
                delta / max(a["tracking_rms"], b["tracking_rms"]))
        if a["spikiness"] is not None and b["spikiness"] is not None:
            result["max_spikiness_difference"] = max(result["max_spikiness_difference"], abs(a["spikiness"] - b["spikiness"]))
        result["max_objective_gap_difference"] = max(result["max_objective_gap_difference"], abs(a["objective_gap"] - b["objective_gap"]))
    return result


def analyze(root):
    status = json.loads((root / "runs/protocol_status.json").read_text())
    if status["status"] != "complete" or len(status["completed"]) != 9:
        raise ValueError("all nine jobs must complete before analysis")
    runs = {(variant, trial): load_run(root / "runs" / variant / f"trial_{trial:03d}")
            for variant in status["variants"] for trial in status["trials"]}
    audits = {f"{v}/trial_{t:03d}": audit_run(run) for (v, t), run in runs.items()}
    integration = [refinement(runs["main", t], runs["integration_half", t]) for t in status["trials"]]
    trigger = [refinement(runs["integration_half", t], runs["trigger_half", t]) for t in status["trials"]]
    # Failure is explicit; do not quietly replace the accepted main resolution.
    integration_pass = all(r["matching_event_counts"] and r["max_event_time_difference"] < 1e-10
        and r["max_stop_time_difference"] < 1e-10 and r["max_path_r_relative_difference"] < 1e-3
        and r["max_spikiness_difference"] < 1e-3 for r in integration)
    conditions = []
    for trial in status["trials"]:
        run = runs["main", trial]
        with np.load(run["folder"] / "states.npz") as states:
            factor_diagnostics = {}
            ap = np.tanh(states["population_returned"]).mean(axis=0)
            for output in run["summary"]["outputs"]:
                n = output["n"]
                ax = np.tanh(states[f"x_{n}_returned"]).mean(axis=0)
                u, _, vt = np.linalg.svd(ax.T @ ap)
                rotation = u @ vt
                factor_diagnostics[n] = {
                    "returned_matrix_gap": float(np.linalg.norm(ax @ ax.T - ap @ ap.T)),
                    "returned_factor_gap": float(np.linalg.norm(ax - ap)),
                    "returned_factor_gap_after_orthogonal_alignment": float(np.linalg.norm(ax @ rotation - ap)),
                    "returned_factor_alignment_determinant": float(np.linalg.det(rotation))}
        for output in run["summary"]["outputs"]:
            n = output["n"]
            rows = [r for r in run["rows"] if r["n"] == n and r["tracking_rms"] is not None]
            conditions.append({"trial": trial, **output, **factor_diagnostics[n],
                "population_stop_time": run["summary"]["population"]["stop_time"],
                "population_return_objective": run["summary"]["population"]["returned"]["objective"],
                "initial_gradient_rms": rows[0]["empirical_gradient_rms"],
                "common_active_end": max(r["time"] for r in rows),
                "common_active_end_r": rows[-1]["tracking_rms"],
                "peak_r_time": max(rows, key=lambda r: r["tracking_rms"])["time"],
                "peak_r_phase": max(rows, key=lambda r: r["tracking_rms"])["phase"],
                "path_max_r": max(r["tracking_rms"] for r in rows),
                "path_max_F_gap": max(r["objective_gap"] for r in rows),
                "A_sp_recorded": max(r["spikiness"] for r in rows if r["spikiness"] is not None),
                "jump_times": [e["time"] for e in run["events"]["empirical"][str(n)]],
                "unmatched_attempts": sum(e["coupling"] == "independent_unmatched"
                    for e in run["events"]["empirical"][str(n)])})
    analysis = {"run_id": root.name, "config": status["variants"]["main"], "trials": status["trials"],
        "conditions": conditions, "population": [runs["main", t]["summary"]["population"] for t in status["trials"]],
        "audits": audits, "integration_refinement_pass": integration_pass,
        "integration_refinement": integration, "trigger_refinement": trigger,
        "limitations": ["Three fixed seeds; descriptive evidence, not a convergence-rate estimate.",
            f"Fixed atomic population K={status['variants']['main']['population_size']}, not a certified continuous-law approximation.",
            "A_sp is a maximum over recorded common-active times, not all continuous times.",
            "Returned pre-jump candidates and executed final states are distinct.",
            "Event-index adaptive coupling is outside the synchronized prescribed-schedule theorem.",
            "Pointwise path differences under trigger refinement can be large at asynchronous jumps."]}
    return analysis, runs


def save_figure(fig, stem, folder, records, analysis_hash):
    now = datetime.now(ZoneInfo("Asia/Tokyo"))
    timestamp = now.strftime("%Y%m%d-%H%M%SJST")
    for extension in ("pdf", "png"):
        temporary = folder / f"{stem}_{timestamp}_pending.{extension}"
        kwargs = {"bbox_inches": "tight"}
        if extension == "pdf":
            kwargs["metadata"] = {"Title": stem, "Subject": "analysis SHA256 " + analysis_hash,
                                  "CreationDate": now, "ModDate": now}
        else:
            kwargs.update(dpi=170, metadata={"AnalysisSHA256": analysis_hash})
        fig.savefig(temporary, **kwargs)
        sha = digest(temporary)
        final = folder / f"{stem}_{timestamp}_{sha[:12]}.{extension}"
        if final.exists():
            raise FileExistsError(final)
        temporary.rename(final)
        records.append({"kind": stem, "path": str(final.relative_to(folder.parent)),
                        "sha256": sha, "bytes": final.stat().st_size, "created_at": now.isoformat()})


def figures(analysis, runs, out, analysis_hash):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.lines import Line2D
    plt.rcParams.update({"font.size": 10, "axes.spines.top": False, "axes.spines.right": False,
                         "axes.grid": True, "grid.alpha": .2, "pdf.fonttype": 42})
    folder = out / "figures"
    folder.mkdir(exist_ok=False)
    ns, trials = analysis["config"]["particle_counts"], analysis["trials"]
    tag = f"adaptive_K{analysis['config']['population_size']}"
    colors = dict(zip(ns, plt.get_cmap("viridis")(np.linspace(.08, .87, len(ns)))))
    records = []
    fig, axes = plt.subplots(3, 3, figsize=(14, 10), sharex="col", constrained_layout=True)
    for col, trial in enumerate(trials):
        run = runs["main", trial]
        for n in ns:
            rows = [r for r in run["rows"] if r["n"] == n and r["tracking_rms"] is not None]
            ts = [r["time"] for r in rows]
            axes[0, col].plot(ts, [r["tracking_rms"] for r in rows], color=colors[n], lw=1.35)
            axes[1, col].plot(ts, [r["objective_gap"] for r in rows], color=colors[n], lw=1.35)
            spikes = [(r["time"], r["spikiness"]) for r in rows if r["spikiness"] is not None]
            axes[2, col].plot([x[0] for x in spikes], np.maximum.accumulate([x[1] for x in spikes]), color=colors[n], lw=1.35)
            for event in run["events"]["empirical"][str(n)]:
                match = [r for r in rows if abs(r["time"] - event["time"]) < 1e-9 and r["phase"] == "post_jump"]
                if match:
                    axes[0, col].plot(event["time"], match[0]["tracking_rms"], "o", color=colors[n], ms=4)
        for ax in axes[:, col]:
            for event in run["events"]["population"]:
                ax.axvline(event["time"], color="black", lw=.8, ls=":", alpha=.5)
            ax.set_xlim(left=0)
        axes[0, col].set_title(f"Trial {trial}")
        axes[2, col].set_xlabel("Physical time t")
    axes[0, 0].set_ylabel(r"Paired trajectory error $r_t$")
    axes[1, 0].set_ylabel(r"Objective gap $|F_X(t)-F_P(t)|$")
    axes[2, 0].set_ylabel(r"$A_{\rm sp}(t)$: recorded running maximum")
    fig.suptitle("Autonomous adaptive PWGF | common-active trajectories\n"
                 "Dots: empirical jumps; dotted vertical lines: population jumps", fontsize=14)
    axes[0, 1].legend([Line2D([], [], color=colors[n]) for n in ns], [f"N={n:,}" for n in ns], fontsize=8)
    save_figure(fig, tag + "_time_tracking", folder, records, analysis_hash)
    plt.close(fig)

    fig, axes = plt.subplots(1, 3, figsize=(14, 3.8), constrained_layout=True)
    for ax, trial in zip(axes, trials):
        run = runs["main", trial]
        for n in ns:
            rows = [r for r in run["rows"] if r["n"] == n and r["spikiness"] is not None]
            ax.plot([r["time"] for r in rows], [r["spikiness"] for r in rows], color=colors[n], lw=1.2)
        ax.set(title=f"Trial {trial}", xlabel="Physical time t", xlim=(0, None))
    axes[0].set_ylabel(r"Instantaneous ratio $E_N[\|\delta_t\|^3]/r_t^3$")
    axes[1].legend([Line2D([], [], color=colors[n]) for n in ns],
                   [f"N={n:,}" for n in ns], fontsize=8, loc="upper right")
    fig.suptitle("Spikiness ratio at recorded times | distinct from its running maximum")
    save_figure(fig, tag + "_instantaneous_spikiness", folder, records, analysis_hash)
    plt.close(fig)

    fig, axes = plt.subplots(3, 1, figsize=(12, 9), constrained_layout=True)
    for ax, trial in zip(axes, trials):
        run = runs["main", trial]
        for row, name in enumerate(["population"] + [str(n) for n in ns]):
            obj = run["summary"]["population"] if name == "population" else next(o for o in run["summary"]["outputs"] if o["n"] == int(name))
            color = "#20262e" if name == "population" else colors[int(name)]
            end = obj["stop_time"] or analysis["config"]["end_time"]
            ax.plot([0, end], [row, row], color=color, alpha=.65, lw=2)
            for e in event_series(run)[name]:
                marker = "o" if e.get("evaluation", {}).get("accepted") else "^"
                ax.plot(e["time"], row, marker, color=color, ms=7, clip_on=False)
                if e.get("coupling") == "independent_unmatched":
                    ax.plot(e["time"], row, "s", ms=11, mfc="none", mec=color, mew=1.3)
            ax.plot(end, row, "x", color=color, ms=7)
        ax.set_yticks(range(6), ["Population"] + [f"N={n:,}" for n in ns])
        ax.invert_yaxis()
        ax.set(title=f"Trial {trial}", xlabel="Physical time t", xlim=(-.5, None))
    fig.suptitle("Independent schedules | circle: passed test; triangle: returned candidate; x: stop\n"
                 "Open square: unmatched empirical attempt (independent noise)")
    save_figure(fig, tag + "_schedules", folder, records, analysis_hash)
    plt.close(fig)

    fig, axes = plt.subplots(1, 3, figsize=(14, 4), constrained_layout=True)
    for ax, trial in zip(axes, trials):
        run = runs["main", trial]
        ax.plot([r["time"] for r in run["prows"]], [r["objective"] for r in run["prows"]], color="black", lw=1.8, label="Population")
        if run["summary"]["population"]["returned"] is not None:
            ax.plot(run["events"]["population"][-1]["time"],
                    run["summary"]["population"]["returned"]["objective"], "*", ms=9, color="black")
        for n in ns:
            rows = [r for r in run["rows"] if r["n"] == n]
            ax.plot([r["time"] for r in rows], [r["empirical_objective"] for r in rows], color=colors[n], lw=1.2, label=f"N={n:,}")
            obj = next(o for o in run["summary"]["outputs"] if o["n"] == n)
            if "returned" in obj:
                ax.plot(obj["candidate_time"], obj["returned"]["objective"], "*", ms=8, color=colors[n])
        ax.set(title=f"Trial {trial}", xlabel="Physical time t", yscale="log", xlim=(0, None))
    axes[0].set_ylabel("Objective F (minimum = 0)")
    axes[2].legend(fontsize=8)
    fig.suptitle("Executed objectives until each system stops | stars: returned pre-jump candidates")
    save_figure(fig, tag + "_objectives", folder, records, analysis_hash)
    plt.close(fig)

    fig, axes = plt.subplots(1, 3, figsize=(13, 3.8), constrained_layout=True)
    for trial in trials:
        rows = [r for r in analysis["conditions"] if r["trial"] == trial]
        for ax, key in zip(axes, ("return_tracking_rms", "return_objective_gap", "A_sp_recorded")):
            ax.plot(ns, [r[key] for r in rows], "o-", label=f"Trial {trial}")
            ax.set_xscale("log", base=2)
            ax.set_xticks(ns, [f"{n//1024}k" for n in ns])
            ax.set_xlabel("Particle count N (k = 1024)")
    axes[0].set(yscale="log", ylabel="Returned-candidate paired RMS")
    axes[1].set(yscale="log", ylabel="Returned-candidate objective gap")
    axes[2].set_ylabel(r"$A_{\rm sp}$ over common-active records")
    axes[0].legend()
    fig.suptitle("Returned outputs and recorded spikiness | three fixed seeds, no rate fit")
    save_figure(fig, tag + "_returned_outputs", folder, records, analysis_hash)
    plt.close(fig)
    return records


def report(analysis, manifest, out):
    """Write an English report; numerical analysis and plotting are separate."""
    cond = analysis["conditions"]
    cfg = analysis["config"]
    largest = [r for r in cond if r["n"] == max(cfg["particle_counts"])]
    large = [r for r in cond if r["return_tracking_rms"] > 1]
    integration = analysis["integration_refinement"]
    trigger = analysis["trigger_refinement"]
    model_note = ("Each particle W is a 32-by-2 matrix. A = E[tanh(W)] and "
        "F = ||A A^T - M_*||_F^2 / 4. The target has nonzero eigenvalues "
        "1 and 1/2, and the minimum objective is zero. "
        f"The population has K={cfg['population_size']} equally weighted antithetic atoms. "
        "Empirical initial labels are sampled with replacement. K is fixed across N; "
        "N=K does not assign one particle to each atom.")
    controller_note = (f"Particle counts: {cfg['particle_counts']}. Each system uses only its own "
        f"gradient and objective for control. Gradient RMS <= {cfg['gradient_threshold']} "
        f"triggers a jump of amplitude {cfg['jump_strength']}. After {cfg['wait_time']} "
        f"units of flow time, a decrease <= {cfg['decrease_threshold']} causes the "
        f"saved pre-jump candidate to be returned. Checks begin at t=0 with interval "
        f"{cfg['check_interval']}; RK4 step {cfg['dt']}; observation cap {cfg['end_time']}. "
        "A passed decrease test resumes inspection on the next tick.")
    coupling_note = ("Attempts are coupled by index using the saved population pre-state. "
        "Physical jump times can differ. Unmatched empirical attempts use independent "
        "noise. The final attempt whose decrease test fails is included.")
    measurement_note = ("For the same initial labels, delta_i(t)=X_i(t)-Y_i(t) and "
        "r_t=sqrt(mean(||delta_i(t)||_F^2)). The instantaneous spikiness ratio is "
        "s_t=mean(||delta_i(t)||_F^3)/r_t^3. A_sp(t) is its recorded running maximum. "
        "Ratios with numerically negligible denominators are omitted. Pairwise curves "
        "end when either system stops. Returned candidates may have different times; "
        "executed paths are not rewound to their candidates.")
    largest_note = (f"At N={largest[0]['n']}, recorded peak r_t ranges from "
        f"{min(r['path_max_r'] for r in largest):.3f} to {max(r['path_max_r'] for r in largest):.3f}. "
        f"At the end of the common-active interval it ranges from "
        f"{min(r['common_active_end_r'] for r in largest):.3f} to "
        f"{max(r['common_active_end_r'] for r in largest):.3f}; "
        f"returned-candidate RMS ranges from {min(r['return_tracking_rms'] for r in largest):.3f} "
        f"to {max(r['return_tracking_rms'] for r in largest):.3f}.")
    outlier_note = "Returned RMS above 1: " + "; ".join(
        f"trial {r['trial']}, N={r['n']} ({r['return_tracking_rms']:.3f})"
        for r in large) + ". All conditions are retained."
    factor_note = (f"For these {len(large)} conditions, the largest reconstruction-matrix "
        f"gap is {max(r['returned_matrix_gap'] for r in large):.4g}, and the largest "
        f"mean-factor gap after orthogonal alignment is "
        f"{max(r['returned_factor_gap_after_orthogonal_alignment'] for r in large):.4g}. "
        "The plotted particle distances have no alignment applied.") if large else ""
    result_notes = [
        f"The empirical systems stopped in {sum(r['status']=='stopped' for r in cond)}/{len(cond)} conditions.",
        f"The largest recorded A_sp is {max(r['A_sp_recorded'] for r in cond):.8f}; "
        "this is not a continuous-time or high-probability bound.",
        largest_note, outlier_note, factor_note,
        f"Returned F ranges from {min(r['returned']['objective'] for r in cond):.3g} to "
        f"{max(r['returned']['objective'] for r in cond):.3g}. These are candidates "
        "returned under the specified thresholds, not limits of indefinite flow.",
        f"In {sum(r['initial_gradient_rms'] > cfg['gradient_threshold'] for r in cond)}/{len(cond)} "
        "conditions the initial empirical gradient exceeds the threshold and no jump "
        "occurs at t=0. All population trials jump at t=0.",
        f"There are {sum(r['unmatched_attempts'] for r in cond)} unmatched empirical attempts: "
        + "; ".join(f"trial {r['trial']}, N={r['n']} ({r['unmatched_attempts']})"
                    for r in cond if r['unmatched_attempts']) + "."]
    validation = [
        f"All nine archived job audits passed. Integration-refinement gate: "
        f"{analysis['integration_refinement_pass']}.",
        f"Halving the RK4 step changes jump times by at most "
        f"{max(r['max_event_time_difference'] for r in integration):.3g}, "
        f"and matched-record r_t by a relative amount at most "
        f"{max(r['max_path_r_relative_difference'] for r in integration):.3g}.",
        f"Halving the inspection interval changes jump times by at most "
        f"{max(r['max_event_time_difference'] for r in trigger):.6g}, and returned states "
        f"by an RMS amount at most {max(r['max_returned_state_rms_difference'] for r in trigger):.6g}.",
        f"Attempt counts agree under inspection refinement: "
        f"{all(r['matching_event_counts'] for r in trigger)}. The largest returned F "
        f"change is {max(r['max_return_objective_difference'] for r in trigger):.6g}.",
        "Small returned-objective gaps should be interpreted with this grid sensitivity "
        "in mind. Asynchronous-jump mismatches are distinct from ODE integration errors."]
    limitations = ("Three trials and a fixed atomic population provide descriptive evidence. "
        "They establish neither a convergence rate, adaptive superiority, nor an all-time "
        "non-spikiness bound. Attempt-index adaptive coupling is outside the prescribed "
        "common-schedule theorem. A same-time supremum discrepancy can retain a jump-sized "
        "peak even as the jump-time lag shrinks. Spikiness concerns paired errors, not "
        "the spread of particle positions.")
    provenance_note = ("Each PDF/PNG filename records its generation time in JST and the "
        "first 12 hexadecimal digits of its own SHA-256. The figure manifest records "
        "full hashes and input provenance. See the package README for the distinction "
        "between archived scalar records, optional state snapshots, and a full rerun.")
    headers = ["trial", "N", "jump times", "stop", "returned r", "returned F gap",
               "returned F", "recorded A_sp"]
    cells = [[str(r['trial']), str(r['n']), ", ".join(f"{t:.2f}" for t in r['jump_times']),
              f"{r['stop_time']:.2f}", f"{r['return_tracking_rms']:.6g}",
              f"{r['return_objective_gap']:.6g}", f"{r['returned']['objective']:.6g}",
              f"{r['A_sp_recorded']:.6f}"] for r in cond]
    lines = ["# Adaptive matrix-factorization sanity check", "", "## Setup", "",
             model_note, "", controller_note, "", coupling_note, "", "## Measurements", "",
             measurement_note, "", "## Results", "", *result_notes, "",
             "|" + "|".join(headers) + "|", "|" + "|".join(["---"] * len(headers)) + "|"]
    lines.extend("|" + "|".join(row) + "|" for row in cells)
    lines.extend(["", "## Numerical checks", "", *validation, "", "## Limitations", "",
                  limitations, "", "## Provenance", "", provenance_note, ""])
    pictures = []
    for item in manifest["figures"]:
        if not item["path"].endswith(".png"):
            continue
        png = out / item["path"]
        pdf = next(x for x in manifest["figures"]
                   if x["kind"] == item["kind"] and x["path"].endswith(".pdf"))
        image_data = base64.b64encode(png.read_bytes()).decode()
        pdf_data = base64.b64encode((out / pdf["path"]).read_bytes()).decode()
        pictures.append(f'<figure><img src="data:image/png;base64,{image_data}" '
            f'alt="{html.escape(item["kind"])}"><figcaption>{html.escape(png.name)} '
            f'<a download="{html.escape(Path(pdf["path"]).name)}" '
            f'href="data:application/pdf;base64,{pdf_data}">PDF</a></figcaption></figure>')
        lines.append(f"![{item['kind']}]({item['path']})\n")
    (out / "REPORT.md").write_text("\n".join(lines), encoding="utf-8")
    table = "".join("<tr>" + "".join(f"<td>{html.escape(value)}</td>" for value in row)
                    + "</tr>" for row in cells)
    def paragraphs(values):
        return "".join(f"<p>{html.escape(value)}</p>" for value in values if value)
    download = base64.b64encode(json.dumps(manifest, indent=2).encode()).decode()
    page = f'''<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Adaptive matrix-factorization sanity check</title><style>
body{{font-family:system-ui,sans-serif;color:#1b2838;background:#f5f7fa;margin:0;line-height:1.6}}
main{{max-width:1180px;margin:auto;padding:32px 24px}}figure{{background:white;padding:16px}}
img{{width:100%;height:auto}}figcaption{{overflow-wrap:anywhere}}.table{{overflow-x:auto}}
table{{border-collapse:collapse;white-space:nowrap}}th,td{{padding:8px;border-bottom:1px solid #ddd}}
a{{color:#1264a3}}
</style></head><body><main><p>{html.escape(analysis['run_id'])}</p>
<h1>Adaptive matrix-factorization sanity check</h1>
<h2>Setup</h2>{paragraphs([model_note, controller_note, coupling_note])}
<h2>Measurements</h2>{paragraphs([measurement_note])}
<h2>Results</h2>{paragraphs(result_notes)}
<div class="table"><table><thead><tr>{''.join('<th>'+html.escape(x)+'</th>' for x in headers)}</tr></thead><tbody>{table}</tbody></table></div>
{''.join(pictures)}
<h2>Numerical checks</h2>{paragraphs(validation)}
<h2>Limitations</h2>{paragraphs([limitations])}
<h2>Provenance</h2>{paragraphs([provenance_note])}
<p><a download="figure_manifest.json" href="data:application/json;base64,{download}">Download figure manifest</a></p>
</main></body></html>'''
    (out / "adaptive_report.html").write_text(page, encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    root, out = args.root.resolve(), args.out.resolve()
    analysis, runs = analyze(root)
    out.mkdir(parents=True, exist_ok=False)
    text = json.dumps(analysis, indent=2, allow_nan=False) + "\n"
    (out / "analysis.json").write_text(text)
    flat = []
    for condition in analysis["conditions"]:
        row = {k: v for k, v in condition.items() if not isinstance(v, (dict, list))}
        row["jump_times"] = ";".join(str(t) for t in condition["jump_times"])
        row.update({"returned_" + k: v for k, v in condition["returned"].items()})
        flat.append(row)
    with (out / "summary.csv").open("x", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(flat[0]))
        writer.writeheader()
        writer.writerows(flat)
    shutil.copy2(__file__, out / "render_source.py")
    figure_records = figures(analysis, runs, out, digest(out / "analysis.json"))
    files = [p for p in (root / "source").iterdir() if p.is_file()]
    files += [p for p in (root / "runs").rglob("*") if p.suffix in (".json", ".csv", ".npz")]
    manifest = {"created_at": datetime.now(timezone.utc).isoformat(), "run_id": root.name,
        "analysis_sha256": digest(out / "analysis.json"), "render_source_sha256": digest(out / "render_source.py"),
        "summary_csv_sha256": digest(out / "summary.csv"),
        "inputs": {str(p.relative_to(root)): digest(p) for p in sorted(files)},
        "figures": figure_records}
    (out / "figure_manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    report(analysis, manifest, out)
    print(json.dumps({"output": str(out), "integration_refinement_pass": analysis["integration_refinement_pass"],
        "max_A_sp": max(r["A_sp_recorded"] for r in analysis["conditions"]),
        "conditions": analysis["conditions"]}, allow_nan=False))
    # Please retain the report on failure, but do not report verification success.
    if not analysis["integration_refinement_pass"]:
        raise SystemExit("Integration refinement failed; please inspect analysis.json")


if __name__ == "__main__":
    main()
