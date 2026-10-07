#!/usr/bin/env python3
"""Recompute saved-state quantities independently, and replay recorded jumps.

Please distinguish the independent mathematical identities from the same-code
RNG replay. This does not reconstruct states at every inspection time.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
import time

for setting in ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(setting, "1")

import numpy as np

SOURCE = Path(__file__).resolve().parent / "source"
sys.path.insert(0, str(SOURCE))
from model import MatrixModel
from coupling import population_field, empirical_field, reduced_factors


def digest(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def independent_target(d):
    signs = 1.0 - 2.0 * (np.arange(d) % 2)
    return (np.ones((d, d)) + 0.5 * np.outer(signs, signs)) / d


def independent_quantities(state, target):
    if state.ndim != 3 or state.shape[1:] != (len(target), 2) or not np.isfinite(state).all():
        raise ValueError("Invalid saved particle array")
    features = np.tanh(state)
    a = np.mean(features, axis=0)
    residual = a @ a.T - target
    gradient = (1.0 - features ** 2) * (residual @ a)
    loss = np.sum(residual ** 2) / 4.0
    return {
        "objective": float(loss),
        "gradient_rms": float(np.sqrt(np.mean(np.sum(gradient ** 2, axis=(1, 2))))),
        "target_relative_error": float(np.linalg.norm(residual) / np.linalg.norm(target)),
    }


def independent_hessian(a, target):
    d, rank = a.shape
    residual = a @ a.T - target
    gram = a.T @ a
    tensor = (np.einsum("ij,ab->iajb", residual, np.eye(rank))
              + np.einsum("ij,ab->iajb", np.eye(d), gram)
              + np.einsum("ib,ja->iajb", a, a))
    return tensor.reshape(d * rank, d * rank)


def close(actual, expected, label, stats, tolerance=1e-10):
    a, b = np.asarray(actual), np.asarray(expected)
    if a.shape != b.shape or not np.isfinite(a).all() or not np.isfinite(b).all():
        raise AssertionError(f"Invalid comparison: {label}")
    error = float(np.linalg.norm(a - b) / max(1.0, float(np.linalg.norm(b))))
    stats["max_scaled_error"] = max(stats["max_scaled_error"], error)
    stats["comparisons"] += 1
    if error > tolerance:
        raise AssertionError(f"{label}: scaled error {error} exceeds {tolerance}")


def audit_job(folder):
    metadata = json.loads((folder / "metadata.json").read_text())
    events = json.loads((folder / "events.json").read_text())
    summary = json.loads((folder / "summary.json").read_text())
    if metadata["status"] != "complete":
        raise AssertionError("Incomplete simulation")
    cfg, trial = metadata["config"], metadata["trial"]
    for name, expected in metadata["source_sha256"].items():
        if digest(SOURCE / name) != expected:
            raise AssertionError(f"Simulation source changed: {name}")
    target = independent_target(cfg["d"])
    # The production target is regenerated for exact same-code jump replay.
    from model import target_matrix, initial_population
    model = MatrixModel(target_matrix(cfg["d"]))
    stats = {"comparisons": 0, "max_scaled_error": 0.0, "saved_arrays": 0,
             "independent_hessians": 0, "replayed_jumps": 0,
             "covariance_checks": 0, "max_covariance_relative_error": 0.0}
    close(model.target, target, "independent target", stats)
    initial = initial_population(cfg["population_size"], cfg["d"], cfg["population_seed"])
    if hashlib.sha256(initial.tobytes()).hexdigest() != summary["population_sha256"]:
        raise AssertionError("Initial population identity changed")
    q = cfg["d"] * 2
    rng = lambda kind, n=None: np.random.default_rng(np.random.SeedSequence(
        [cfg["trial_seed"], trial, kind] + ([] if n is None else [n])))
    population_normals = rng(1).normal(size=(len(events["population"]), q))
    with np.load(folder / "states.npz", allow_pickle=False) as states:
        indices = states["indices"]
        expected_indices = rng(0).integers(0, len(initial), size=max(cfg["particle_counts"]))
        if not np.array_equal(indices, expected_indices):
            raise AssertionError("Initial sampled labels differ from their seed stream")
        info = {}
        for key in states.files:
            if key == "indices":
                continue
            state = states[key]
            expected_n = cfg["population_size"] if key.startswith("population_") else int(key.split("_")[1])
            if len(state) != expected_n:
                raise AssertionError(f"Wrong number of particles: {key}")
            info[key] = independent_quantities(state, target)
            stats["saved_arrays"] += 1
        series = {"population": events["population"], **events["empirical"]}
        for name, sequence in series.items():
            prefix = "population" if name == "population" else "x_" + name
            output = summary["population"] if name == "population" else next(
                x for x in summary["outputs"] if x["n"] == int(name))
            for phase in ("actual", "returned"):
                if output.get(phase) is not None:
                    for metric, value in info[prefix + "_" + phase].items():
                        close(value, output[phase][metric], prefix + " " + phase + " " + metric, stats)
            if output["status"] == "stopped":
                pre = states[f"{prefix}_attempt_{len(sequence):03d}_pre"]
                if not np.array_equal(pre, states[prefix + "_returned"]):
                    raise AssertionError("Returned state is not the failed attempt's pre-jump state")
                if sequence[-1]["evaluation"]["accepted"]:
                    raise AssertionError("Stopped despite an accepted decrease test")
                for metric, value in info[prefix + "_actual"].items():
                    close(value, sequence[-1]["evaluation"][metric], prefix + " stop " + metric, stats)
            for j, event in enumerate(sequence, 1):
                if event["attempt"] != j:
                    raise AssertionError("Invalid attempt index")
                key = f"{prefix}_attempt_{j:03d}_pre"
                pre = states[key]
                for metric, value in info[key].items():
                    close(value, event["pre_diagnostics"][metric], key + " " + metric, stats)
                a = np.tanh(pre).mean(axis=0)
                h = independent_hessian(a, target)
                close(h, model.hessian(a), key + " closed-form Hessian", stats)
                close(h, h.T, key + " Hessian symmetry", stats)
                direction = np.sin(np.arange(q) + 0.25).reshape(a.shape)
                direction /= np.linalg.norm(direction)
                epsilon = 1e-5
                grad = lambda b: (b @ b.T - target) @ b
                finite_difference = (grad(a + epsilon * direction) - grad(a - epsilon * direction)) / (2 * epsilon)
                close((h @ direction.ravel()).reshape(a.shape), finite_difference,
                      key + " independent Hessian difference quotient", stats, tolerance=2e-7)
                stats["independent_hessians"] += 1
            if name != "population":
                n = int(name)
                _, first, inverse = np.unique(indices[:n], return_index=True, return_inverse=True)
                actual = states[prefix + "_actual"]
                if not np.array_equal(actual, actual[first][inverse]):
                    raise AssertionError("Duplicate initial labels diverged")
                if output.get("returned") is not None and summary["population"].get("returned") is not None:
                    x = states[prefix + "_returned"]
                    y = states["population_returned"][indices[:n]]
                    norms = np.linalg.norm((x - y).reshape(n, -1), axis=1)
                    rms = float(np.sqrt(np.mean(norms ** 2)))
                    close(rms, output["return_tracking_rms"], prefix + " returned RMS", stats)
                    close(abs(info[prefix + "_returned"]["objective"] - info["population_returned"]["objective"]),
                          output["return_objective_gap"], prefix + " returned objective gap", stats)
                    if output.get("return_spikiness") is not None:
                        close(float(np.mean((norms / rms) ** 3)), output["return_spikiness"],
                              prefix + " returned spikiness", stats)
        population_data = []
        for j, z in enumerate(population_normals, 1):
            pre = states[f"population_attempt_{j:03d}_pre"]
            field, hp, sp = population_field(model, pre, z)
            close(pre + cfg["jump_strength"] * field, states[f"population_attempt_{j:03d}_post"],
                  "population jump replay", stats)
            population_data.append((pre, hp, sp, z))
            stats["replayed_jumps"] += 1
        for name, sequence in events["empirical"].items():
            n = int(name)
            auxiliary, fallback = rng(2, n), rng(3, n)
            for j, event in enumerate(sequence, 1):
                pre = states[f"x_{n}_attempt_{j:03d}_pre"]
                za = auxiliary.normal(size=q)
                if j <= len(population_data):
                    if event["coupling"] != "matched_attempt":
                        raise AssertionError("Incorrect matched-attempt label")
                    population_pre, hp, sp, z = population_data[j - 1]
                    y = population_pre[indices[:n]]
                    field, _ = empirical_field(model, pre, y, hp, sp, z, za)
                    jx, lx, ep, ea, _ = reduced_factors(model, pre, y, hp, sp)
                    direct_jac = (1 - np.tanh(pre) ** 2).reshape(n, q)
                    sx = np.mean(direct_jac ** 2, axis=0)
                    covariance = ep @ ep.T + ea @ ea.T
                    relative = float(np.linalg.norm(covariance - np.diag(sx)) / max(np.linalg.norm(sx), 1e-300))
                    stats["max_covariance_relative_error"] = max(stats["max_covariance_relative_error"], relative)
                    if relative > 1e-10:
                        raise AssertionError("Recomputed Gaussian coefficient covariance failed")
                    h = independent_hessian(np.tanh(pre).mean(axis=0), target)
                    selected = np.vstack([direct_jac[k, :, None] * h for k in [0, n // 2, n - 1]])
                    actual_covariance = (selected @ ep) @ (selected @ ep).T + (selected @ ea) @ (selected @ ea).T
                    expected_covariance = (selected * sx) @ selected.T
                    close(actual_covariance, expected_covariance, "three-point Gaussian field covariance", stats)
                    stats["covariance_checks"] += 1
                else:
                    if event["coupling"] != "independent_unmatched":
                        raise AssertionError("Incorrect unmatched-attempt label")
                    field, _, _ = population_field(model, pre, fallback.normal(size=q))
                close(pre + cfg["jump_strength"] * field, states[f"x_{n}_attempt_{j:03d}_post"],
                      "empirical jump RNG replay", stats)
                stats["replayed_jumps"] += 1
    stats.update(status="passed", trial=trial,
                 files_sha256={p.name: digest(p) for p in sorted(folder.iterdir()) if p.suffix in (".json", ".csv", ".npz")})
    return stats


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runs", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if args.out.exists():
        parser.error("Please choose a new receipt path instead of overwriting evidence")
    status = json.loads((args.runs / "protocol_status.json").read_text())
    expected = {(v, t) for v in ("main", "integration_half", "trigger_half") for t in (0, 1, 2)}
    completed = [(r["variant"], r["trial"]) for r in status["completed"]]
    if status["status"] != "complete" or status["failed"] or set(completed) != expected or len(completed) != 9:
        raise RuntimeError("The complete fixed nine-job protocol is required")
    receipt = {"status": "running", "jobs": {}, "audit_source_sha256": digest(__file__),
        "scope": "Independent target/objective/gradient/Hessian and saved-state checks; same-code RNG jump replay; recomputed low-dimensional and selected-point field covariances. Not a proof for all paths or a statistical convergence-rate guarantee.",
        "not_reconstructed": ["All intermediate inspection states", "All successful decrease-test states", "Original Linux/MKL raw states, which are absent"]}
    started = time.monotonic()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    try:
        for variant, trial in sorted(expected):
            name = f"{variant}/trial_{trial:03d}"
            receipt["jobs"][name] = audit_job(args.runs / name)
            print("Independently checked " + name, flush=True)
        receipt["status"] = "passed"
    except BaseException as error:
        receipt["status"] = "failed"
        receipt["error"] = str(error)
        raise
    finally:
        receipt["elapsed_seconds"] = time.monotonic() - started
        args.out.write_text(json.dumps(receipt, indent=2, allow_nan=False) + "\n")


if __name__ == "__main__":
    main()
