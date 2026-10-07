"""Autonomous adaptive PWGF, with coupling indexed by attempted jumps.

The population is simulated first to freeze its event pre-states, then replayed
alongside empirical systems for same-clock diagnostics. Empirical controllers
never read the population, reference particles, or diagnostic errors.
"""

import argparse
from dataclasses import dataclass
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import sys
import time
import csv

import numpy as np

from coupling import empirical_field, population_field
from model import MatrixModel, discrepancy_metrics, initial_population, rk4_step, target_matrix


@dataclass(frozen=True)
class Config:
    d: int
    population_size: int
    particle_counts: list
    population_seed: int
    trial_seed: int
    jump_strength: float
    gradient_threshold: float
    wait_time: float
    decrease_threshold: float
    end_time: float
    dt: float
    check_interval: float

    def __post_init__(self):
        for key in ("d", "population_size", "population_seed", "trial_seed"):
            value = getattr(self, key)
            if type(value) is not int or value < 0:
                raise ValueError(key + " must be a nonnegative integer")
        if self.d < 2 or self.d % 2 or self.population_size < 2 or self.population_size % 2:
            raise ValueError("d and population_size must be even and >= 2")
        ns = self.particle_counts
        if not isinstance(ns, list) or not ns or any(type(n) is not int or n < 2 for n in ns):
            raise ValueError("particle_counts must be a nonempty list of integers >= 2")
        if ns != sorted(set(ns)):
            raise ValueError("particle_counts must be sorted and distinct")
        for key in ("jump_strength", "gradient_threshold", "wait_time", "decrease_threshold",
                    "end_time", "dt", "check_interval"):
            value = getattr(self, key)
            if type(value) not in (int, float) or not math.isfinite(value) or value <= 0:
                raise ValueError(key + " must be finite and positive")
        for value, unit in ((self.check_interval, self.dt), (self.wait_time, self.check_interval),
                            (self.end_time, self.check_interval)):
            if not math.isclose(value / unit, round(value / unit), rel_tol=0, abs_tol=1e-9):
                raise ValueError("time intervals must be integer multiples of their grid units")
        if self.wait_time >= self.end_time:
            raise ValueError("wait_time must precede end_time")

    @property
    def ticks(self):
        return round(self.end_time / self.check_interval)

    @property
    def wait_ticks(self):
        return round(self.wait_time / self.check_interval)

    @property
    def substeps(self):
        return round(self.check_interval / self.dt)


class Controller:
    """A decrease test takes precedence; successful tests resume on the next tick.

    Attempt numbers include the final unsuccessful test. A returned candidate
    is a separate output; the executed trajectory is never rewound.
    """

    def __init__(self, config):
        self.config = config
        self.pending = None
        self.attempts = 0
        self.stopped = False
        self.last_tick = -1

    def decide(self, tick, loss, gradient_rms):
        if tick != self.last_tick + 1:
            raise ValueError("controller must be visited on successive check ticks")
        if not math.isfinite(loss) or not math.isfinite(gradient_rms) or gradient_rms < 0:
            raise FloatingPointError("nonfinite diagnostics or negative gradient norm")
        self.last_tick = tick
        if self.stopped:
            return {"action": "inactive"}
        if self.pending is not None:
            due, candidate_loss = self.pending
            if tick < due:
                return {"action": "wait"}
            if tick != due:
                raise AssertionError("missed decrease-test tick")
            decrease = candidate_loss - loss
            self.pending = None
            self.stopped = decrease <= self.config.decrease_threshold
            return {"action": "stop" if self.stopped else "resume", "decrease": decrease}
        # The finite observation ends at T; do not start a jump exactly at T.
        if tick < self.config.ticks and gradient_rms <= self.config.gradient_threshold:
            self.attempts += 1
            self.pending = (tick + self.config.wait_ticks, loss)
            return {"action": "jump", "attempt": self.attempts}
        return {"action": "flow"}


def diagnostics(model, state):
    if not np.all(np.isfinite(state)):
        raise FloatingPointError("nonfinite particle state")
    features = np.tanh(state)
    mean = features.mean(axis=0)
    velocity = -(1 - features * features) * model.gradient(mean)
    loss = model.objective(mean)
    return {"objective": loss,
            "gradient_rms": float(np.sqrt(np.mean(np.sum(velocity * velocity, axis=(1, 2))))),
            "target_relative_error": float(2 * np.sqrt(loss) / np.linalg.norm(model.target))}


def advance(model, state, config):
    for _ in range(config.substeps):
        state = rk4_step(model, state, config.dt)
    return state


def normal_stream(config, trial, kind, n=None):
    words = [config.trial_seed, trial, kind]
    if n is not None:
        words.append(n)
    return np.random.default_rng(np.random.SeedSequence(words))


def population_path(config, trial, normal_overrides=None):
    """Keep only event states and the output: O(number of events * Kq) storage."""
    model = MatrixModel(target_matrix(config.d))
    state = initial_population(config.population_size, config.d, config.population_seed)
    rng, controller = normal_stream(config, trial, 1), Controller(config)
    events, rows, candidate, returned, stop_tick = [], [], None, None, None
    for tick in range(config.ticks + 1):
        if tick:
            state = advance(model, state, config)
        info = diagnostics(model, state)
        decision = controller.decide(tick, info["objective"], info["gradient_rms"])
        action = decision["action"]
        rows.append({"time": tick * config.check_interval, "tick": tick,
                     "phase": "pre_jump" if action == "jump" else action, **info})
        if action == "jump":
            j = controller.attempts
            z = rng.normal(size=model.q)
            if normal_overrides and j in normal_overrides:
                z = np.asarray(normal_overrides[j], dtype=float).copy()
                if z.shape != (model.q,) or not np.all(np.isfinite(z)):
                    raise ValueError("normal override has invalid shape or values")
            candidate = state.copy()
            field, lp, sp = population_field(model, state, z)
            state = state + config.jump_strength * field
            events.append({"attempt": j, "tick": tick, "time": tick * config.check_interval,
                           "pre": candidate.copy(), "post": state.copy(), "lp": lp,
                           "sp": sp, "normal": z, "pre_diagnostics": info})
            rows.append({"time": tick * config.check_interval, "tick": tick,
                         "phase": "post_jump", **diagnostics(model, state)})
        elif action in ("stop", "resume"):
            events[-1]["evaluation"] = {"time": tick * config.check_interval,
                "decrease": decision["decrease"], "accepted": action == "resume", **info}
            if action == "stop":
                returned, stop_tick = candidate.copy(), tick
                break
    return {"events": events, "rows": rows, "actual": state, "returned": returned,
            "stop_tick": stop_tick, "status": "stopped" if returned is not None else "horizon"}


def simulate(config, trial, normal_overrides=None, progress=None):
    if type(trial) is not int or trial < 0:
        raise ValueError("trial must be a nonnegative integer")
    started = time.monotonic()
    model = MatrixModel(target_matrix(config.d))
    initial = initial_population(config.population_size, config.d, config.population_seed)
    population = population_path(config, trial, normal_overrides)
    if progress:
        progress({"stage": "population_complete", "trial": trial,
                  "status": population["status"], "attempts": len(population["events"]),
                  "stop_time": None if population["stop_tick"] is None else
                  population["stop_tick"] * config.check_interval})
    indices = normal_stream(config, trial, 0).integers(0, len(initial), size=max(config.particle_counts))
    xs = {n: initial[indices[:n]].copy() for n in config.particle_counts}
    controls = {n: Controller(config) for n in xs}
    auxiliary = {n: normal_stream(config, trial, 2, n) for n in xs}
    fallback = {n: normal_stream(config, trial, 3, n) for n in xs}
    candidates, returned, stopped, empirical_events = {}, {}, {}, {n: [] for n in xs}
    pstate = initial.copy()
    pevents = {e["tick"]: e for e in population["events"]}
    pend = population["stop_tick"] if population["stop_tick"] is not None else config.ticks
    rows, snapshots = [], {"indices": indices, "population_actual": population["actual"]}
    if population["returned"] is not None:
        snapshots["population_returned"] = population["returned"]
    for e in population["events"]:
        for phase in ("pre", "post"):
            snapshots[f"population_attempt_{e['attempt']:03d}_{phase}"] = e[phase]

    def record(tick, phase, active):
        pinfo = diagnostics(model, pstate) if tick <= pend else None
        ap = np.tanh(pstate).mean(axis=0) if pinfo is not None else None
        for n in active:
            x = xs[n]
            info = diagnostics(model, x)
            rms = spike = threshold = gap = matrix_error = None
            if pinfo is not None:
                y = pstate[indices[:n]]
                rms, spike, threshold = discrepancy_metrics(x, y)
                gap = abs(info["objective"] - pinfo["objective"])
                ax = np.tanh(x).mean(axis=0)
                matrix_error = float(np.linalg.norm(ax @ ax.T - ap @ ap.T))
            rows.append({"trial": trial, "n": n, "time": tick * config.check_interval,
                "tick": tick, "phase": phase, "tracking_rms": rms, "spikiness": spike,
                "spikiness_rms_threshold": threshold, "objective_gap": gap,
                "matrix_error": matrix_error, "empirical_objective": info["objective"],
                "empirical_gradient_rms": info["gradient_rms"],
                "empirical_target_relative_error": info["target_relative_error"],
                "population_objective": None if pinfo is None else pinfo["objective"],
                "population_gradient_rms": None if pinfo is None else pinfo["gradient_rms"]})

    for tick in range(config.ticks + 1):
        active = [n for n in xs if n not in stopped]
        if not active:
            break
        if tick:
            if tick <= pend:
                pstate = advance(model, pstate, config)
            for n in active:
                xs[n] = advance(model, xs[n], config)
        decisions = {}
        for n in active:
            info = diagnostics(model, xs[n])
            decisions[n] = (controls[n].decide(tick, info["objective"], info["gradient_rms"]), info)
        jumping = [n for n in active if decisions[n][0]["action"] == "jump"]
        pjump = pevents.get(tick)
        record(tick, "pre_jump" if jumping or pjump is not None else "flow", active)
        if pjump is not None:
            if not np.array_equal(pstate, pjump["pre"]):
                raise AssertionError("population replay differs from independent first pass")
            field, _, _ = population_field(model, pstate, pjump["normal"])
            pstate = pstate + config.jump_strength * field
            if not np.array_equal(pstate, pjump["post"]):
                raise AssertionError("population post-jump replay differs")
        for n in active:
            decision, info = decisions[n]
            action = decision["action"]
            if action == "jump":
                j = controls[n].attempts
                candidates[n] = xs[n].copy()
                z_aux = auxiliary[n].normal(size=model.q)
                if j <= len(population["events"]):
                    pe = population["events"][j - 1]
                    field, coupling_info = empirical_field(model, xs[n], pe["pre"][indices[:n]],
                        pe["lp"], pe["sp"], pe["normal"], z_aux)
                    mode = "matched_attempt"
                else:
                    field, _, _ = population_field(model, xs[n], fallback[n].normal(size=model.q))
                    coupling_info, mode = {}, "independent_unmatched"
                snapshots[f"x_{n}_attempt_{j:03d}_pre"] = xs[n].copy()
                xs[n] = xs[n] + config.jump_strength * field
                snapshots[f"x_{n}_attempt_{j:03d}_post"] = xs[n].copy()
                empirical_events[n].append({"attempt": j, "tick": tick,
                    "time": tick * config.check_interval, "coupling": mode,
                    "pre_diagnostics": info, "coupling_diagnostics": coupling_info})
            elif action in ("stop", "resume"):
                empirical_events[n][-1]["evaluation"] = {
                    "time": tick * config.check_interval, "decrease": decision["decrease"],
                    "accepted": action == "resume", **info}
                if action == "stop":
                    stopped[n] = tick
                    returned[n] = candidates[n].copy()
                    if progress:
                        progress({"stage": "empirical_stop", "trial": trial, "n": n,
                            "time": tick * config.check_interval, "attempts": controls[n].attempts})
        # Simultaneous jumps are recorded as one before/after pair, without an
        # artificial intermediate state in which only one system was updated.
        if jumping or pjump is not None:
            record(tick, "post_jump", active)
        if tick == pend and not np.array_equal(pstate, population["actual"]):
            raise AssertionError("population terminal replay differs")

    outputs = []
    for n in xs:
        snapshots[f"x_{n}_actual"] = xs[n]
        output = {"n": n, "status": "stopped" if n in stopped else "horizon",
                  "stop_time": stopped[n] * config.check_interval if n in stopped else None,
                  "attempts": len(empirical_events[n]), "actual": diagnostics(model, xs[n])}
        if n in returned:
            snapshots[f"x_{n}_returned"] = returned[n]
            output["returned"] = diagnostics(model, returned[n])
            output["candidate_time"] = empirical_events[n][-1]["time"]
            if population["returned"] is not None:
                y = population["returned"][indices[:n]]
                rms, spike, threshold = discrepancy_metrics(returned[n], y)
                pinfo = diagnostics(model, population["returned"])
                output["return_tracking_rms"] = rms
                output["return_spikiness"] = spike
                output["return_objective_gap"] = abs(output["returned"]["objective"] - pinfo["objective"])
        outputs.append(output)
    pevent_info = [{key: value for key, value in e.items()
                   if key not in ("pre", "post", "lp", "sp", "normal")} for e in population["events"]]
    summary = {"trial": trial, "seconds": time.monotonic() - started,
        "population_sha256": hashlib.sha256(initial.tobytes()).hexdigest(),
        "population": {"status": population["status"],
            "stop_time": None if population["stop_tick"] is None else pend * config.check_interval,
            "attempts": len(pevent_info), "actual": diagnostics(model, population["actual"]),
            "returned": None if population["returned"] is None else diagnostics(model, population["returned"])},
        "outputs": outputs, "population_replay_exact": True}
    return rows, population["rows"], {"population": pevent_info, "empirical": empirical_events}, snapshots, summary


def source_hashes():
    root = Path(__file__).resolve().parent
    names = ("model.py", "coupling.py", "adaptive.py", "adaptive_config.json",
             "test_adaptive.py", "run_adaptive_protocol.py")
    return {name: hashlib.sha256((root / name).read_bytes()).hexdigest() for name in names}


def write_json(path, value):
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, allow_nan=False) + "\n")
    os.replace(temporary, path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", type=Path, default=Path(__file__).with_name("adaptive_config.json"))
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--trial", type=int, required=True)
    args = parser.parse_args()
    if args.trial < 0:
        parser.error("trial must be nonnegative")
    config = Config(**json.loads(args.config.read_text()))
    args.out.mkdir(parents=True, exist_ok=False)
    metadata = {"config": config.__dict__, "trial": args.trial, "status": "running",
        "python": sys.version, "numpy": np.__version__, "platform": platform.platform(),
        "source_sha256": source_hashes(),
        "config_sha256": hashlib.sha256(args.config.read_bytes()).hexdigest(),
        "thread_environment": {k: os.environ.get(k) for k in
            ("OPENBLAS_NUM_THREADS", "OMP_NUM_THREADS", "MKL_NUM_THREADS")}}
    path = args.out / "metadata.json"
    write_json(path, metadata)
    try:
        rows, prows, events, states, summary = simulate(config, args.trial,
            progress=lambda record: print(json.dumps(record, allow_nan=False), flush=True))
        for name, data in (("trajectory.csv", rows), ("population.csv", prows)):
            with (args.out / name).open("x", newline="") as handle:
                writer = csv.DictWriter(handle, fieldnames=list(data[0]))
                writer.writeheader()
                writer.writerows(data)
        write_json(args.out / "events.json", events)
        write_json(args.out / "summary.json", summary)
        np.savez_compressed(args.out / "states.npz", **states)
        metadata.update(status="complete", summary=summary)
        print(json.dumps({"stage": "complete", "trial": args.trial,
                          "seconds": summary["seconds"]}), flush=True)
    except Exception as error:
        metadata.update(status="failed", error=repr(error))
        raise
    finally:
        write_json(path, metadata)


if __name__ == "__main__":
    main()
