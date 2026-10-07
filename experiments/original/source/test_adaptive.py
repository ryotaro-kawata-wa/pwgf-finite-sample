"""Tests of the adaptive protocol's law, control flow, and information flow."""

from dataclasses import replace
import unittest

import numpy as np

from adaptive import Config, Controller, simulate, diagnostics
from coupling import population_field, reduced_factors
from model import MatrixModel, initial_population, target_matrix, statistics


def small_config(**changes):
    config = Config(d=4, population_size=32, particle_counts=[12, 24], population_seed=27,
        trial_seed=81073, jump_strength=.2, gradient_threshold=10., wait_time=.2,
        decrease_threshold=1e-5, end_time=1., dt=.05, check_interval=.1)
    return replace(config, **changes)


class AdaptiveTests(unittest.TestCase):
    def test_controller_returns_prejump_candidate_and_waits(self):
        c = Controller(small_config(decrease_threshold=.01))
        self.assertEqual(c.decide(0, 1., 0.)["action"], "jump")
        self.assertEqual(c.decide(1, .5, 0.)["action"], "wait")
        self.assertEqual(c.decide(2, .5, 0.)["action"], "resume")
        # Strict cooldown: the successful test itself does not start a jump.
        self.assertEqual(c.attempts, 1)
        self.assertEqual(c.decide(3, .5, 0.)["action"], "jump")
        self.assertEqual(c.decide(4, .51, 0.)["action"], "wait")
        result = c.decide(5, .51, 0.)
        self.assertEqual(result["action"], "stop")
        self.assertAlmostEqual(result["decrease"], -.01)
        self.assertEqual(c.attempts, 2)  # Retain the failed final attempt.

    def test_threshold_and_incomplete_horizon_are_not_success(self):
        cfg = small_config(gradient_threshold=.01)
        c = Controller(cfg)
        for tick in range(cfg.ticks):
            gradient = .01 if tick == cfg.ticks - 1 else .011
            self.assertEqual(c.decide(tick, .5, gradient)["action"],
                             "jump" if tick == cfg.ticks - 1 else "flow")
        self.assertEqual(c.decide(cfg.ticks, .5, 0.)["action"], "wait")
        self.assertFalse(c.stopped)

    def test_invalid_configuration_and_nonfinite_diagnostics(self):
        for changes in ({"dt": .03}, {"check_interval": 0}, {"particle_counts": [24, 12]},
                        {"jump_strength": float("nan")}, {"d": True}):
            with self.assertRaises((ValueError, TypeError)):
                small_config(**changes)
        with self.assertRaises(FloatingPointError):
            Controller(small_config()).decide(0, float("nan"), 0.)

    def test_asynchronous_frozen_covariance_and_unmatched_covariance(self):
        model = MatrixModel(target_matrix(4))
        p = initial_population(32, 4, 27)
        z = np.random.default_rng(8).normal(size=model.q)
        _, lp, sp = population_field(model, p, z)
        idx = np.array([0, 0, 1, 3, 8, 12, 16, 25])
        y = p[idx]
        x = y + np.random.default_rng(9).normal(scale=.3, size=y.shape)
        jx, lx, ep, ea, _ = reduced_factors(model, x, y, lp, sp)
        _, _, sx = statistics(x)
        bx = np.vstack([np.diag(j) @ lx for j in jx])
        expected = bx @ np.diag(sx) @ bx.T
        actual = bx @ (ep @ ep.T + ea @ ea.T) @ bx.T
        np.testing.assert_allclose(actual, expected, rtol=2e-12, atol=2e-12)
        # Independent fallback is the self-state kernel factor, with no Y.
        factor = np.column_stack([population_field(model, x, e)[0].ravel()
                                  for e in np.eye(model.q)])
        np.testing.assert_allclose(factor @ factor.T, expected, rtol=2e-12, atol=2e-12)

    def test_future_noise_does_not_change_current_trigger_or_prestate(self):
        cfg = small_config()
        base = simulate(cfg, 0)
        self.assertGreaterEqual(len(base[2]["population"]), 2)
        changed = simulate(cfg, 0, normal_overrides={2: np.full(cfg.d * 2, 7.)})
        for system in ("population", "x_12", "x_24"):
            name = system + "_attempt_002_pre"
            if name in base[3]:
                np.testing.assert_array_equal(base[3][name], changed[3][name])
        for n in cfg.particle_counts:
            original = base[2]["empirical"][n]
            altered = changed[2]["empirical"][n]
            if len(original) >= 2:
                self.assertEqual(original[1]["time"], altered[1]["time"])
        self.assertEqual(base[2]["population"][1]["time"], changed[2]["population"][1]["time"])

    def test_population_and_each_n_do_not_depend_on_other_n(self):
        cfg = small_config()
        both, alone = simulate(cfg, 1), simulate(replace(cfg, particle_counts=[12]), 1)
        for key in both[3]:
            if key.startswith("population") or key.startswith("x_12_"):
                np.testing.assert_array_equal(both[3][key], alone[3][key])
        a = [r for r in both[0] if r["n"] == 12]
        self.assertEqual(a, alone[0])

    def test_stopping_does_not_rewind_executed_path(self):
        cfg = small_config(decrease_threshold=1.)
        rows, prows, events, states, summary = simulate(cfg, 0)
        self.assertEqual(summary["population"]["status"], "stopped")
        self.assertEqual(summary["population"]["attempts"], 1)
        self.assertFalse(events["population"][0]["evaluation"]["accepted"])
        np.testing.assert_array_equal(states["population_returned"], states["population_attempt_001_pre"])
        self.assertGreater(np.linalg.norm(states["population_actual"] - states["population_returned"]), 0)
        self.assertEqual(prows[-1]["phase"], "stop")
        for n in cfg.particle_counts:
            np.testing.assert_array_equal(states[f"x_{n}_returned"], states[f"x_{n}_attempt_001_pre"])
        # Synchronous jumps produce exactly one before/after pair per N.
        for n in cfg.particle_counts:
            first = [r for r in rows if r["n"] == n and r["time"] == 0]
            self.assertEqual([r["phase"] for r in first], ["pre_jump", "post_jump"])


if __name__ == "__main__":
    unittest.main()
