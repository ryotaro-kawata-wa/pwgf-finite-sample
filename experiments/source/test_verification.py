"""Independent derivative, kernel-integral and full-matrix coupling checks."""

import unittest

import numpy as np

from coupling import population_field, reduced_factors, sign_plus
from model import MatrixModel, discrepancy_metrics, initial_population, statistics, target_matrix


def stack_jacobians(jac):
    return np.vstack([np.diag(row) for row in jac])


def psd_root(matrix):
    values, vectors = np.linalg.eigh((matrix + matrix.T) / 2)
    tolerance = 1e-12 * max(1.0, np.max(np.abs(values)))
    if values.min() < -tolerance:
        raise AssertionError("dense oracle covariance is not PSD")
    # Dense oracle only: discard floating-point eigenvalues on the known null space.
    values = np.where(values > tolerance, values, 0.0)
    return (vectors * np.sqrt(values)) @ vectors.T


class Verification(unittest.TestCase):
    def setUp(self):
        self.rng = np.random.default_rng(731)
        self.model = MatrixModel(target_matrix(4))

    def test_mean_gradient_and_hessian(self):
        a = self.rng.normal(scale=0.3, size=self.model.shape)
        eps = 1e-6
        gradient = np.empty(self.model.q)
        hessian = np.empty((self.model.q, self.model.q))
        for k, basis in enumerate(np.eye(self.model.q).reshape(self.model.q, *self.model.shape)):
            gradient[k] = (self.model.objective(a + eps * basis)
                           - self.model.objective(a - eps * basis)) / (2 * eps)
            hessian[:, k] = ((self.model.gradient(a + eps * basis)
                              - self.model.gradient(a - eps * basis)) / (2 * eps)).ravel()
        np.testing.assert_allclose(self.model.gradient(a).ravel(), gradient, atol=1e-9, rtol=1e-8)
        np.testing.assert_allclose(self.model.hessian(a), hessian, atol=1e-9, rtol=1e-8)

    def test_particle_gradient_normalization_and_full_hessian(self):
        x = self.rng.normal(size=(3, *self.model.shape))
        a, jac, _ = statistics(x)
        d = stack_jacobians(jac)
        spatial = (-2 * np.tanh(x) * (1 - np.tanh(x) ** 2)
                   * self.model.gradient(a)).ravel()
        expected_full = d @ self.model.hessian(a) @ d.T / len(x) + np.diag(spatial)
        eps = 1e-6
        gradient = np.empty(x.size)
        full = np.empty((x.size, x.size))
        for k in range(x.size):
            perturbation = np.zeros_like(x)
            perturbation.ravel()[k] = eps
            plus, minus = x + perturbation, x - perturbation
            gradient[k] = (self.model.objective(np.tanh(plus).mean(axis=0))
                           - self.model.objective(np.tanh(minus).mean(axis=0))) / (2 * eps)
            full[:, k] = (-(self.model.drift(plus) - self.model.drift(minus)) / (2 * eps)).ravel()
        np.testing.assert_allclose(-self.model.drift(x).ravel(), len(x) * gradient, atol=1e-9, rtol=1e-7)
        np.testing.assert_allclose(expected_full, full, atol=1e-9, rtol=1e-7)

    def test_population_covariance_against_direct_kernel_integration(self):
        p = self.rng.normal(size=(7, *self.model.shape))
        a, j, sigma = statistics(p)
        lp = self.model.hessian(a)
        direct = np.zeros((2 * self.model.q, 2 * self.model.q))
        for jw in j:
            evaluated_kernel = np.vstack([np.diag(row) @ lp @ np.diag(jw) for row in j[:2]])
            direct += evaluated_kernel @ evaluated_kernel.T / len(j)
        factor = stack_jacobians(j[:2]) @ lp @ np.diag(np.sqrt(sigma))
        np.testing.assert_allclose(direct, factor @ factor.T, atol=2e-13, rtol=2e-12)

    def check_dense_coupling(self, symmetric):
        p = self.rng.normal(size=(7, *self.model.shape))
        if symmetric:
            p = np.concatenate((p, -p))
        y = p[[0, 1, 4, 0]].copy()  # A duplicate atom is intentional.
        x = y + self.rng.normal(scale=0.08, size=y.shape)
        ap, jp, sp = statistics(p)
        ay, jy, _ = statistics(y)
        ax, jx, sx = statistics(x)
        lp, ly, lx = [self.model.hessian(a) for a in (ap, ay, ax)]
        dp, dy, dx = [stack_jacobians(j) for j in (jp, jy, jx)]
        n = len(x)
        my = dy @ ly @ dy.T / np.sqrt(n)
        mx = dx @ lx @ dx.T / np.sqrt(n)
        population_factor = dp @ lp @ np.diag(np.sqrt(sp))
        evaluation_factor = dy @ lp @ np.diag(np.sqrt(sp))
        c = evaluation_factor @ evaluation_factor.T
        q_dense, _ = sign_plus(my)
        b = psd_root(c) @ q_dense
        inverse = np.linalg.pinv(b, rcond=1e-10)
        dense_population = mx @ inverse @ evaluation_factor
        dense_auxiliary = mx @ (np.eye(n * self.model.q) - inverse @ b)
        _, _, ep, ea, diagnostics = reduced_factors(self.model, x, y, lp, sp)
        reduced_population, reduced_auxiliary = dx @ lx @ ep, dx @ lx @ ea
        expected = dx @ lx @ np.diag(sx) @ lx @ dx.T
        np.testing.assert_allclose(reduced_population @ reduced_population.T
                                   + reduced_auxiliary @ reduced_auxiliary.T,
                                   expected, atol=2e-10, rtol=2e-9)
        np.testing.assert_allclose(dense_population @ dense_population.T
                                   + dense_auxiliary @ dense_auxiliary.T,
                                   expected, atol=2e-9, rtol=2e-8)
        # Equality of the joint Gaussian law with the ENTIRE population field.
        np.testing.assert_allclose(reduced_population @ population_factor.T,
                                   dense_population @ population_factor.T,
                                   atol=2e-9, rtol=2e-8)
        self.assertLess(diagnostics["reduced_covariance_relative_error"], 1e-12)
        self.assertGreater(diagnostics["covariance_residual"], 1e-6)

    def test_dense_coupling_full_rank(self):
        self.check_dense_coupling(False)

    def test_dense_coupling_singular_population_covariance(self):
        self.check_dense_coupling(True)

    def test_spikiness_boundary_cases(self):
        y = np.zeros((16, 4, 2))
        x = np.ones_like(y)
        self.assertAlmostEqual(discrepancy_metrics(x, y)[1], 1.0)
        x[1:] = 0
        self.assertAlmostEqual(discrepancy_metrics(x, y)[1], np.sqrt(len(x)))
        self.assertIsNone(discrepancy_metrics(y, y)[1])

    def test_symmetric_population_and_feasible_target(self):
        p = initial_population(100, 4, 83)
        self.assertLess(np.linalg.norm(np.tanh(p).mean(axis=0)), 1e-15)
        self.assertLess(np.linalg.norm(self.model.drift(p)), 1e-13)
        # Coordinatewise magnitudes vary: the sampled covariance is not constant.
        self.assertGreater(np.var(statistics(p)[1] ** 2, axis=0).min(), 0.01)


if __name__ == "__main__":
    unittest.main(verbosity=2)
