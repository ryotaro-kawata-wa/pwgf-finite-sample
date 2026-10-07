"""Finite-feature PSD matrix factorization; all particle arrays have shape (n,d,2)."""

from dataclasses import dataclass

import numpy as np


@dataclass(frozen=True)
class MatrixModel:
    target: np.ndarray
    rank: int = 2

    def __post_init__(self):
        m = np.asarray(self.target, dtype=np.float64)
        if m.ndim != 2 or m.shape[0] != m.shape[1] or not np.all(np.isfinite(m)):
            raise ValueError("target must be a finite square matrix")
        if not np.allclose(m, m.T, atol=1e-14, rtol=1e-14) or self.rank < 1:
            raise ValueError("target must be symmetric and rank must be positive")
        object.__setattr__(self, "target", m.copy())

    @property
    def shape(self):
        return self.target.shape[0], self.rank

    @property
    def q(self):
        return self.target.shape[0] * self.rank

    def objective(self, a):
        residual = a @ a.T - self.target
        return float(np.sum(residual * residual) / 4.0)

    def gradient(self, a):
        return (a @ a.T - self.target) @ a

    def hessian_action(self, a, b):
        return ((a @ a.T - self.target) @ b
                + b @ (a.T @ a) + a @ (b.T @ a))

    def hessian(self, a):
        basis = np.eye(self.q).reshape(self.q, *self.shape)
        h = np.column_stack([self.hessian_action(a, b).ravel() for b in basis])
        return (h + h.T) / 2.0

    def drift(self, particles):
        features = np.tanh(particles)
        a = features.mean(axis=0)
        # This equals -n * grad_{particle_i} F(empirical law).
        return -(1.0 - features * features) * self.gradient(a)


def statistics(particles):
    """Return mean feature, flattened diagonal Jacobians, and E[J^2]."""
    features = np.tanh(particles)
    jac = (1.0 - features * features).reshape(len(particles), -1)
    return features.mean(axis=0), jac, np.mean(jac * jac, axis=0)


def target_matrix(d):
    """Dense orthogonal columns, eigenvalues 1 and 1/2, feasible tanh means."""
    if d < 2 or d % 2:
        raise ValueError("d must be positive, even, and at least 2")
    u = np.ones((d, 2), dtype=np.float64) / np.sqrt(d)
    u[1::2, 1] *= -1.0
    factor = u * np.sqrt([1.0, 0.5])
    if np.max(np.abs(factor)) >= 1:
        raise ValueError("target factor is outside the attainable tanh range")
    return factor @ factor.T


def initial_population(k, d, seed):
    if k < 2 or k % 2:
        raise ValueError("population support size must be positive and even")
    atoms = np.random.default_rng(seed).normal(size=(k // 2, d, 2))
    return np.concatenate((atoms, -atoms), axis=0)


def rk4_step(model, particles, dt):
    k1 = model.drift(particles)
    k2 = model.drift(particles + (dt / 2) * k1)
    k3 = model.drift(particles + (dt / 2) * k2)
    k4 = model.drift(particles + dt * k3)
    return particles + (dt / 6) * (k1 + 2 * k2 + 2 * k3 + k4)


def discrepancy_metrics(x, y):
    """Spikiness measures the paired error, not the spread of particle positions."""
    delta = (x - y).reshape(len(x), -1)
    norms = np.sqrt(np.einsum("ij,ij->i", delta, delta))
    rms = float(np.sqrt(np.mean(norms * norms)))
    scale = max(1.0, float(np.sqrt(np.mean(np.sum(y * y, axis=(1, 2))))))
    threshold = 1e-12 * scale
    spikiness = float(np.mean((norms / rms) ** 3)) if rms > threshold else None
    return rms, spikiness, threshold
