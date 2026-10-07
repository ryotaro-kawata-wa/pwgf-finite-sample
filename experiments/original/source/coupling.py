"""Population-first coupling in q dimensions, equivalent in observable joint law.

The full-SVD orthogonal completion avoids inverses of small singular values.
See README.md for the reduction from C^(1/2) sign_+(M_Y).
"""

import numpy as np

from model import statistics


def sign_plus(matrix):
    values, vectors = np.linalg.eigh((matrix + matrix.T) / 2.0)
    signs = np.where(values < 0.0, -1.0, 1.0)
    return (vectors * signs) @ vectors.T, values


def population_field(model, population, normal):
    a, jac, sigma = statistics(population)
    hessian = model.hessian(a)
    coefficient = hessian @ (np.sqrt(sigma) * normal)
    return (jac * coefficient).reshape(population.shape), hessian, sigma


def reduced_factors(model, x, y, population_hessian, population_sigma):
    """Linear coefficients e = e_population @ z0 + e_auxiliary @ z2."""
    ax, jx, sx = statistics(x)
    ay, jy, sy = statistics(y)
    if np.any(sy <= 0) or not np.all(np.isfinite(sy)):
        raise FloatingPointError("reference Jacobian saturated; no jitter is added")
    t = np.sqrt(sy)
    cross = np.mean(jx * jy, axis=0)
    k = cross / t
    # Cauchy--Schwarz remainder evaluated without cancellation.
    v = np.mean((jx - (cross / sy) * jy) ** 2, axis=0)
    ly = model.hessian(ay)  # Reference EMPIRICAL mean, not population mean.
    lx = model.hessian(ax)
    m = t[:, None] * ly * t[None, :]
    q, eigenvalues = sign_plus(m)
    f = t[:, None] * population_hessian * np.sqrt(population_sigma)[None, :]
    u, singular_values, vt = np.linalg.svd(f, full_matrices=True)
    rotation = u @ vt
    e_population = k[:, None] * (q @ rotation)
    e_auxiliary = np.diag(np.sqrt(v))
    sigma_error = ((e_population @ e_population.T + e_auxiliary @ e_auxiliary.T)
                   - np.diag(sx))
    residual = (t[:, None] * population_hessian
                @ np.diag(population_sigma - sy)
                @ population_hessian * t[None, :])
    diagnostics = {
        "covariance_residual": float(np.abs(np.linalg.eigvalsh(residual)).sum()),
        "reduced_covariance_relative_error": float(
            np.linalg.norm(sigma_error) / max(np.linalg.norm(sx), 1e-300)),
        "polar_relative_error": float(np.linalg.norm(f - ((u * singular_values) @ u.T) @ rotation)
                                      / max(np.linalg.norm(f), 1e-300)),
        "reference_hessian_min_eigenvalue": float(eigenvalues[0]),
        "reference_hessian_max_eigenvalue": float(eigenvalues[-1]),
        "population_factor_singular_values": singular_values.tolist(),
        "minimum_reference_jacobian_second_moment": float(sy.min()),
    }
    return jx, lx, e_population, e_auxiliary, diagnostics


def empirical_field(model, x, y, population_hessian, population_sigma,
                    population_normal, auxiliary_normal):
    jx, lx, ep, ea, diagnostics = reduced_factors(
        model, x, y, population_hessian, population_sigma)
    e = ep @ population_normal + ea @ auxiliary_normal
    field = (jx * (lx @ e)).reshape(x.shape)
    return field, diagnostics
