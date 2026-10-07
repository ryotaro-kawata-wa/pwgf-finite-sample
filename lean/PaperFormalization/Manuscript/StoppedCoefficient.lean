import PaperFormalization.Continuous.Duhamel

/-! # The manuscript's stopped coefficient and quadratic drift reduction

These are adapters for beta = kappa - c * R - gamma. They prove the algebra
and integrability implication, but do not assert that kappa and gamma from
the particle model have already been identified with these inputs.
-/

open MeasureTheory Set

namespace PaperFormalization.Manuscript

open Continuous

/-- The coefficient after bounding the quadratic drift inside radius `R`. -/
noncomputable def stoppedCoefficient (kappa gamma : ℝ → ℝ) (c R u : ℝ) : ℝ :=
  kappa u - c * R - gamma u

/-- Coefficient integrability follows from curvature and residual integrability. -/
theorem stoppedCoefficient_intervalIntegrable (kappa gamma : ℝ → ℝ) (c R s t : ℝ)
    (hkappa : IntervalIntegrable kappa volume s t)
    (hgamma : IntervalIntegrable gamma volume s t) :
    IntervalIntegrable (stoppedCoefficient kappa gamma c R) volume s t := by
  have hconst : IntervalIntegrable (fun _ : ℝ => c * R) volume s t := intervalIntegrable_const
  exact (hkappa.sub hconst).sub hgamma

/-- Factor the stopped propagator into the curvature propagator and explicit residual growth. -/
theorem propagator_stoppedCoefficient (kappa gamma : ℝ → ℝ) (c R s t : ℝ)
    (hkappa : IntervalIntegrable kappa volume s t)
    (hgamma : IntervalIntegrable gamma volume s t) :
    propagator (stoppedCoefficient kappa gamma c R) t s =
      propagator kappa t s * Real.exp (c * R * (t - s) + ∫ u in s..t, gamma u) := by
  have hconst : IntervalIntegrable (fun _ : ℝ => c * R) volume s t := intervalIntegrable_const
  unfold propagator stoppedCoefficient
  rw [intervalIntegral.integral_sub (hkappa.sub hconst) hgamma,
    intervalIntegral.integral_sub hkappa hconst, intervalIntegral.integral_const,
    ← Real.exp_add]
  congr 1
  simp only [smul_eq_mul]
  ring

/-- For nonnegative discrepancy and quadratic coefficient, x <= R bounds the quadratic drift. -/
theorem quadratic_le_stopped_linear (x kappa gamma c R : ℝ)
    (hx : 0 ≤ x) (hc : 0 ≤ c) (hxR : x ≤ R) :
    -kappa * x + c * x ^ 2 + gamma * x + gamma ≤
      -(kappa - c * R - gamma) * x + gamma := by
  have hquad := mul_le_mul_of_nonneg_left hxR (mul_nonneg hc hx)
  nlinarith only [hquad]

/-- Apply the pointwise reduction to an a.e. branch differential inequality. -/
theorem ae_deriv_le_stoppedCoefficient (r kappa gamma : ℝ → ℝ) (c R s t : ℝ)
    (hc : 0 ≤ c)
    (hr : ∀ᵐ u ∂volume.restrict (Ioo s t), 0 ≤ r u)
    (hR : ∀ᵐ u ∂volume.restrict (Ioo s t), r u ≤ R)
    (hineq : ∀ᵐ u ∂volume.restrict (Ioo s t),
      deriv r u ≤ -kappa u * r u + c * (r u) ^ 2 + gamma u * r u + gamma u) :
    ∀ᵐ u ∂volume.restrict (Ioo s t),
      deriv r u ≤ -stoppedCoefficient kappa gamma c R u * r u + gamma u := by
  filter_upwards [hr, hR, hineq] with u hru hRu hineq_u
  exact le_trans hineq_u (quadratic_le_stopped_linear (r u) (kappa u) (gamma u) c R hru hc hRu)

end PaperFormalization.Manuscript
