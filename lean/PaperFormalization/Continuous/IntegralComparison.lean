import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Tactic.Linarith

/-! # Integrating an almost-everywhere differential upper bound

This is the FTC step used after multiplication by the integrating factor.
The trajectory is absolutely continuous; continuous differentiability is not assumed.
-/

open MeasureTheory Set Filter

namespace PaperFormalization.Continuous

/-- An almost-everywhere derivative upper bound controls the endpoint increment. -/
theorem endpoint_le_of_ae_deriv_le (r f : ℝ → ℝ) (s t : ℝ)
    (hst : s ≤ t) (hr : AbsolutelyContinuousOnInterval r s t)
    (hf : IntervalIntegrable f volume s t)
    (hderiv : ∀ᵐ u ∂volume.restrict (Icc s t), deriv r u ≤ f u) :
    r t ≤ r s + ∫ u in s..t, f u := by
  have hint := intervalIntegral.integral_mono_ae_restrict hst
    hr.intervalIntegrable_deriv hf hderiv
  rw [hr.integral_deriv_eq_sub] at hint
  linarith

end PaperFormalization.Continuous
