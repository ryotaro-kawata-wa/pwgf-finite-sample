import PaperFormalization.Manuscript.GrowthSummability
import Mathlib.Analysis.MeanInequalities

/-! # Uniform scalar bounds for the manuscript feature envelope

All constants in this module are chosen before the variable scale is supplied.
The conjugate exponent is exactly the manuscript's decay exponent divided by
that exponent minus one. No bound on a feature series is assumed here.
-/

open Filter Asymptotics
open scoped Topology

namespace PaperFormalization.Manuscript

/-- The coefficient in a scaled form of Young's inequality. -/
noncomputable def featureYoungCoefficient (c p : ℝ) : ℝ :=
  (((p * c) ^ p⁻¹)⁻¹) ^ (p / (p - 1)) / (p / (p - 1))

/-- The scale-independent Young coefficient is positive. -/
theorem featureYoungCoefficient_pos (c p : ℝ) (hc : 0 < c) (hp : 1 < p) :
    0 < featureYoungCoefficient c p := by
  unfold featureYoungCoefficient
  have hp0 : 0 < p := by linarith
  have hq : 0 < p / (p - 1) := div_pos hp0 (by linarith)
  exact div_pos (Real.rpow_pos_of_pos (inv_pos.mpr
    (Real.rpow_pos_of_pos (mul_pos hp0 hc) _)) _) hq

/-- Weighted Young inequality with an explicit coefficient independent of `x,b`. -/
theorem feature_weighted_young (c p x b : ℝ)
    (hc : 0 < c) (hp : 1 < p) (hx : 0 ≤ x) (hb : 0 ≤ b) :
    x * b ≤ c * x ^ p + featureYoungCoefficient c p * b ^ (p / (p - 1)) := by
  let r : ℝ := (p * c) ^ p⁻¹
  have hp0 : 0 < p := by linarith
  have hr : 0 < r := Real.rpow_pos_of_pos (mul_pos hp0 hc) _
  have hrp : r ^ p = p * c := Real.rpow_inv_rpow (by positivity) hp0.ne'
  have h := Real.young_inequality_of_nonneg (mul_nonneg hr.le hx)
    (mul_nonneg (inv_nonneg.mpr hr.le) hb) (Real.HolderConjugate.conjExponent hp)
  change (r * x) * (r⁻¹ * b) ≤ (r * x) ^ p / p +
    (r⁻¹ * b) ^ (p / (p - 1)) / (p / (p - 1)) at h
  rw [Real.mul_rpow hr.le hx, hrp,
    Real.mul_rpow (inv_nonneg.mpr hr.le) hb] at h
  have hleft : (r * x) * (r⁻¹ * b) = x * b := by field_simp
  have hfirst : p * c * x ^ p / p = c * x ^ p := by field_simp
  rw [hleft, hfirst] at h
  simpa only [featureYoungCoefficient, r, div_mul_eq_mul_div] using h

/-- Legendre-type bound used on the logarithm of a weighted summand. -/
theorem feature_linear_sub_rpow_le (c p x b : ℝ)
    (hc : 0 < c) (hp : 1 < p) (hx : 0 ≤ x) (hb : 0 ≤ b) :
    x * b - c * x ^ p ≤ featureYoungCoefficient c p * b ^ (p / (p - 1)) := by
  linarith [feature_weighted_young c p x b hc hp hx hb]

end PaperFormalization.Manuscript
