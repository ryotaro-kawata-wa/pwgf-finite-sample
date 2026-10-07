import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

/-! # Actual exponential-square moments of a standard real Gaussian

The moment is computed from the Gaussian density and the Gaussian integral.
Integrability follows from the proved nonzero integral; no target moment or
concentration inequality is assumed.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace PaperFormalization.Manuscript

/-- The exponential-square integral under the actual standard Gaussian law. -/
theorem integral_exp_sq_standardGaussian (t : ℝ) (ht : t < 1 / 2) :
    (∫ x : ℝ, Real.exp (t * x ^ 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 - 2 * t))⁻¹ := by
  have hb : 0 < 1 / 2 - t := by linarith
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  have hfun : (fun x : ℝ => gaussianPDFReal 0 1 x • Real.exp (t * x ^ 2)) =
      (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - t) * x ^ 2)) := by
    funext x
    simp only [smul_eq_mul, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hfun, integral_const_mul, integral_gaussian]
  calc
    _ = Real.sqrt ((2 * Real.pi)⁻¹ * (Real.pi / (1 / 2 - t))) := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ (2 * Real.pi)⁻¹), Real.sqrt_inv]
    _ = Real.sqrt ((1 - 2 * t)⁻¹) := by
      congr 1
      field_simp
    _ = _ := Real.sqrt_inv _

/-- The computed positive finite moment entails genuine Bochner integrability. -/
theorem integrable_exp_sq_standardGaussian (t : ℝ) (ht : t < 1 / 2) :
    Integrable (fun x : ℝ => Real.exp (t * x ^ 2)) (gaussianReal 0 1) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_exp_sq_standardGaussian t ht]
  exact (inv_pos.mpr (Real.sqrt_pos.2 (by linarith))).ne'

/-- A random variable with the actual standard Gaussian pushforward law has
the same finite exponential-square moment, under the original measure. -/
theorem exp_sq_moment_of_standardGaussian_law
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ)
    (hX : μ.map X = gaussianReal 0 1) (t : ℝ) (ht : t < 1 / 2) :
    Integrable (fun ω => Real.exp (t * (X ω) ^ 2)) μ ∧
      (∫ ω, Real.exp (t * (X ω) ^ 2) ∂μ) = (Real.sqrt (1 - 2 * t))⁻¹ := by
  have hXm : AEMeasurable X μ := aemeasurable_of_map_neZero (by rw [hX]; infer_instance)
  have hmoment : (∫ ω, Real.exp (t * (X ω) ^ 2) ∂μ) = (Real.sqrt (1 - 2 * t))⁻¹ := by
    rw [← integral_map (f := fun x : ℝ => Real.exp (t * x ^ 2)) hXm (by fun_prop), hX]
    exact integral_exp_sq_standardGaussian t ht
  have hden : 0 < 1 - 2 * t := by linarith
  exact ⟨Integrable.of_integral_ne_zero (by rw [hmoment]; positivity), hmoment⟩

end PaperFormalization.Manuscript
