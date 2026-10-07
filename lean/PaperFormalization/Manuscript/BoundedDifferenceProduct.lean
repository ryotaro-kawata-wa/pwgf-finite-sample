import PaperFormalization.Manuscript.BoundedDifferenceHoeffding
import Mathlib.MeasureTheory.Integral.Prod

/-! # The product integration step for bounded differences

The probability law is the unchanged genuine product. The induction step
integrates one coordinate and adds its exact squared-width/4 parameter.
The two-factor corollary derives both parameters from literal replacement
bounds, without an assumed exponential-moment or concentration bound.
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace PaperFormalization.Manuscript

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Averaging an actual bounded measurable product function over one
probability factor preserves its literal oscillation in the other factor. -/
theorem integral_coordinate_oscillation_le
    (ν : Measure B) [IsProbabilityMeasure ν] (f : A × B → ℝ) (M c : ℝ≥0)
    (hf : Measurable f) (hbound : ∀ p, |f p| ≤ M)
    (hosc : ∀ x x' y, |f (x,y) - f (x',y)| ≤ c) (x x' : A) :
    |(∫ y, f (x,y) ∂ν) - ∫ y, f (x',y) ∂ν| ≤ c := by
  have hi (z : A) : Integrable (fun y => f (z,y)) ν :=
    Integrable.of_bound (hf.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      M (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hbound (z,y))
  rw [← integral_sub (hi x) (hi x')]
  have hb := norm_integral_le_of_norm_le_const (μ := ν)
    (Filter.Eventually.of_forall fun y =>
      show ‖f (x,y) - f (x',y)‖ ≤ (c : ℝ) by
        simpa only [Real.norm_eq_abs] using hosc x x' y)
  simpa using hb

/-- The induction step behind McDiarmid: the actual mean over the last
coordinate has parameter C, and literal last-coordinate oscillation c adds
exactly c²/4 to that parameter. -/
theorem hasSubgaussianMGF_centered_prod_step
    (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure B) [IsProbabilityMeasure ν]
    (f : A × B → ℝ) (M c C : ℝ≥0) (hf : Measurable f)
    (hbound : ∀ p, |f p| ≤ M)
    (hosc : ∀ x y y', |f (x,y) - f (x,y')| ≤ c)
    (hmean : HasSubgaussianMGF
      (fun x => (∫ y, f (x,y) ∂ν) - ∫ z, ∫ y, f (z,y) ∂ν ∂μ) C μ) :
    HasSubgaussianMGF (fun p => f p - ∫ q, f q ∂(μ.prod ν))
      (C + (c / 2) ^ 2) (μ.prod ν) := by
  let g : A → ℝ := fun x => ∫ y, f (x,y) ∂ν
  have hi : Integrable f (μ.prod ν) :=
    Integrable.of_bound hf.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hbound p)
  have htotal : (∫ p, f p ∂(μ.prod ν)) = ∫ x, g x ∂μ := integral_prod f hi
  have hwhole := hasSubgaussianMGF_of_mem_Icc (μ := μ.prod ν) hf.aemeasurable
    (show ∀ᵐ p ∂(μ.prod ν), f p ∈ Set.Icc (-(M : ℝ)) M from
      Filter.Eventually.of_forall fun p => abs_le.mp (hbound p))
  refine ⟨hwhole.integrable_exp_mul, ?_⟩
  intro t
  have hs (x : A) : HasSubgaussianMGF (fun y => f (x,y) - g x) ((c / 2) ^ 2) ν :=
    hasSubgaussianMGF_centered_of_oscillation ν (fun y => f (x,y)) c
      (hf.comp (measurable_const.prodMk measurable_id)).aemeasurable (hosc x)
  have hei : Integrable (fun p => exp (t * (f p - ∫ x, g x ∂μ))) (μ.prod ν) := by
    simpa only [htotal] using hwhole.integrable_exp_mul t
  have hinner (x : A) :
      (∫ y, exp (t * (f (x,y) - ∫ z, g z ∂μ)) ∂ν) ≤
        exp (t * (g x - ∫ z, g z ∂μ)) * exp (((c / 2) ^ 2 : ℝ≥0) * t ^ 2 / 2) := by
    calc
      _ = exp (t * (g x - ∫ z, g z ∂μ)) *
          ∫ y, exp (t * (f (x,y) - g x)) ∂ν := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by dsimp only; rw [← exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ((hs x).mgf_le t) (exp_pos _).le
  change (∫ p, exp (t * (f p - ∫ q, f q ∂(μ.prod ν))) ∂(μ.prod ν)) ≤ _
  rw [htotal, integral_prod _ hei]
  calc
    _ ≤ ∫ x, exp (t * (g x - ∫ z, g z ∂μ)) *
        exp (((c / 2) ^ 2 : ℝ≥0) * t ^ 2 / 2) ∂μ :=
      integral_mono hei.integral_prod_left
        ((hmean.integrable_exp_mul t).mul_const _) hinner
    _ = (∫ x, exp (t * (g x - ∫ z, g z ∂μ)) ∂μ) *
        exp (((c / 2) ^ 2 : ℝ≥0) * t ^ 2 / 2) := integral_mul_const _ _
    _ ≤ exp ((C : ℝ) * t ^ 2 / 2) * exp (((c / 2) ^ 2 : ℝ≥0) * t ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right (hmean.mgf_le t) (exp_pos _).le
    _ = _ := by rw [← exp_add]; congr 1; simp only [NNReal.coe_add]; ring

/-- Two genuine independent probability coordinates, with their literal
replacement widths, give the exact sum of squared-width/4 parameters. -/
theorem hasSubgaussianMGF_centered_prod_of_bounded_differences
    (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure B) [IsProbabilityMeasure ν]
    (f : A × B → ℝ) (M c₁ c₂ : ℝ≥0) (hf : Measurable f)
    (hbound : ∀ p, |f p| ≤ M)
    (hfirst : ∀ x x' y, |f (x,y) - f (x',y)| ≤ c₁)
    (hsecond : ∀ x y y', |f (x,y) - f (x,y')| ≤ c₂) :
    HasSubgaussianMGF (fun p => f p - ∫ q, f q ∂(μ.prod ν))
      ((c₁ / 2) ^ 2 + (c₂ / 2) ^ 2) (μ.prod ν) := by
  apply hasSubgaussianMGF_centered_prod_step μ ν f M c₂ ((c₁ / 2) ^ 2) hf hbound hsecond
  apply hasSubgaussianMGF_centered_of_oscillation μ (fun x => ∫ y, f (x,y) ∂ν) c₁
  · exact hf.stronglyMeasurable.integral_prod_right'.aemeasurable
  · exact integral_coordinate_oscillation_le ν f M c₁ hf hbound hfirst

end PaperFormalization.Manuscript
