import Mathlib

/-! # Fourth moments of finite-measure averages with the exact mass factor

The finite mass contributes its third power. Jensen is applied to the
normalized average only when the original measure is nonzero; the zero
measure is handled directly. The product statement derives integrability
and exchanges the actual two integrals before concluding the estimate.
-/
open MeasureTheory Set Filter Function
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Exact finite-mass version of the fourth-moment Jensen bound, including
zero total mass. This is the form needed for weighted probability averages. -/
theorem finiteMeasure_norm_integral_fourth_le {A E : Type*} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    (mu : Measure A) [IsFiniteMeasure mu] (F : A → E)
    (hF : Integrable F mu) (h4 : Integrable (fun w => norm (F w)^4) mu) :
    norm (∫ w, F w ∂mu)^4 ≤ (mu.real univ)^3*(∫ w, norm (F w)^4 ∂mu) := by
  by_cases hz : mu = 0
  · subst mu
    simp
  letI : NeZero mu := ⟨hz⟩
  have hm : 0 < mu.real univ := measureReal_univ_pos
  have hc : ConvexOn Real univ (fun x : E => norm x^4) :=
    convexOn_univ_norm.pow (fun x _ => norm_nonneg x) 4
  have hj := hc.map_average_le ((continuous_norm.pow 4).continuousOn) isClosed_univ
    (Eventually.of_forall (fun _ => mem_univ _)) hF h4
  simp only [average_eq,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hm,smul_eq_mul] at hj
  calc
    _ = (mu.real univ)^4*((mu.real univ)⁻¹*norm (∫ w, F w ∂mu))^4 := by
      field_simp [hm.ne']
    _ ≤ (mu.real univ)^4*((mu.real univ)⁻¹*(∫ w, norm (F w)^4 ∂mu)) :=
      mul_le_mul_of_nonneg_left hj (pow_nonneg hm.le 4)
    _ = _ := by field_simp [hm.ne']

/-- Averaging over a finite measure has the exact cubic mass factor in the
outer fourth moment. The averaged fourth moment is proved integrable. -/
theorem finiteMeasure_fourth_mean_product {A B E : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    (mu : Measure A) [IsFiniteMeasure mu] (gamma : Measure B) [SFinite gamma]
    (F : A → B → E) (hF : Integrable (uncurry F) (mu.prod gamma))
    (h4 : Integrable (fun wz : A × B => norm (F wz.1 wz.2)^4) (mu.prod gamma)) :
    Integrable (fun z => norm (∫ w, F w z ∂mu)^4) gamma ∧
      (∫ z, norm (∫ w, F w z ∂mu)^4 ∂gamma) ≤
        (mu.real univ)^3*(∫ w, ∫ z, norm (F w z)^4 ∂gamma ∂mu) := by
  have hb : ∀ᵐ z ∂gamma, norm (∫ w, F w z ∂mu)^4 ≤
      (mu.real univ)^3*(∫ w, norm (F w z)^4 ∂mu) := by
    filter_upwards [hF.prod_left_ae,h4.prod_left_ae] with z hz hz4
    exact finiteMeasure_norm_integral_fourth_le mu (fun w => F w z) hz hz4
  have hdom := h4.integral_prod_right.const_mul ((mu.real univ)^3)
  have hi : Integrable (fun z => norm (∫ w, F w z ∂mu)^4) gamma := by
    apply hdom.mono' (hF.integral_prod_right.aestronglyMeasurable.norm.pow 4)
    filter_upwards [hb] with z hz
    change norm (norm (∫ w, F w z ∂mu)^4) ≤ (mu.real univ)^3*(∫ w, norm (F w z)^4 ∂mu)
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    exact hz
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ z, (mu.real univ)^3*(∫ w, norm (F w z)^4 ∂mu) ∂gamma :=
      integral_mono_ae hi hdom hb
    _ = (mu.real univ)^3*(∫ w, ∫ z, norm (F w z)^4 ∂gamma ∂mu) := by
      rw [integral_const_mul,← integral_integral_swap h4]

end PaperFormalization.MatrixFactorization
