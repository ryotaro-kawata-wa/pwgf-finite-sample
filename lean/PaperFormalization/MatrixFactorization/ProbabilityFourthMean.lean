import Mathlib

/-! # Fourth-moment control of an original probability mean

Jensen's inequality is applied to the actual convex function x ↦ ‖x‖^4.
The product theorem derives integrability of the averaged fourth moment and
performs the genuine Fubini exchange. These generic helpers assume the input
integrals exist; model applications must establish those hypotheses from the
finite activation rather than supply the desired moment inequality.
-/
open MeasureTheory Set Filter Function
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The fourth moment of an actual probability mean is bounded by the
original fourth moment, with no dimension or Hilbert-space restriction. -/
theorem probability_norm_integral_fourth_le {A E : Type*} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    (mu : Measure A) [IsProbabilityMeasure mu] (F : A → E)
    (hF : Integrable F mu) (h4 : Integrable (fun w => norm (F w)^4) mu) :
    norm (∫ w, F w ∂mu)^4 ≤ ∫ w, norm (F w)^4 ∂mu := by
  have hc : ConvexOn Real univ (fun x : E => norm x^4) :=
    convexOn_univ_norm.pow (fun x _ => norm_nonneg x) 4
  exact hc.map_integral_le ((continuous_norm.pow 4).continuousOn) isClosed_univ
    (Eventually.of_forall (fun _ => mem_univ _)) hF h4

/-- Original-measure averaging controls the outer fourth moment. The
integrability of the averaged fourth moment is derived, not assumed. -/
theorem probability_fourth_mean_product {A B E : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    (mu : Measure A) [IsProbabilityMeasure mu] (gamma : Measure B) [SFinite gamma]
    (F : A → B → E) (hF : Integrable (uncurry F) (mu.prod gamma))
    (h4 : Integrable (fun wz : A × B => norm (F wz.1 wz.2)^4) (mu.prod gamma)) :
    Integrable (fun z => norm (∫ w, F w z ∂mu)^4) gamma ∧
      (∫ z, norm (∫ w, F w z ∂mu)^4 ∂gamma) ≤
        ∫ w, ∫ z, norm (F w z)^4 ∂gamma ∂mu := by
  have hb : ∀ᵐ z ∂gamma, norm (∫ w, F w z ∂mu)^4 ≤ ∫ w, norm (F w z)^4 ∂mu := by
    filter_upwards [hF.prod_left_ae,h4.prod_left_ae] with z hz hz4
    exact probability_norm_integral_fourth_le mu (fun w => F w z) hz hz4
  have hi : Integrable (fun z => norm (∫ w, F w z ∂mu)^4) gamma := by
    apply h4.integral_prod_right.mono' (hF.integral_prod_right.aestronglyMeasurable.norm.pow 4)
    filter_upwards [hb] with z hz
    change norm (norm (∫ w, F w z ∂mu)^4) ≤ ∫ w, norm (F w z)^4 ∂mu
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    exact hz
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ z, ∫ w, norm (F w z)^4 ∂mu ∂gamma :=
      integral_mono_ae hi h4.integral_prod_right hb
    _ = ∫ w, ∫ z, norm (F w z)^4 ∂gamma ∂mu :=
      (integral_integral_swap h4).symm

end PaperFormalization.MatrixFactorization
