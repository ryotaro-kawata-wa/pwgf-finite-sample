import PaperFormalization.MatrixFactorization.FiniteMeasureL4Average
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Exact L4 bounds for nonnegative weighted averages

The weighting measure is constructed from the original measure and an actual
integrable nonnegative density. Its mass is the original weight integral.
No normalization by a possibly zero total mass is needed.
-/
open MeasureTheory Set Filter Function
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The real mass of the actual density measure is the original weight integral. -/
theorem withDensity_ofReal_mass {A : Type*} [MeasurableSpace A]
    (mu : Measure A) (R : A → Real) (hR : ∀ w, 0 ≤ R w)
    (hm : Measurable R) (hi : Integrable R mu) :
    (mu.withDensity (fun w => ENNReal.ofReal (R w))).real univ = ∫ w, R w ∂mu := by
  letI := isFiniteMeasure_withDensity_ofReal hi.hasFiniteIntegral
  have he (w : A) : (ENNReal.ofReal (R w)).toReal = R w := ENNReal.toReal_ofReal (hR w)
  have hh := integral_withDensity_eq_integral_toReal_smul (μ := mu) hm.ennreal_ofReal
    (Eventually.of_forall (fun w => ENNReal.ofReal_lt_top)) (fun _w : A => (1 : Real))
  simp only [integral_const,smul_eq_mul,mul_one,he] at hh
  exact hh

/-- Uniform L4 bounds under a genuine nonnegative density retain the exact
integral of the weight, including a zero weighting measure or zero constant. -/
theorem weighted_lpNorm_four_average_le {A B E : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    (mu : Measure A) (gamma : Measure B) [SFinite gamma]
    (R : A → Real) (hR : ∀ w, 0 ≤ R w) (hm : Measurable R) (hi : Integrable R mu)
    (G : A → B → E) (C : Real) (hC : 0 ≤ C)
    (hG : Integrable (uncurry G) ((mu.withDensity (fun w => ENNReal.ofReal (R w))).prod gamma))
    (h4 : Integrable (fun wz : A × B => norm (G wz.1 wz.2)^4)
      ((mu.withDensity (fun w => ENNReal.ofReal (R w))).prod gamma))
    (hb : ∀ᵐ w ∂mu.withDensity (fun w => ENNReal.ofReal (R w)), lpNorm (G w) 4 gamma ≤ C) :
    lpNorm (fun z => ∫ w, R w • G w z ∂mu) 4 gamma ≤ C*(∫ w, R w ∂mu) := by
  letI := isFiniteMeasure_withDensity_ofReal hi.hasFiniteIntegral
  have he : (fun z => ∫ w, R w • G w z ∂mu) =
      (fun z => ∫ w, G w z ∂mu.withDensity (fun w => ENNReal.ofReal (R w))) := by
    funext z
    symm
    have hh := integral_withDensity_eq_integral_toReal_smul (μ := mu) hm.ennreal_ofReal
      (Eventually.of_forall (fun w => ENNReal.ofReal_lt_top)) (fun w => G w z)
    simpa only [ENNReal.toReal_ofReal (hR _)] using hh
  rw [he]
  have hh := finiteMeasure_lpNorm_four_average_le
    (mu.withDensity (fun w => ENNReal.ofReal (R w))) gamma G C hC hG h4 hb
  rw [withDensity_ofReal_mass mu R hR hm hi] at hh
  exact hh

end PaperFormalization.MatrixFactorization
