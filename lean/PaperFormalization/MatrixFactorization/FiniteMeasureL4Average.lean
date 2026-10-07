import PaperFormalization.MatrixFactorization.FiniteMeasureFourthMean

/-! # Exact L4 bounds for finite-measure averages

The mass is retained linearly in the final L4 bound. This applies in particular
to weighted time or weight averages, and includes zero mass or a zero bound.
-/
open MeasureTheory Set Filter Function
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- A uniform fourth-moment bound gives the exact fourth power of the mass
for the actual finite-measure average. -/
theorem finiteMeasure_fourth_average_bound {A B E : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    (mu : Measure A) [IsFiniteMeasure mu] (gamma : Measure B) [SFinite gamma]
    (F : A → B → E) (C : Real) (_hC : 0 ≤ C)
    (hF : Integrable (uncurry F) (mu.prod gamma))
    (h4 : Integrable (fun wz : A × B => norm (F wz.1 wz.2)^4) (mu.prod gamma))
    (hb : ∀ᵐ w ∂mu, (∫ z, norm (F w z)^4 ∂gamma) ≤ C^4) :
    (∫ z, norm (∫ w, F w z ∂mu)^4 ∂gamma) ≤ (C*mu.real univ)^4 := by
  have hj := finiteMeasure_fourth_mean_product mu gamma F hF h4
  have hav : (∫ w, ∫ z, norm (F w z)^4 ∂gamma ∂mu) ≤ mu.real univ*C^4 := by
    calc
      _ ≤ ∫ _w, C^4 ∂mu := integral_mono_ae h4.integral_prod_left (integrable_const _) hb
      _ = _ := by simp [mul_comm]
  calc
    _ ≤ (mu.real univ)^3*(∫ w, ∫ z, norm (F w z)^4 ∂gamma ∂mu) := hj.2
    _ ≤ (mu.real univ)^3*(mu.real univ*C^4) :=
      mul_le_mul_of_nonneg_left hav (by positivity)
    _ = _ := by ring

/-- Uniform L4 section bounds imply the exact linear mass factor for their
actual average. Section measurability follows from the joint integrability. -/
theorem finiteMeasure_lpNorm_four_average_le {A B E : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    (mu : Measure A) [IsFiniteMeasure mu] (gamma : Measure B) [SFinite gamma]
    (F : A → B → E) (C : Real) (hC : 0 ≤ C)
    (hF : Integrable (uncurry F) (mu.prod gamma))
    (h4 : Integrable (fun wz : A × B => norm (F wz.1 wz.2)^4) (mu.prod gamma))
    (hb : ∀ᵐ w ∂mu, lpNorm (F w) 4 gamma ≤ C) :
    lpNorm (fun z => ∫ w, F w z ∂mu) 4 gamma ≤ C*mu.real univ := by
  have hb4 : ∀ᵐ w ∂mu, (∫ z, norm (F w z)^4 ∂gamma) ≤ C^4 := by
    filter_upwards [hF.prod_right_ae,hb] with w hw hbw
    change Integrable (F w) gamma at hw
    have he : lpNorm (F w) 4 gamma^4 = ∫ z, norm (F w z)^4 ∂gamma := by
      rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hw.aestronglyMeasurable]
      norm_num only [ENNReal.toReal_ofNat,Real.rpow_ofNat]
      simpa using Real.rpow_inv_natCast_pow (n := 4) (integral_nonneg (fun z => pow_nonneg (norm_nonneg _) 4)) (by norm_num)
    rw [← he]
    exact pow_le_pow_left₀ lpNorm_nonneg hbw 4
  have hsm : AEStronglyMeasurable (fun z => ∫ w, F w z ∂mu) gamma :=
    hF.integral_prod_right.aestronglyMeasurable
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hsm]
  norm_num only [ENNReal.toReal_ofNat,Real.rpow_ofNat]
  calc
    _ ≤ ((C*mu.real univ)^4)^(1/4 : Real) :=
      Real.rpow_le_rpow (integral_nonneg (fun z => pow_nonneg (norm_nonneg _) 4))
        (finiteMeasure_fourth_average_bound mu gamma F C hC hF h4 hb4) (by norm_num)
    _ = _ := by
      simpa using Real.pow_rpow_inv_natCast (n := 4) (mul_nonneg hC (measureReal_nonneg)) (by norm_num)

end PaperFormalization.MatrixFactorization
