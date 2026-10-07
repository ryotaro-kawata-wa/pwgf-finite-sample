import PaperFormalization.MatrixFactorization.ContractionPointL4
import PaperFormalization.MatrixFactorization.WeightedL4Average
import PaperFormalization.MatrixFactorization.ContractionMeanRemainder
import PaperFormalization.MatrixFactorization.CharacteristicPointwiseRadial

/-! # The sharp L4 remainder bound for an actual original marginal

A genuine density given by the squared assigned angular radius retains its
original integral exactly. The normalized point remainder is controlled by
K2/2; zero radius is handled without division. The original cap half masses
cancel the initial feature, and reflected optimal costs give the final Z/4.
-/
open MeasureTheory ProbabilityTheory Set Filter Function
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Original-measure averaging preserves the exact source remainder coefficient
K2*Z/4. No pointwise radius bound is inferred from the transport mean. -/
theorem contractionMeanRemainder_lpNorm_four_le {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (r : Real) (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu) :
    lpNorm (contractionMeanRemainder O a pole mu) 4 (stdGaussian (Weight d)) ≤
      gaussianSecondJetL4 O a * productAntipodalTransportSq pole mu (reflectedMeasure mu) / 4 := by
  letI : IsProbabilityMeasure mu := hcap.probability
  let R : UnitSphere d → Real := fun w => sphericalPoleRadius pole w^2
  let F : UnitSphere d → Weight d → Weight h :=
    fun w z => poleContractionFeatureRemainder O a (assignedPole pole w) w z
  let G : UnitSphere d → Weight d → Weight h := fun w z => (R w)⁻¹ • F w z
  have hR (w : UnitSphere d) : 0 ≤ R w := sq_nonneg _
  have hRc : Continuous R := (sphericalPoleRadius_continuous pole).pow 2
  have hRi : Integrable R mu := sphere_integrable mu R hRc
  let nu : Measure (UnitSphere d) := mu.withDensity (fun w => ENNReal.ofReal (R w))
  letI : IsFiniteMeasure nu := isFiniteMeasure_withDensity_ofReal hRi.hasFiniteIntegral
  have hswap : Measurable (fun wz : UnitSphere d × Weight d => (wz.2,wz.1)) := measurable_swap
  have hFsm : StronglyMeasurable (uncurry F) := by
    apply Measurable.stronglyMeasurable
    change Measurable (fun wz : UnitSphere d × Weight d =>
      poleContractionFeatureRemainder O a (assignedPole pole wz.1) wz.1 wz.2)
    exact (poleContractionFeatureRemainder_stronglyMeasurable O a pole).measurable.comp
      (f := fun wz : UnitSphere d × Weight d => (wz.2,wz.1)) hswap
  have hGsm : StronglyMeasurable (uncurry G) :=
    (((hRc.measurable.comp measurable_fst).inv).smul hFsm.measurable).stronglyMeasurable
  have hpoint (w : UnitSphere d) (z : Weight d) :
      norm (F w z) ≤ R w/2*featureSecondEnvelope 0 O a z := by
    have hb := poleContractionFeatureRemainder_norm_le O a (assignedPole pole w) w
      (assignedPole_short pole w) z
    simpa only [F, R, sphericalPoleRadius, sphericalDistance_comm (assignedPole pole w) w] using hb
  have hpointL4 (w : UnitSphere d) :
      lpNorm (F w) 4 (stdGaussian (Weight d)) ≤ gaussianSecondJetL4 O a * R w / 2 := by
    have hb := poleContractionFeatureRemainder_lpNorm_four_le O a (assignedPole pole w) w
      (assignedPole_short pole w)
    simpa only [F, R, sphericalPoleRadius, sphericalDistance_comm (assignedPole pole w) w] using hb
  have hz (w : UnitSphere d) (hw : R w = 0) (z : Weight d) : F w z = 0 := by
    apply norm_eq_zero.mp
    have hb := hpoint w z
    rw [hw, zero_div, zero_mul] at hb
    exact le_antisymm hb (norm_nonneg _)
  have hrec (w : UnitSphere d) (z : Weight d) : R w • G w z = F w z := by
    by_cases hw : R w = 0
    · simp only [hw, zero_smul, hz w hw z]
    · change R w • ((R w)⁻¹ • F w z) = F w z
      rw [smul_smul, mul_inv_cancel₀ hw, one_smul]
  have hGb (w : UnitSphere d) (z : Weight d) :
      norm (G w z) ≤ (1/2 : Real)*featureSecondEnvelope 0 O a z := by
    by_cases hw : R w = 0
    · simp only [G, hw, inv_zero, zero_smul, norm_zero]
      exact mul_nonneg (by norm_num) (featureSecondEnvelope_nonneg 0 O a z)
    · have hp : 0 < R w := lt_of_le_of_ne (hR w) (Ne.symm hw)
      change norm ((R w)⁻¹ • F w z) ≤ _
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (hR w)]
      calc
        _ ≤ (R w)⁻¹ * (R w/2*featureSecondEnvelope 0 O a z) :=
          mul_le_mul_of_nonneg_left (hpoint w z) (inv_nonneg.mpr (hR w))
        _ = _ := by field_simp
  have hGi (q : Nat) : Integrable (fun wz : UnitSphere d × Weight d => norm (G wz.1 wz.2)^q)
      (nu.prod (stdGaussian (Weight d))) := by
    have hd := (((featureEnvelopes_gaussian_pow_integrable (d := d) 0 O a q).2.2).const_mul
      ((1/2 : Real)^q)).comp_snd nu
    apply hd.mono' (hGsm.norm.pow q).aestronglyMeasurable
    filter_upwards with wz
    change norm (norm (G wz.1 wz.2)^q) ≤ (1/2 : Real)^q * (featureSecondEnvelope 0 O a wz.2)^q
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _), ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hGb wz.1 wz.2) q
  have hGF : Integrable (uncurry G) (nu.prod (stdGaussian (Weight d))) := by
    apply (integrable_norm_iff hGsm.aestronglyMeasurable).mp
    simpa only [pow_one, Function.uncurry] using hGi 1
  have hGL4 (w : UnitSphere d) : lpNorm (G w) 4 (stdGaussian (Weight d)) ≤
      gaussianSecondJetL4 O a/2 := by
    by_cases hw : R w = 0
    · have he : G w = (fun _ : Weight d => (0 : Weight h)) := by
        funext z
        simp only [G, hw, inv_zero, zero_smul]
      rw [he, lpNorm_fun_zero]
      exact div_nonneg lpNorm_nonneg (by norm_num)
    · have he : G w = (R w)⁻¹ • F w := rfl
      rw [he, lpNorm_const_smul]
      change norm ((R w)⁻¹) * lpNorm (F w) 4 _ ≤ _
      rw [Real.norm_eq_abs, abs_inv, abs_of_nonneg (hR w)]
      calc
        _ ≤ (R w)⁻¹ * (gaussianSecondJetL4 O a * R w/2) :=
          mul_le_mul_of_nonneg_left (hpointL4 w) (inv_nonneg.mpr (hR w))
        _ = _ := by field_simp
  have hb := weighted_lpNorm_four_average_le mu (stdGaussian (Weight d)) R hR hRc.measurable hRi
    G (gaussianSecondJetL4 O a/2) (div_nonneg lpNorm_nonneg (by norm_num)) hGF (hGi 4)
    (Eventually.of_forall hGL4)
  have he : contractionMeanRemainder O a pole mu = (fun z => ∫ w, R w • G w z ∂mu) := by
    funext z
    rw [contractionMeanRemainder_integral O a hO pole r mu hcap z]
    exact integral_congr_ae (Eventually.of_forall (fun w => (hrec w z).symm))
  rw [← he] at hb
  have hmass : (∫ w, R w ∂mu) = productAntipodalTransportSq pole mu (reflectedMeasure mu)/2 := by
    calc
      _ = ∫ w, norm (assignedGradient pole w)^2 ∂mu := by
        apply integral_congr_ae
        filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
        rw [assignedGradient_norm_on_support pole r mu hcap w hw]
        rfl
      _ = sphericalWassersteinSq mu (antipodalMeasure pole) := assignedGradient_energy pole r mu hcap
      _ = _ := by
        rw [productAntipodalTransportSq, sphericalWassersteinSq_reflected_antipodal pole mu]
        ring
  rw [hmass] at hb
  convert hb using 1
  ring

end PaperFormalization.MatrixFactorization
