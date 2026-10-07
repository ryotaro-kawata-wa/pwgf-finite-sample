import PaperFormalization.MatrixFactorization.GaussianFeatureWasserstein
import PaperFormalization.MatrixFactorization.ContractionMeanRemainder
import PaperFormalization.MatrixFactorization.CharacteristicPointwiseRadial
import PaperFormalization.MatrixFactorization.GaussianOutputL4Bounds
import PaperFormalization.MatrixFactorization.WeightedL4Average
import PaperFormalization.MatrixFactorization.ContractionPointL4

/-! # Sharp Gaussian L4 control of the original antisymmetric mean

The assigned-pole feature cancels only after using the original exact cap
half masses. The radial first moment is estimated by its actual transport
second moment before the sharp pointwise Gaussian bound is averaged.
-/
open MeasureTheory ProbabilityTheory Set Filter Function
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The original mean is the mean of its actual assigned-pole differences. -/
theorem meanFeature_eq_integral_assigned_difference {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (r : Real) (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu) (z : Weight d) :
    meanFeature (finiteHermiteActivation O a) mu z =
      ∫ w, (finiteHermiteActivation O a (inner Real w.val z)-
        finiteHermiteActivation O a (inner Real (assignedPole pole w).val z)) ∂mu := by
  letI : IsProbabilityMeasure mu := hcap.probability
  have he (w : UnitSphere d) :
      finiteHermiteActivation O a (inner Real w.val z)-
        finiteHermiteActivation O a (inner Real (assignedPole pole w).val z) =
      contractionFeatureJet 0 O a pole w z 1-contractionFeatureJet 0 O a pole w z 0 := by
    change _ = finiteHermiteActivationJet 0 O a (inner Real (assignedContraction pole 1 w).val z)-
      finiteHermiteActivationJet 0 O a (inner Real (assignedContraction pole 0 w).val z)
    rw [assignedContraction_one,assignedContraction_zero]
    simp only [finiteHermiteActivationJet_zero]
  simp_rw [he]
  rw [integral_sub (contractionFeature_integrable 0 O a pole mu z 1).1
    (contractionFeature_integrable 0 O a pole mu z 0).1,
    ← meanFeatureAlongContraction_integral 0 O a pole mu z 1,
    ← meanFeatureAlongContraction_integral 0 O a pole mu z 0,
    meanFeatureAlongContraction_zero O a hO pole r mu hcap z,
    meanFeatureAlongContraction_one,sub_zero]
  simp only [meanFeature,finiteHermiteActivationJet_zero]

/-- The radius second moment is exactly half the actual reflected product cost. -/
theorem sphericalPoleRadius_sq_integral {d : Nat} (pole : UnitSphere d)
    (r : Real) (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu) :
    (∫ w, (sphericalPoleRadius pole w)^2 ∂mu) =
      productAntipodalTransportSq pole mu (reflectedMeasure mu)/2 := by
  letI : IsProbabilityMeasure mu := hcap.probability
  calc
    _ = ∫ w, norm (assignedGradient pole w)^2 ∂mu := by
      apply integral_congr_ae
      filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
      rw [assignedGradient_norm_on_support pole r mu hcap w hw]
      rfl
    _ = _ := by
      rw [assignedGradient_energy pole r mu hcap, productAntipodalTransportSq,
        sphericalWassersteinSq_reflected_antipodal pole mu]
      ring

/-- Cauchy--Schwarz uses the true radius second moment and retains the
source factor one-half inside the square root. -/
theorem sphericalPoleRadius_integral_le_sqrt_product {d : Nat} (pole : UnitSphere d)
    (r : Real) (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu) :
    (∫ w, sphericalPoleRadius pole w ∂mu) ≤
      Real.sqrt (productAntipodalTransportSq pole mu (reflectedMeasure mu)/2) := by
  letI : IsProbabilityMeasure mu := hcap.probability
  have hi := sphere_integrable mu (sphericalPoleRadius pole) (sphericalPoleRadius_continuous pole)
  have hi2 := sphere_integrable mu (fun w => (sphericalPoleRadius pole w)^2)
    ((sphericalPoleRadius_continuous pole).pow 2)
  have hb := probability_integral_sq_ge_sq_integral mu (sphericalPoleRadius pole) hi hi2
  rw [sphericalPoleRadius_sq_integral pole r mu hcap] at hb
  have hZ : 0 ≤ productAntipodalTransportSq pole mu (reflectedMeasure mu)/2 := by
    rw [← sphericalPoleRadius_sq_integral pole r mu hcap]
    exact integral_nonneg (fun _ => sq_nonneg _)
  exact (Real.le_sqrt (integral_nonneg (sphericalPoleRadius_nonneg pole)) hZ).mpr hb

/-- The actual odd mean on the original two-cap law satisfies the manuscript's
sharp first-jet L4 estimate, with the true reflected product distance. -/
theorem antisymmetric_mean_lpNorm_four_le {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (r : Real) (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu) :
    lpNorm (meanFeature (finiteHermiteActivation O a) mu) 4 (stdGaussian (Weight d)) ≤
      gaussianFirstJetL4 O a *
        Real.sqrt (productAntipodalTransportSq pole mu (reflectedMeasure mu)/2) := by
  letI : IsProbabilityMeasure mu := hcap.probability
  let R := sphericalPoleRadius pole
  let G : UnitSphere d → Weight d → Weight h := fun w z => (R w)⁻¹ •
    (finiteHermiteActivation O a (inner Real w.val z)-
      finiteHermiteActivation O a (inner Real (assignedPole pole w).val z))
  have hR (w : UnitSphere d) : 0 ≤ R w := sphericalPoleRadius_nonneg pole w
  have hmR : Measurable R := (sphericalPoleRadius_continuous pole).measurable
  have hiR : Integrable R mu := sphere_integrable mu R (sphericalPoleRadius_continuous pole)
  let nu := mu.withDensity (fun w => ENNReal.ofReal (R w))
  letI : IsFiniteMeasure nu := isFiniteMeasure_withDensity_ofReal hiR.hasFiniteIntegral
  have hmG : Measurable (uncurry G) := by
    have hm0 : Measurable (fun wz : UnitSphere d × Weight d => wz.1.val) :=
      measurable_subtype_coe.comp measurable_fst
    have hm1 : Measurable (fun wz : UnitSphere d × Weight d => (assignedPole pole wz.1).val) :=
      measurable_subtype_coe.comp ((assignedPole_measurable pole).comp measurable_fst)
    exact ((hmR.comp measurable_fst).inv).smul
      (((finiteHermiteActivation_continuous O a).measurable.comp (hm0.inner (𝕜 := Real) measurable_snd)).sub
        ((finiteHermiteActivation_continuous O a).measurable.comp (hm1.inner (𝕜 := Real) measurable_snd)))
  have hGb (w : UnitSphere d) (z : Weight d) : norm (G w z) ≤ featureFirstEnvelope 0 O a z := by
    have hd : norm (finiteHermiteActivation O a (inner Real w.val z)-
        finiteHermiteActivation O a (inner Real (assignedPole pole w).val z)) ≤
        featureFirstEnvelope 0 O a z*R w := by
      simpa only [R,sphericalPoleRadius,finiteHermiteActivationJet_zero] using
        finiteHermiteActivationJet_sphere_lipschitz 0 O a z w (assignedPole pole w)
    by_cases hz : R w = 0
    · simpa only [G,hz,inv_zero,zero_smul,norm_zero] using featureFirstEnvelope_nonneg 0 O a z
    · have hp : 0 < R w := lt_of_le_of_ne (hR w) (Ne.symm hz)
      simp only [G,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hp]
      calc
        _ ≤ (R w)⁻¹*(featureFirstEnvelope 0 O a z*R w) :=
          mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr (hR w))
        _ = _ := by field_simp [hz]
  have hiE : Integrable (featureFirstEnvelope (d := d) 0 O a) (stdGaussian (Weight d)) := by
    simpa only [pow_one] using (featureEnvelopes_gaussian_pow_integrable (d := d) 0 O a 1).2.1
  have hG : Integrable (uncurry G) (nu.prod (stdGaussian (Weight d))) := by
    apply (hiE.comp_snd nu).mono' hmG.aestronglyMeasurable
    exact Eventually.of_forall (fun wz => hGb wz.1 wz.2)
  have h4 : Integrable (fun wz : UnitSphere d × Weight d => norm (G wz.1 wz.2)^4)
      (nu.prod (stdGaussian (Weight d))) := by
    apply ((featureEnvelopes_gaussian_pow_integrable (d := d) 0 O a 4).2.1.comp_snd nu).mono'
      (hmG.norm.pow_const 4).aestronglyMeasurable
    apply Eventually.of_forall
    intro wz
    change norm (norm (G wz.1 wz.2)^4) ≤ (featureFirstEnvelope 0 O a wz.2)^4
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hGb wz.1 wz.2) 4
  have hK : 0 ≤ gaussianFirstJetL4 O a := lpNorm_nonneg
  have hb : ∀ᵐ w ∂nu, lpNorm (G w) 4 (stdGaussian (Weight d)) ≤ gaussianFirstJetL4 O a := by
    apply Eventually.of_forall
    intro w
    have hd : lpNorm (fun z : Weight d => finiteHermiteActivation O a (inner Real w.val z)-
        finiteHermiteActivation O a (inner Real (assignedPole pole w).val z)) 4 (stdGaussian (Weight d)) ≤
        gaussianFirstJetL4 O a*R w := by
      simpa only [R,sphericalPoleRadius,sphericalDistance_comm (assignedPole pole w) w] using
        poleContractionFeatureDifference_lpNorm_four_le O a (assignedPole pole w) w (assignedPole_short pole w)
    by_cases hz : R w = 0
    · simpa only [G,hz,inv_zero,zero_smul,lpNorm_fun_zero] using hK
    · have hp : 0 < R w := lt_of_le_of_ne (hR w) (Ne.symm hz)
      change lpNorm ((R w)⁻¹ • (fun z : Weight d =>
        finiteHermiteActivation O a (inner Real w.val z)-
          finiteHermiteActivation O a (inner Real (assignedPole pole w).val z)))
        4 (stdGaussian (Weight d)) ≤ _
      rw [lpNorm_const_smul]
      simp only [coe_nnnorm,Real.norm_eq_abs,abs_inv,abs_of_pos hp]
      calc
        _ ≤ (R w)⁻¹*(gaussianFirstJetL4 O a*R w) :=
          mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr (hR w))
        _ = _ := by field_simp [hz]
  have he (w : UnitSphere d) (z : Weight d) : R w • G w z =
      finiteHermiteActivation O a (inner Real w.val z)-
        finiteHermiteActivation O a (inner Real (assignedPole pole w).val z) := by
    by_cases hz : R w = 0
    · have hw : w = assignedPole pole w := (sphericalDistance_eq_zero_iff w (assignedPole pole w)).mp hz
      have hd : finiteHermiteActivation O a (inner Real w.val z)-
          finiteHermiteActivation O a (inner Real (assignedPole pole w).val z) = 0 :=
        sub_eq_zero.mpr (congrArg (fun y : UnitSphere d => finiteHermiteActivation O a (inner Real y.val z)) hw)
      simp only [hz,zero_smul,hd]
    · simp only [G,smul_smul,mul_inv_cancel₀ hz,one_smul]
  have hmean : (fun z => ∫ w, R w • G w z ∂mu) = meanFeature (finiteHermiteActivation O a) mu := by
    funext z
    simp_rw [he]
    exact (meanFeature_eq_integral_assigned_difference O a hO pole r mu hcap z).symm
  have hw := weighted_lpNorm_four_average_le mu (stdGaussian (Weight d)) R hR hmR hiR G
    (gaussianFirstJetL4 O a) hK hG h4 hb
  rw [hmean] at hw
  exact hw.trans (mul_le_mul_of_nonneg_left
    (sphericalPoleRadius_integral_le_sqrt_product pole r mu hcap) hK)

end PaperFormalization.MatrixFactorization
