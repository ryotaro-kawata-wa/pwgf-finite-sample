import PaperFormalization.MatrixFactorization.ContractionFeatureIntegral
import PaperFormalization.MatrixFactorization.SphericalTransportSymmetry

/-! # The actual mean-feature remainder of assigned-pole contraction

The remainder is averaged over the original marginal. Its initial feature
vanishes only after the actual assigned-pole pushforward and cap half-mass
conditions are used. The coefficient one-quarter for product distance is
then an equality consequence of reflected angular transport costs.
-/
open MeasureTheory ProbabilityTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def contractionMeanRemainder {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (mu : Measure (UnitSphere d))
    (z : Weight d) : Weight h :=
  meanFeatureAlongContractionFirst 0 O a pole mu z 1-
    meanFeature (finiteHermiteActivation O a) mu z

/-- The endpoint remainder refers to the original assigned gradient. -/
theorem contractionFeature_remainder_identity {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole w : UnitSphere d) (z : Weight d) :
    poleContractionFeatureRemainder O a (assignedPole pole w) w z =
      contractionFeatureFirst 0 O a pole w z 1-
        contractionFeatureJet 0 O a pole w z 1+contractionFeatureJet 0 O a pole w z 0 := by
  change _ = inner Real (assignedContractionVelocity pole 1 w) z •
    finiteHermiteActivationJet 1 O a (inner Real (assignedContraction pole 1 w).val z) -
      finiteHermiteActivationJet 0 O a (inner Real (assignedContraction pole 1 w).val z) +
        finiteHermiteActivationJet 0 O a (inner Real (assignedContraction pole 0 w).val z)
  rw [assignedContractionVelocity_one, assignedContraction_one, assignedContraction_zero]
  simp only [finiteHermiteActivationJet_zero, poleContractionFeatureRemainder, assignedGradient]

set_option backward.isDefEq.respectTransparency false in
theorem poleContractionFeatureRemainder_integrable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (z : Weight d) :
    Integrable (fun w => poleContractionFeatureRemainder O a (assignedPole pole w) w z) mu := by
  have h1 := contractionFeature_integrable 0 O a pole mu z 1
  have h0 := contractionFeature_integrable 0 O a pole mu z 0
  simp_rw [contractionFeature_remainder_identity]
  exact (h1.2.1.sub h1.1).add h0.1

set_option backward.isDefEq.respectTransparency false in
/-- The original half-mass assumptions cancel the initial pole feature after
integration, rather than asserting pointwise cancellation. -/
theorem contractionMeanRemainder_integral {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (r : Real) (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu) (z : Weight d) :
    contractionMeanRemainder O a pole mu z =
      ∫ w, poleContractionFeatureRemainder O a (assignedPole pole w) w z ∂mu := by
  letI : IsProbabilityMeasure mu := hcap.probability
  have h1 := contractionFeature_integrable 0 O a pole mu z 1
  have h0 := contractionFeature_integrable 0 O a pole mu z 0
  have hsub : Integrable (fun w => contractionFeatureFirst 0 O a pole w z 1-
      contractionFeatureJet 0 O a pole w z 1) mu := by
    exact h1.2.1.sub h1.1
  simp_rw [contractionFeature_remainder_identity]
  rw [integral_add hsub h0.1, integral_sub h1.2.1 h1.1,
    ← meanFeatureAlongContraction_integral 0 O a pole mu z 1,
    ← meanFeatureAlongContraction_integral 0 O a pole mu z 0,
    meanFeatureAlongContraction_zero O a hO pole r mu hcap z, add_zero,
    meanFeatureAlongContraction_one]
  simp only [contractionMeanRemainder, meanFeatureAlongContractionFirst,
    meanFeature, finiteHermiteActivationJet_zero]

/-- One original marginal contributes exactly one-half of its actual squared
angular transport cost to the mean-feature remainder envelope. -/
theorem contractionMeanRemainder_norm_le {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (r : Real) (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu) (z : Weight d) :
    norm (contractionMeanRemainder O a pole mu z) ≤
      sphericalWassersteinSq mu (antipodalMeasure pole)/2 * featureSecondEnvelope 0 O a z := by
  letI : IsProbabilityMeasure mu := hcap.probability
  have hi := poleContractionFeatureRemainder_integrable O a pole mu z
  have hd := ((assignedGradient_norm_sq_integrable pole r mu hcap).div_const 2).mul_const
    (featureSecondEnvelope 0 O a z)
  rw [contractionMeanRemainder_integral O a hO pole r mu hcap z]
  calc
    _ ≤ ∫ w, norm (poleContractionFeatureRemainder O a (assignedPole pole w) w z) ∂mu :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ w, norm (assignedGradient pole w)^2/2*featureSecondEnvelope 0 O a z ∂mu := by
      apply integral_mono_ae hi.norm hd
      filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
      rw [assignedGradient_norm_on_support pole r mu hcap w hw, sphericalDistance_comm w (assignedPole pole w)]
      exact poleContractionFeatureRemainder_norm_le O a (assignedPole pole w) w (assignedPole_short pole w) z
    _ = _ := by rw [integral_mul_const, integral_div, assignedGradient_energy pole r mu hcap]

/-- Reflection of every transport plan supplies the exact product factor two,
so the original product distance has the source coefficient one-quarter. -/
theorem contractionMeanRemainder_product_norm_le {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (r : Real) (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu) (z : Weight d) :
    norm (contractionMeanRemainder O a pole mu z) ≤
      productAntipodalTransportSq pole mu (reflectedMeasure mu)/4 * featureSecondEnvelope 0 O a z := by
  letI : IsProbabilityMeasure mu := hcap.probability
  have hb := contractionMeanRemainder_norm_le O a hO pole r mu hcap z
  convert hb using 1
  rw [productAntipodalTransportSq, sphericalWassersteinSq_reflected_antipodal pole mu]
  ring

/-- Joint measurability keeps the original assigned-pole map measurable;
continuity across its equatorial tie is not required. -/
theorem poleContractionFeatureRemainder_stronglyMeasurable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) :
    StronglyMeasurable (fun p : Weight d × UnitSphere d =>
      poleContractionFeatureRemainder O a (assignedPole pole p.2) p.2 p.1) := by
  have hq : Measurable (fun p : Weight d × UnitSphere d => assignedGradient pole p.2) :=
    (assignedGradient_measurable pole).comp measurable_snd
  have hw : Measurable (fun p : Weight d × UnitSphere d => p.2.val) :=
    measurable_subtype_coe.comp measurable_snd
  have hy : Measurable (fun p : Weight d × UnitSphere d => (assignedPole pole p.2).val) :=
    measurable_subtype_coe.comp ((assignedPole_measurable pole).comp measurable_snd)
  have hj := (finiteHermiteActivationJet_continuous 1 O a).measurable.comp (hw.inner (𝕜 := Real) measurable_fst)
  have h1 := (finiteHermiteActivation_continuous O a).measurable.comp (hw.inner (𝕜 := Real) measurable_fst)
  have h0 := (finiteHermiteActivation_continuous O a).measurable.comp (hy.inner (𝕜 := Real) measurable_fst)
  exact ((((hq.inner (𝕜 := Real) measurable_fst).smul hj).sub h1).add h0).stronglyMeasurable

/-- The actual averaged remainder is strongly measurable in Gaussian input. -/
theorem contractionMeanRemainder_stronglyMeasurable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (r : Real) (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu) :
    StronglyMeasurable (contractionMeanRemainder O a pole mu) := by
  letI : IsProbabilityMeasure mu := hcap.probability
  have he : contractionMeanRemainder O a pole mu = fun z =>
      ∫ w, poleContractionFeatureRemainder O a (assignedPole pole w) w z ∂mu :=
    funext (contractionMeanRemainder_integral O a hO pole r mu hcap)
  rw [he]
  exact (poleContractionFeatureRemainder_stronglyMeasurable O a pole).integral_prod_right

/-- The product needed by the source square completion is genuinely Gaussian
integrable before its expectation is bounded. -/
theorem contractionMeanRemainder_weighted_sq_integrable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (r : Real) (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu) :
    Integrable (fun z : Weight d => norm (contractionMeanRemainder O a pole mu z)^2*
      (fittingFeatureEnvelope O a z)^2) (stdGaussian (Weight d)) := by
  letI : IsProbabilityMeasure mu := hcap.probability
  let Z := productAntipodalTransportSq pole mu (reflectedMeasure mu)
  have hZ : 0 ≤ Z := add_nonneg (sphericalWassersteinSq_nonneg mu (antipodalMeasure pole))
    (sphericalWassersteinSq_nonneg (reflectedMeasure mu) (antipodalMeasure pole))
  have hB : Continuous (fun z : Weight d => fittingFeatureEnvelope O a z) := by
    unfold fittingFeatureEnvelope
    fun_prop
  have hsm := ((contractionMeanRemainder_stronglyMeasurable O a hO pole r mu hcap).norm.pow 2).mul
    (hB.stronglyMeasurable.pow 2)
  have hi : Integrable (fun z : Weight d => (Z/4)^2*(fittingFeatureEnvelope O a z)^4)
      (stdGaussian (Weight d)) := by
    simpa only [one_mul] using
      (fittingFeatureEnvelope_gaussian_integrable (d := d) O a 1 4).const_mul ((Z/4)^2)
  apply hi.mono' hsm.aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  have hb : norm (contractionMeanRemainder O a pole mu z) ≤ Z/4*fittingFeatureEnvelope O a z :=
    (contractionMeanRemainder_product_norm_le O a hO pole r mu hcap z).trans
      (mul_le_mul_of_nonneg_left (fittingFeatureEnvelope_bounds O a z).2.2.1 (by positivity))
  have hpow := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) hb 2) (sq_nonneg (fittingFeatureEnvelope O a z))
  calc
    _ ≤ (Z/4*fittingFeatureEnvelope O a z)^2*(fittingFeatureEnvelope O a z)^2 := hpow
    _ = (Z/4)^2*(fittingFeatureEnvelope O a z)^4 := by ring

end PaperFormalization.MatrixFactorization
