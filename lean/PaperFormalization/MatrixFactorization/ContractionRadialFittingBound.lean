import PaperFormalization.MatrixFactorization.ContractionMeanRemainder
import PaperFormalization.MatrixFactorization.AntisymmetricFittingForce

/-! # A source-derived radial fitting bound

The original Gaussian pairing is bounded by the actual contraction remainder
and the exact vector square completion. The coefficient is the explicit
finite-Hermite polynomial envelope constant divided by 64; it is not claimed
to equal the manuscript's sharper Gaussian L4 coefficient.
-/
open MeasureTheory ProbabilityTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The scalar Gaussian pairing is integrable before its lower estimate is
integrated. All envelopes come from the actual finite activation. -/
theorem contraction_radial_gaussian_integrable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (r : Real) (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    Integrable (fun z => inner Real (antisymmetricOutputForce O a mu teacher z)
      (meanFeatureAlongContractionFirst 0 O a pole mu z 1)) (stdGaussian (Weight d)) := by
  letI : IsProbabilityMeasure mu := hcap.probability
  let Z := productAntipodalTransportSq pole mu (reflectedMeasure mu)
  have hZ : 0 ≤ Z := add_nonneg (sphericalWassersteinSq_nonneg mu (antipodalMeasure pole))
    (sphericalWassersteinSq_nonneg (reflectedMeasure mu) (antipodalMeasure pole))
  have hm := meanFeature_stronglyMeasurable _ (finiteHermiteActivation_continuous O a) mu
  have ht := meanFeature_stronglyMeasurable _ (finiteHermiteActivation_continuous O a) teacher
  have hforce : StronglyMeasurable (antisymmetricOutputForce O a mu teacher) :=
    ((hm.norm.pow 2).smul hm).add ((hm.inner (𝕜 := Real) ht).smul ht)
  have he : (fun z => meanFeatureAlongContractionFirst 0 O a pole mu z 1) =
      fun z => contractionMeanRemainder O a pole mu z+meanFeature (finiteHermiteActivation O a) mu z := by
    funext z
    simp only [contractionMeanRemainder, sub_add_cancel]
  have hder : StronglyMeasurable (fun z => meanFeatureAlongContractionFirst 0 O a pole mu z 1) := by
    rw [he]
    exact (contractionMeanRemainder_stronglyMeasurable O a hO pole r mu hcap).add hm
  have hi : Integrable (fun z : Weight d => (2*(Z/4+1))*(fittingFeatureEnvelope O a z)^4)
      (stdGaussian (Weight d)) := by
    simpa only [one_mul] using
      (fittingFeatureEnvelope_gaussian_integrable (d := d) O a 1 4).const_mul (2*(Z/4+1))
  apply hi.mono' (hforce.inner (𝕜 := Real) hder).aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs]
  have hB := fittingFeatureEnvelope_nonneg O a z
  have hb : norm (meanFeature (finiteHermiteActivation O a) mu z) ≤ fittingFeatureEnvelope O a z :=
    (finiteHermite_mean_growth O a mu z).trans (fittingFeatureEnvelope_bounds O a z).2.2.2
  have hr : norm (contractionMeanRemainder O a pole mu z) ≤ Z/4*fittingFeatureEnvelope O a z :=
    (contractionMeanRemainder_product_norm_le O a hO pole r mu hcap z).trans
      (mul_le_mul_of_nonneg_left (fittingFeatureEnvelope_bounds O a z).2.2.1 (by positivity))
  have hd : norm (meanFeatureAlongContractionFirst 0 O a pole mu z 1) ≤
      (Z/4+1)*fittingFeatureEnvelope O a z := by
    rw [congrFun he z]
    exact (norm_add_le _ _).trans (by nlinarith [add_le_add hr hb])
  have hf : norm (antisymmetricOutputForce O a mu teacher z) ≤ 2*(fittingFeatureEnvelope O a z)^3 := by
    rw [← fittingOutputGradient_antibranch_zero O a hO mu teacher z]
    exact fittingOutputGradient_norm_le O a mu (reflectedMeasure mu) teacher teacher 0 z
  calc
    _ ≤ norm (antisymmetricOutputForce O a mu teacher z)*
        norm (meanFeatureAlongContractionFirst 0 O a pole mu z 1) := abs_real_inner_le_norm _ _
    _ ≤ (2*(fittingFeatureEnvelope O a z)^3)*((Z/4+1)*fittingFeatureEnvelope O a z) :=
      mul_le_mul hf hd (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The exact one-half square completion and one-quarter remainder yield the
pointwise coefficient one-sixteenth before Gaussian integration. -/
theorem contraction_radial_gaussian_point_lower {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (r : Real) (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] (z : Weight d) :
    -(productAntipodalTransportSq pole mu (reflectedMeasure mu)^2/16)*
        (fittingFeatureEnvelope O a z)^4 ≤
      2*inner Real (antisymmetricOutputForce O a mu teacher z)
        (meanFeatureAlongContractionFirst 0 O a pole mu z 1) := by
  letI : IsProbabilityMeasure mu := hcap.probability
  let Z := productAntipodalTransportSq pole mu (reflectedMeasure mu)
  let B := fittingFeatureEnvelope O a z
  let x := meanFeature (finiteHermiteActivation O a) mu z
  let b := meanFeature (finiteHermiteActivation O a) teacher z
  let e := contractionMeanRemainder O a pole mu z
  have hZ : 0 ≤ Z := add_nonneg (sphericalWassersteinSq_nonneg mu (antipodalMeasure pole))
    (sphericalWassersteinSq_nonneg (reflectedMeasure mu) (antipodalMeasure pole))
  have hB : 0 ≤ B := fittingFeatureEnvelope_nonneg O a z
  have hx : norm x ≤ B :=
    (finiteHermite_mean_growth O a mu z).trans (fittingFeatureEnvelope_bounds O a z).2.2.2
  have hb : norm b ≤ B :=
    (finiteHermite_mean_growth O a teacher z).trans (fittingFeatureEnvelope_bounds O a z).2.2.2
  have he : norm e ≤ Z/4*B :=
    (contractionMeanRemainder_product_norm_le O a hO pole r mu hcap z).trans
      (mul_le_mul_of_nonneg_left (fittingFeatureEnvelope_bounds O a z).2.2.1 (by positivity))
  have hs : norm x^2+norm b^2 ≤ 2*B^2 := by
    nlinarith [pow_le_pow_left₀ (norm_nonneg x) hx 2, pow_le_pow_left₀ (norm_nonneg b) hb 2]
  have hp := mul_le_mul hs (pow_le_pow_left₀ (norm_nonneg e) he 2)
    (sq_nonneg (norm e)) (by positivity : 0 ≤ 2*B^2)
  have hforce := antibranch_force_square_completion x b e
  have hsum : x+e = meanFeatureAlongContractionFirst 0 O a pole mu z 1 := by
    dsimp only [x, e, contractionMeanRemainder]
    module
  rw [hsum] at hforce
  calc
    _ = (-1/2 : Real)*((2*B^2)*(Z/4*B)^2) := by ring
    _ ≤ (-1/2 : Real)*((norm x^2+norm b^2)*norm e^2) :=
      mul_le_mul_of_nonpos_left hp (by norm_num)
    _ ≤ _ := by simpa only [mul_assoc, antisymmetricOutputForce, x, b, neg_div] using hforce

/-- A coarse original-model radial fitting estimate, with no assumed radial
bound or assumed Gaussian identity among its hypotheses. -/
theorem contraction_radial_gaussian_lower {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (r : Real) (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    -(fittingCurvatureConstant d O a/64)*
        (productAntipodalTransportSq pole mu (reflectedMeasure mu))^2 ≤
      2*(∫ z, inner Real (antisymmetricOutputForce O a mu teacher z)
        (meanFeatureAlongContractionFirst 0 O a pole mu z 1) ∂stdGaussian (Weight d)) := by
  let Z := productAntipodalTransportSq pole mu (reflectedMeasure mu)
  have hi : Integrable (fun z : Weight d => -(Z^2/16)*(fittingFeatureEnvelope O a z)^4)
      (stdGaussian (Weight d)) := by
    simpa only [one_mul] using
      (fittingFeatureEnvelope_gaussian_integrable (d := d) O a 1 4).const_mul (-(Z^2/16))
  have hb := integral_mono hi
    ((contraction_radial_gaussian_integrable O a hO pole r mu hcap teacher).const_mul 2)
    (contraction_radial_gaussian_point_lower O a hO pole r mu hcap teacher)
  simp only [integral_const_mul] at hb
  calc
    _ = -(Z^2/16)*(∫ z : Weight d, (fittingFeatureEnvelope O a z)^4 ∂stdGaussian (Weight d)) := by
      dsimp only [fittingCurvatureConstant, Z]
      ring
    _ ≤ _ := hb

end PaperFormalization.MatrixFactorization
