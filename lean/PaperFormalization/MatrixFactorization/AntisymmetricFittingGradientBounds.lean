import PaperFormalization.MatrixFactorization.AntisymmetricFittingForce

/-! # A source-derived coarse fitting-force bound on the reflected branch

The finite coefficient used here is the already proved Gaussian polynomial
envelope coefficient. It is not identified with the manuscript's sharper
L_fit. The field itself is the exact spherical Gaussian gradient, and its
smallness is derived from the actual spherical transport infimum.
-/
open MeasureTheory ProbabilityTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Oddness makes the target mean exactly zero before the transport estimate
is applied to the original marginal. -/
theorem finiteHermite_mean_antipodal_distance_bound {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] (z : Weight d) :
    norm (meanFeature (finiteHermiteActivation O a) mu z) ≤
      featureFirstEnvelope 0 O a z*Real.sqrt (sphericalWassersteinSq mu (antipodalMeasure pole)) := by
  simpa only [finiteHermite_mean_antipodal O a hO pole z, sub_zero] using
    finiteHermite_mean_wasserstein_norm_le O a mu (antipodalMeasure pole) z

/-- Both reflected output derivatives inherit a factor of the actual distance
to the antipodal target; no active coefficient is required to be nonzero. -/
theorem antisymmetric_fittingOutputGradient_norm_le {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (mu teacher : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure teacher] (i : Fin 2) (z : Weight d) :
    norm (fittingOutputGradient O a mu (reflectedMeasure mu) teacher teacher i z) ≤
      2*(fittingFeatureEnvelope O a z)^3*Real.sqrt (sphericalWassersteinSq mu (antipodalMeasure pole)) := by
  let B := fittingFeatureEnvelope O a z
  let x := meanFeature (finiteHermiteActivation O a) mu z
  let b := meanFeature (finiteHermiteActivation O a) teacher z
  let D := Real.sqrt (sphericalWassersteinSq mu (antipodalMeasure pole))
  have hB : 0 ≤ B := fittingFeatureEnvelope_nonneg O a z
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hx : norm x ≤ B :=
    (finiteHermite_mean_growth O a mu z).trans (fittingFeatureEnvelope_bounds O a z).2.2.2
  have hb : norm b ≤ B :=
    (finiteHermite_mean_growth O a teacher z).trans (fittingFeatureEnvelope_bounds O a z).2.2.2
  have hxd : norm x ≤ B*D :=
    (finiteHermite_mean_antipodal_distance_bound O a hO pole mu z).trans
      (mul_le_mul_of_nonneg_right (fittingFeatureEnvelope_bounds O a z).2.1 hD)
  have hf : norm (antisymmetricOutputForce O a mu teacher z) ≤ 2*B^3*D := by
    calc
      _ ≤ (norm x^2+norm b^2)*norm x := antisymmetricOutputForce_norm_le O a mu teacher z
      _ ≤ (B^2+B^2)*norm x := by gcongr
      _ ≤ (B^2+B^2)*(B*D) := mul_le_mul_of_nonneg_left hxd (by positivity)
      _ = _ := by ring
  fin_cases i
  · change norm (fittingOutputGradient O a mu (reflectedMeasure mu) teacher teacher 0 z) ≤ _
    rw [fittingOutputGradient_antibranch_zero O a hO mu teacher z]
    exact hf
  · change norm (fittingOutputGradient O a mu (reflectedMeasure mu) teacher teacher 1 z) ≤ _
    rw [fittingOutputGradient_antibranch_one O a hO mu teacher z, norm_neg]
    exact hf

/-- The pointwise Gaussian envelope is uniform over the sphere weight. -/
theorem antisymmetric_fittingGradientIntegrand_norm_le {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (mu teacher : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure teacher] (i : Fin 2) (w : UnitSphere d) (z : Weight d) :
    norm (fittingGradientIntegrand O a mu (reflectedMeasure mu) teacher teacher i w z) ≤
      4*(fittingFeatureEnvelope O a z)^4*Real.sqrt (sphericalWassersteinSq mu (antipodalMeasure pole)) := by
  let B := fittingFeatureEnvelope O a z
  let D := Real.sqrt (sphericalWassersteinSq mu (antipodalMeasure pole))
  have hB : 0 ≤ B := fittingFeatureEnvelope_nonneg O a z
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hE : 0 ≤ featureEnvelope 1 O a z := featureEnvelope_nonneg 1 O a z
  rw [fittingGradientIntegrand, norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ (norm (fittingOutputGradient O a mu (reflectedMeasure mu) teacher teacher i z)*
        norm (finiteHermiteActivationJet 1 O a (inner Real w.val z)))*(2*norm z) :=
      mul_le_mul (abs_real_inner_le_norm _ _) (transverseProjection_norm_le w z)
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ (2*B^3*D*featureEnvelope 1 O a z)*(2*norm z) := by
      gcongr
      · exact antisymmetric_fittingOutputGradient_norm_le O a hO pole mu teacher i z
      · exact finiteHermiteActivationJet_sphere_bound 1 O a w z
    _ = (4*B^3*D)*featureFirstEnvelope 0 O a z := by unfold featureFirstEnvelope; norm_num; ring
    _ ≤ (4*B^3*D)*B :=
      mul_le_mul_of_nonneg_left (fittingFeatureEnvelope_bounds O a z).2.1 (by positivity)
    _ = _ := by ring

/-- A uniform fitting-force estimate follows after integration against the
original Gaussian input. Its constant is explicit and deliberately coarse. -/
theorem antisymmetric_sphericalFittingGradient_norm_le {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (mu teacher : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure teacher] (i : Fin 2) (w : UnitSphere d) :
    norm (sphericalFittingGradient O a mu (reflectedMeasure mu) teacher teacher i w) ≤
      fittingCurvatureConstant d O a*Real.sqrt (sphericalWassersteinSq mu (antipodalMeasure pole)) := by
  let D := Real.sqrt (sphericalWassersteinSq mu (antipodalMeasure pole))
  have hi := fittingGradientIntegrand_integrable O a mu (reflectedMeasure mu) teacher teacher i w
  have hd : Integrable (fun z : Weight d => 4*(fittingFeatureEnvelope O a z)^4*D)
      (stdGaussian (Weight d)) := by
    simpa only [one_mul] using ((fittingFeatureEnvelope_gaussian_integrable (d := d) O a 1 4).const_mul 4).mul_const D
  calc
    _ ≤ ∫ z, norm (fittingGradientIntegrand O a mu (reflectedMeasure mu) teacher teacher i w z) ∂stdGaussian (Weight d) :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z : Weight d, 4*(fittingFeatureEnvelope O a z)^4*D ∂stdGaussian (Weight d) :=
      integral_mono hi.norm hd (antisymmetric_fittingGradientIntegrand_norm_le O a hO pole mu teacher i w)
    _ = _ := by rw [integral_mul_const, integral_const_mul]; rfl

/-- This product-distance consequence requires neither a cap assumption nor a
choice of an optimal plan. The measured transport is the original infimum. -/
theorem antisymmetric_sphericalFittingGradient_product_bound {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (mu teacher : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure teacher] (i : Fin 2) (w : UnitSphere d) :
    norm (sphericalFittingGradient O a mu (reflectedMeasure mu) teacher teacher i w) ≤
      fittingCurvatureConstant d O a*Real.sqrt
        (productAntipodalTransportSq pole mu (reflectedMeasure mu)) := by
  apply (antisymmetric_sphericalFittingGradient_norm_le O a hO pole mu teacher i w).trans
  apply mul_le_mul_of_nonneg_left _ (fittingCurvatureConstant_nonneg d O a)
  apply Real.sqrt_le_sqrt
  exact le_add_of_nonneg_right (sphericalWassersteinSq_nonneg (reflectedMeasure mu) (antipodalMeasure pole))

end PaperFormalization.MatrixFactorization
