import PaperFormalization.MatrixFactorization.SphericalTransportContinuity
import PaperFormalization.MatrixFactorization.SphericalFeatureBounds

/-! # Actual finite-Hermite feature continuity in spherical transport

The Lipschitz envelope is obtained from the polynomial derivative on the full
interval of possible inner products. Coupling estimates then apply to the
original sphere measures, and their polynomial envelopes are integrated
against the original Gaussian input. No optimal-plan or Lipschitz assumption
is introduced for the model activation.
-/
open MeasureTheory ProbabilityTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The derivative bound is uniform on the entire scalar interval reached by
unit weights at the given, unrestricted Gaussian input. -/
theorem finiteHermiteActivationJet_interval_lipschitz {d h : Nat}
    (k : Nat) (O : Finset Nat) (a : Nat → Weight h) (z : Weight d)
    (x y : Real) (hx : abs x ≤ norm z) (hy : abs y ≤ norm z) :
    norm (finiteHermiteActivationJet k O a x-finiteHermiteActivationJet k O a y) ≤
      featureEnvelope (k+1) O a z * abs (x-y) := by
  have hbound (s : Real) (hs : s ∈ Icc (-norm z) (norm z)) :
      norm (finiteHermiteActivationJet (k+1) O a s) ≤ featureEnvelope (k+1) O a z := by
    have habs : abs s ≤ norm z := abs_le.mpr hs
    exact (finiteHermiteActivationJet_growth (k+1) O a s).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (by linarith) _)
        (activationJetMass_nonneg (k+1) O a))
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s (_ : s ∈ Icc (-norm z) (norm z)) =>
      (finiteHermiteActivationJet_hasDerivAt k O a s).hasDerivWithinAt)
    hbound (convex_Icc (-norm z) (norm z)) (abs_le.mp hy) (abs_le.mp hx)
  simpa only [Real.norm_eq_abs] using hb

/-- The estimate uses the spherical angle after proving the Euclidean chord
bound, and is valid even for antipodal weights. -/
theorem finiteHermiteActivationJet_sphere_lipschitz {d h : Nat}
    (k : Nat) (O : Finset Nat) (a : Nat → Weight h) (z : Weight d)
    (w y : UnitSphere d) :
    norm (finiteHermiteActivationJet k O a (inner Real w.val z)-
      finiteHermiteActivationJet k O a (inner Real y.val z)) ≤
        featureFirstEnvelope k O a z * sphericalDistance w y := by
  have hw : abs (inner Real w.val z) ≤ norm z := by
    simpa only [unitSphere_norm, one_mul] using abs_real_inner_le_norm w.val z
  have hy : abs (inner Real y.val z) ≤ norm z := by
    simpa only [unitSphere_norm, one_mul] using abs_real_inner_le_norm y.val z
  have hi : abs (inner Real w.val z-inner Real y.val z) ≤
      sphericalDistance w y*norm z := by
    rw [← inner_sub_left]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (unitSphere_chord_le_sphericalDistance w y) (norm_nonneg z))
  calc
    _ ≤ featureEnvelope (k+1) O a z * abs (inner Real w.val z-inner Real y.val z) :=
      finiteHermiteActivationJet_interval_lipschitz k O a z _ _ hw hy
    _ ≤ featureEnvelope (k+1) O a z * (sphericalDistance w y*norm z) :=
      mul_le_mul_of_nonneg_left hi (featureEnvelope_nonneg (k+1) O a z)
    _ = _ := by unfold featureFirstEnvelope; ring

/-- This squared mean-feature bound follows from the actual infimum over all
couplings, with no chosen-plan hypothesis. -/
theorem meanFeatureJet_wasserstein_sq_le {d h : Nat} (k : Nat)
    (O : Finset Nat) (a : Nat → Weight h) (mu nu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (z : Weight d) :
    norm (meanFeature (finiteHermiteActivationJet k O a) mu z-
      meanFeature (finiteHermiteActivationJet k O a) nu z)^2 ≤
        (featureFirstEnvelope k O a z)^2*sphericalWassersteinSq mu nu := by
  apply sphericalWasserstein_expectation_sub_sq_le mu nu
    (fun w => finiteHermiteActivationJet k O a (inner Real w.val z))
    ((finiteHermiteActivationJet_continuous k O a).comp
      (continuous_subtype_val.inner (𝕜 := Real) continuous_const))
    (featureFirstEnvelope k O a z) (featureFirstEnvelope_nonneg k O a z)
  exact finiteHermiteActivationJet_sphere_lipschitz k O a z

theorem meanFeatureJet_wasserstein_norm_le {d h : Nat} (k : Nat)
    (O : Finset Nat) (a : Nat → Weight h) (mu nu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (z : Weight d) :
    norm (meanFeature (finiteHermiteActivationJet k O a) mu z-
      meanFeature (finiteHermiteActivationJet k O a) nu z) ≤
        featureFirstEnvelope k O a z*Real.sqrt (sphericalWassersteinSq mu nu) := by
  apply sphericalWasserstein_expectation_sub_norm_le mu nu
    (fun w => finiteHermiteActivationJet k O a (inner Real w.val z))
    ((finiteHermiteActivationJet_continuous k O a).comp
      (continuous_subtype_val.inner (𝕜 := Real) continuous_const))
    (featureFirstEnvelope k O a z) (featureFirstEnvelope_nonneg k O a z)
  exact finiteHermiteActivationJet_sphere_lipschitz k O a z

/-- The zeroth-jet estimate is stated directly for the original activation. -/
theorem finiteHermite_mean_wasserstein_norm_le {d h : Nat}
    (O : Finset Nat) (a : Nat → Weight h) (mu nu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (z : Weight d) :
    norm (meanFeature (finiteHermiteActivation O a) mu z-
      meanFeature (finiteHermiteActivation O a) nu z) ≤
        featureFirstEnvelope 0 O a z*Real.sqrt (sphericalWassersteinSq mu nu) := by
  simpa only [meanFeature, finiteHermiteActivationJet_zero] using
    meanFeatureJet_wasserstein_norm_le 0 O a mu nu z

/-- The finite coefficient is an actual Gaussian integral of the proved
polynomial envelope; its integrability is established below. -/
noncomputable def gaussianFeatureLipschitzSq (d : Nat) {h : Nat}
    (k : Nat) (O : Finset Nat) (a : Nat → Weight h) : Real :=
  ∫ z : Weight d, (featureFirstEnvelope k O a z)^2 ∂stdGaussian (Weight d)

theorem gaussianFeatureLipschitzSq_nonneg (d : Nat) {h : Nat}
    (k : Nat) (O : Finset Nat) (a : Nat → Weight h) :
    0 ≤ gaussianFeatureLipschitzSq d k O a := integral_nonneg (fun _z => sq_nonneg _)

/-- Gaussian integrability is discharged from the original activation and the
proved coupling bound before the second-moment comparison is integrated. -/
theorem meanFeatureJet_difference_gaussian_sq_integrable {d h : Nat} (k : Nat)
    (O : Finset Nat) (a : Nat → Weight h) (mu nu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    Integrable (fun z => norm (meanFeature (finiteHermiteActivationJet k O a) mu z-
      meanFeature (finiteHermiteActivationJet k O a) nu z)^2) (stdGaussian (Weight d)) := by
  have hm := (meanFeature_stronglyMeasurable (finiteHermiteActivationJet k O a)
    (finiteHermiteActivationJet_continuous k O a) mu).sub
    (meanFeature_stronglyMeasurable (finiteHermiteActivationJet k O a)
      (finiteHermiteActivationJet_continuous k O a) nu)
  apply (((featureEnvelopes_gaussian_pow_integrable (d := d) k O a 2).2.1).mul_const
    (sphericalWassersteinSq mu nu)).mono' (hm.norm.pow 2).aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact meanFeatureJet_wasserstein_sq_le k O a mu nu z

/-- Actual mean features are Lipschitz in Gaussian L² with respect to the
square root of the spherical transport infimum. -/
theorem meanFeatureJet_gaussian_wasserstein_sq_le {d h : Nat} (k : Nat)
    (O : Finset Nat) (a : Nat → Weight h) (mu nu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    (∫ z : Weight d, norm (meanFeature (finiteHermiteActivationJet k O a) mu z-
      meanFeature (finiteHermiteActivationJet k O a) nu z)^2 ∂stdGaussian (Weight d)) ≤
        gaussianFeatureLipschitzSq d k O a*sphericalWassersteinSq mu nu := by
  have hb := integral_mono (meanFeatureJet_difference_gaussian_sq_integrable k O a mu nu)
    (((featureEnvelopes_gaussian_pow_integrable (d := d) k O a 2).2.1).mul_const
      (sphericalWassersteinSq mu nu))
    (meanFeatureJet_wasserstein_sq_le k O a mu nu)
  simpa only [integral_mul_const, gaussianFeatureLipschitzSq] using hb

/-- The original finite-Hermite activation obeys the integrated Gaussian
estimate, without a separate integrability or coupling assumption. -/
theorem finiteHermite_mean_gaussian_wasserstein_sq_le {d h : Nat}
    (O : Finset Nat) (a : Nat → Weight h) (mu nu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    (∫ z : Weight d, norm (meanFeature (finiteHermiteActivation O a) mu z-
      meanFeature (finiteHermiteActivation O a) nu z)^2 ∂stdGaussian (Weight d)) ≤
        gaussianFeatureLipschitzSq d 0 O a*sphericalWassersteinSq mu nu := by
  simpa only [meanFeature, finiteHermiteActivationJet_zero] using
    meanFeatureJet_gaussian_wasserstein_sq_le 0 O a mu nu

end PaperFormalization.MatrixFactorization
