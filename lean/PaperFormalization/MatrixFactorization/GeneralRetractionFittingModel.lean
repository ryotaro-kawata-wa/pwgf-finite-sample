import PaperFormalization.MatrixFactorization.GeneralRetractionFeatureGaussian
import PaperFormalization.MatrixFactorization.SphericalFittingVariation

/-! # Uniform Gaussian control of the actual normalized fitting path

The normalized pointwise path and its mean-feature derivatives use the original
sphere measures. A common envelope absorbs the proved speed factors two and
six; it is finite under the existing Gaussian law, with no new hypotheses.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def variationRetractedFeature {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (i : Fin 2) (t : Real) (z : Weight d) : Weight h :=
  meanFeatureJetAlongRetract 0 O a (P.measure i) (P.velocity i) (P.tangent i) z t

noncomputable def variationRetractedFeatureFirst {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (i : Fin 2) (t : Real) (z : Weight d) : Weight h :=
  meanFeatureJetAlongRetractFirst 0 O a (P.measure i) (P.velocity i) (P.tangent i) z t

noncomputable def variationRetractedFeatureSecond {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (i : Fin 2) (t : Real) (z : Weight d) : Weight h :=
  meanFeatureJetAlongRetractSecond 0 O a (P.measure i) (P.velocity i) (P.tangent i) z t

noncomputable def variationRetractedFeatureBound {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (z : Weight d) : Real :=
  6 * variationFeatureBound O a P z

theorem variationRetractedFeatureBound_nonneg {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (z : Weight d) :
    0 ≤ variationRetractedFeatureBound O a P z :=
  mul_nonneg (by norm_num) (variationFeatureBound_nonneg O a P z)

theorem variationRetractedFeature_bounds {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (i : Fin 2) (t : Real) (z : Weight d) :
    norm (variationRetractedFeature O a P i t z) ≤ variationRetractedFeatureBound O a P z ∧
    norm (variationRetractedFeatureFirst O a P i t z) ≤ variationRetractedFeatureBound O a P z ∧
    norm (variationRetractedFeatureSecond O a P i t z) ≤ variationRetractedFeatureBound O a P z := by
  letI : IsProbabilityMeasure (P.measure i) := (P.cap i).probability
  have hb := meanFeatureAlongRetract_bounds 0 O a (P.measure i) (P.velocity i) (P.tangent i)
    (P.continuous_velocity i) z t
  have he := fittingFeatureEnvelope_bounds O a z
  have hs := variationSpeedScale_bounds P i
  have hS : 0 ≤ variationSpeedScale P := le_trans (by norm_num) hs.1
  have hB := variationFeatureBound_nonneg O a P z
  have hinc : variationFeatureBound O a P z ≤ variationRetractedFeatureBound O a P z := by
    unfold variationRetractedFeatureBound
    linarith
  refine ⟨?_, ?_, ?_⟩
  · exact ((hb.1.trans he.1).trans
      (le_mul_of_one_le_left (fittingFeatureEnvelope_nonneg O a z) hs.1)).trans hinc
  · have hprod := mul_le_mul hs.2.1 he.2.1 (featureFirstEnvelope_nonneg 0 O a z) hS
    have hscaled := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : Real) ≤ 2)
    have hlarge : 2 * variationFeatureBound O a P z ≤ variationRetractedFeatureBound O a P z := by
      unfold variationRetractedFeatureBound
      linarith
    exact (hb.2.1.trans (by simpa only [variationFeatureBound, mul_assoc] using hscaled)).trans hlarge
  · have hprod := mul_le_mul hs.2.2 he.2.2.1 (featureSecondEnvelope_nonneg 0 O a z) hS
    have hscaled := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : Real) ≤ 6)
    exact hb.2.2.trans (by simpa only [variationRetractedFeatureBound, variationFeatureBound, mul_assoc] using hscaled)

theorem teacherOutput_retracted_bound {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (z : Weight d) :
    norm (teacherOutput O a teacher1 teacher2 z) ≤ (variationRetractedFeatureBound O a P z)^2 := by
  apply (teacherOutput_bound O a P teacher1 teacher2 z).trans
  have hB := variationFeatureBound_nonneg O a P z
  apply pow_le_pow_left₀ hB
  unfold variationRetractedFeatureBound
  linarith

theorem variationRetractedFeature_stronglyMeasurable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (i : Fin 2) (t : Real) :
    StronglyMeasurable (variationRetractedFeature O a P i t) ∧
    StronglyMeasurable (variationRetractedFeatureFirst O a P i t) ∧
    StronglyMeasurable (variationRetractedFeatureSecond O a P i t) := by
  letI : IsProbabilityMeasure (P.measure i) := (P.cap i).probability
  exact meanFeatureAlongRetract_stronglyMeasurable 0 O a (P.measure i) (P.velocity i)
    (P.tangent i) (P.continuous_velocity i) t

theorem variationRetractedFeature_variations {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (i : Fin 2) (t : Real) (z : Weight d) :
    HasDerivAt (fun u => variationRetractedFeature O a P i u z) (variationRetractedFeatureFirst O a P i t z) t ∧
    HasDerivAt (fun u => variationRetractedFeatureFirst O a P i u z) (variationRetractedFeatureSecond O a P i t z) t := by
  letI : IsProbabilityMeasure (P.measure i) := (P.cap i).probability
  exact meanFeatureJetAlongRetract_variations 0 O a (P.measure i) (P.velocity i)
    (P.tangent i) (P.continuous_velocity i) z t

theorem variationRetractedFeature_initial_jets {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (i : Fin 2) (z : Weight d) :
    variationRetractedFeature O a P i 0 z = variationFeature O a P i 0 z ∧
    variationRetractedFeatureFirst O a P i 0 z = variationFeatureFirst O a P i 0 z ∧
    variationRetractedFeatureSecond O a P i 0 z = variationFeatureSecond O a P i 0 z := by
  letI : IsProbabilityMeasure (P.measure i) := (P.cap i).probability
  exact meanFeatureJetAlongRetract_initial_jets 0 O a (P.measure i) (P.velocity i)
    (P.tangent i) (P.continuous_velocity i) z

noncomputable def variationRetractedFittingBound {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (z : Weight d) : Real :=
  12*(variationRetractedFeatureBound O a P z)^4

theorem variationRetractedFittingBound_integrable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) :
    Integrable (variationRetractedFittingBound O a P) (stdGaussian (Weight d)) := by
  have hi := (fittingFeatureEnvelope_gaussian_integrable (d := d) O a (6*variationSpeedScale P) 4).const_mul 12
  change Integrable (fun z : Weight d => 12*(6*(variationSpeedScale P*fittingFeatureEnvelope O a z))^4)
    (stdGaussian (Weight d))
  simpa only [mul_assoc] using hi

end PaperFormalization.MatrixFactorization
