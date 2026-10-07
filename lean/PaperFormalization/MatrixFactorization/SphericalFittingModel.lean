import PaperFormalization.MatrixFactorization.FittingEnvelope
import PaperFormalization.MatrixFactorization.FittingBounds
import PaperFormalization.MatrixFactorization.ModelEndpoints
import PaperFormalization.MatrixFactorization.SphericalRegularizer

/-! # MF04: original spherical fitting paths and a uniform Gaussian bound

The student features are taken from the actual EXP-pushed probability measures.
The scale below depends only on the two original speed moments. It is finite
because the tangent fields are continuous on the compact sphere. No fitting
derivative or Gaussian integrability is supplied as a model hypothesis.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def variationSpeedScale {d : Nat} (P : SphericalVariation d) : Real :=
  1 + (∑ i : Fin 2, ∫ w, norm (P.velocity i w) ∂P.measure i) + variationEnergy P

theorem variationSpeedScale_bounds {d : Nat} (P : SphericalVariation d) (i : Fin 2) :
    1 ≤ variationSpeedScale P ∧
    (∫ w, norm (P.velocity i w) ∂P.measure i) ≤ variationSpeedScale P ∧
    (∫ w, norm (P.velocity i w)^2 ∂P.measure i) ≤ variationSpeedScale P := by
  have h1 (j : Fin 2) : 0 ≤ ∫ w, norm (P.velocity j w) ∂P.measure j :=
    integral_nonneg (fun w => norm_nonneg _)
  have h2 (j : Fin 2) : 0 ≤ ∫ w, norm (P.velocity j w)^2 ∂P.measure j :=
    integral_nonneg (fun w => sq_nonneg _)
  have hs1 := Finset.sum_nonneg (s := Finset.univ) (fun j _ => h1 j)
  have hs2 := variationEnergy_nonneg P
  have hi1 := Finset.single_le_sum (f := fun j : Fin 2 => ∫ w, norm (P.velocity j w) ∂P.measure j)
    (fun j _ => h1 j) (Finset.mem_univ i)
  have hi2 : (∫ w, norm (P.velocity i w)^2 ∂P.measure i) ≤ variationEnergy P :=
    Finset.single_le_sum (fun j _ => h2 j) (Finset.mem_univ i)
  unfold variationSpeedScale
  exact ⟨by linarith, by linarith, by linarith⟩

noncomputable def variationFeature {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (i : Fin 2) (t : Real) (z : Weight d) : Weight h :=
  meanFeatureJetAlongExp 0 O a (P.measure i) (P.velocity i) (P.tangent i) z t

noncomputable def variationFeatureFirst {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (i : Fin 2) (t : Real) (z : Weight d) : Weight h :=
  meanFeatureJetAlongExpFirst 0 O a (P.measure i) (P.velocity i) (P.tangent i) z t

noncomputable def variationFeatureSecond {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (i : Fin 2) (t : Real) (z : Weight d) : Weight h :=
  meanFeatureJetAlongExpSecond 0 O a (P.measure i) (P.velocity i) (P.tangent i) z t

noncomputable def teacherOutput {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (teacher1 teacher2 : Measure (UnitSphere d)) (z : Weight d) : Output h :=
  outer (meanFeature (finiteHermiteActivation O a) teacher1 z)
    (meanFeature (finiteHermiteActivation O a) teacher2 z)

noncomputable def variationFeatureBound {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (z : Weight d) : Real :=
  variationSpeedScale P * fittingFeatureEnvelope O a z

theorem variationFeatureBound_nonneg {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (z : Weight d) :
    0 ≤ variationFeatureBound O a P z :=
  mul_nonneg (le_trans (by norm_num) (variationSpeedScale_bounds P 0).1)
    (fittingFeatureEnvelope_nonneg O a z)

theorem variationFeature_bounds {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (i : Fin 2) (t : Real) (z : Weight d) :
    norm (variationFeature O a P i t z) ≤ variationFeatureBound O a P z ∧
    norm (variationFeatureFirst O a P i t z) ≤ variationFeatureBound O a P z ∧
    norm (variationFeatureSecond O a P i t z) ≤ variationFeatureBound O a P z := by
  letI : IsProbabilityMeasure (P.measure i) := (P.cap i).probability
  have hb := meanFeatureAlongExp_bounds 0 O a (P.measure i) (P.velocity i) (P.tangent i)
    (P.continuous_velocity i) z t
  have he := fittingFeatureEnvelope_bounds O a z
  have hs := variationSpeedScale_bounds P i
  have hS : 0 ≤ variationSpeedScale P := le_trans (by norm_num) hs.1
  refine ⟨?_, ?_, ?_⟩
  · exact (hb.1.trans he.1).trans (le_mul_of_one_le_left (fittingFeatureEnvelope_nonneg O a z) hs.1)
  · exact hb.2.1.trans (mul_le_mul hs.2.1 he.2.1
      (featureFirstEnvelope_nonneg 0 O a z) hS)
  · exact hb.2.2.trans (mul_le_mul hs.2.2 he.2.2.1
      (featureSecondEnvelope_nonneg 0 O a z) hS)

theorem teacherOutput_bound {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (z : Weight d) :
    norm (teacherOutput O a teacher1 teacher2 z) ≤ (variationFeatureBound O a P z)^2 := by
  have hb (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] :
      norm (meanFeature (finiteHermiteActivation O a) mu z) ≤ variationFeatureBound O a P z :=
    ((finiteHermite_mean_growth O a mu z).trans (fittingFeatureEnvelope_bounds O a z).2.2.2).trans
      (le_mul_of_one_le_left (fittingFeatureEnvelope_nonneg O a z) (variationSpeedScale_bounds P 0).1)
  rw [teacherOutput, outer_norm, pow_two]
  exact mul_le_mul (hb teacher1) (hb teacher2) (norm_nonneg _) (variationFeatureBound_nonneg O a P z)

theorem variationFeature_stronglyMeasurable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (i : Fin 2) (t : Real) :
    StronglyMeasurable (variationFeature O a P i t) ∧
    StronglyMeasurable (variationFeatureFirst O a P i t) ∧
    StronglyMeasurable (variationFeatureSecond O a P i t) := by
  letI : IsProbabilityMeasure (P.measure i) := (P.cap i).probability
  exact meanFeatureAlongExp_stronglyMeasurable 0 O a (P.measure i) (P.velocity i)
    (P.tangent i) (P.continuous_velocity i) t

theorem teacherOutput_stronglyMeasurable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    StronglyMeasurable (teacherOutput O a teacher1 teacher2) :=
  outer_stronglyMeasurable _ _
    (meanFeature_stronglyMeasurable _ (finiteHermiteActivation_continuous O a) teacher1)
    (meanFeature_stronglyMeasurable _ (finiteHermiteActivation_continuous O a) teacher2)

theorem variationFeature_variations {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (i : Fin 2) (t : Real) (z : Weight d) :
    HasDerivAt (fun s => variationFeature O a P i s z) (variationFeatureFirst O a P i t z) t ∧
    HasDerivAt (fun s => variationFeatureFirst O a P i s z) (variationFeatureSecond O a P i t z) t := by
  letI : IsProbabilityMeasure (P.measure i) := (P.cap i).probability
  exact meanFeatureJetAlongExp_variations 0 O a (P.measure i) (P.velocity i)
    (P.tangent i) (P.continuous_velocity i) z t

/-- The matrix loss and both derivative integrands share this Gaussian bound. -/
noncomputable def variationFittingBound {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (z : Weight d) : Real :=
  12*(variationFeatureBound O a P z)^4

theorem variationFittingBound_integrable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) :
    Integrable (variationFittingBound O a P) (stdGaussian (Weight d)) :=
  (fittingFeatureEnvelope_gaussian_integrable O a (variationSpeedScale P) 4).const_mul 12

end PaperFormalization.MatrixFactorization
