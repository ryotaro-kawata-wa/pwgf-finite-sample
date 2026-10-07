import PaperFormalization.MatrixFactorization.PrimalACContinuousTests

/-! # MF26: time and weight regularity of the literal Gaussian fitting field

Verification status and conditional scope: see `MF26_VALIDATION.md`. All current-law dependence is through the actual mean
features. The fixed finite-Hermite polynomial envelope dominates the Gaussian
integrands uniformly in time and sphere weight. No field-continuity or field
measurability certificate is a new premise of the AC trajectory.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

/-- The two literal output gradients vary continuously along the current laws. -/
theorem PrimalACCharacteristicData.fittingOutputGradient_continuousOn_time
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (i : Fin 2) (z : Weight d) :
    ContinuousOn (fun t => fittingOutputGradient O a (X.measure 0 t) (X.measure 1 t)
      teacher teacher i z) (Ici (0 : Real)) := by
  have h0 := X.meanFeature_continuousOn_time hl hp 0 z
  have h1 := X.meanFeature_continuousOn_time hl hp 1 z
  unfold fittingOutputGradient
  split_ifs
  · exact ((h1.norm.pow 2).smul h0).sub
      ((continuousOn_const.inner (𝕜 := Real) h1).smul continuousOn_const)
  · exact ((h0.norm.pow 2).smul h1).sub
      ((continuousOn_const.inner (𝕜 := Real) h0).smul continuousOn_const)

/-- Before Gaussian integration, joint continuity uses only explicit formulas. -/
theorem PrimalACCharacteristicData.fittingGradientIntegrand_continuousOn
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (i : Fin 2) (z : Weight d) :
    ContinuousOn (fun tw : Real × UnitSphere d => fittingGradientIntegrand O a
      (X.measure 0 tw.1) (X.measure 1 tw.1) teacher teacher i tw.2 z)
      ((Ici (0 : Real)) ×ˢ (univ : Set (UnitSphere d))) := by
  have ho : ContinuousOn (fun tw : Real × UnitSphere d =>
      fittingOutputGradient O a (X.measure 0 tw.1) (X.measure 1 tw.1)
        teacher teacher i z) ((Ici (0 : Real)) ×ˢ (univ : Set (UnitSphere d))) :=
    (X.fittingOutputGradient_continuousOn_time hl hp i z).comp
    continuous_fst.continuousOn (fun tw htw => htw.1)
  have hj : Continuous (fun tw : Real × UnitSphere d =>
      finiteHermiteActivationJet 1 O a (inner Real tw.2.val z)) :=
    (finiteHermiteActivationJet_continuous 1 O a).comp (by fun_prop)
  have hproj : Continuous (fun tw : Real × UnitSphere d => transverseProjection tw.2 z) := by
    unfold transverseProjection
    fun_prop
  exact (ho.inner (𝕜 := Real) hj.continuousOn).smul hproj.continuousOn

/-- Dominated convergence supplies joint continuity of the genuine Gaussian
field on nonnegative times and ALL sphere weights, not only sampled points. -/
theorem PrimalACCharacteristicData.fittingGradient_continuousOn
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (i : Fin 2) :
    ContinuousOn (fun tw : Real × UnitSphere d => sphericalFittingGradient O a
      (X.measure 0 tw.1) (X.measure 1 tw.1) teacher teacher i tw.2)
      ((Ici (0 : Real)) ×ˢ (univ : Set (UnitSphere d))) := by
  have hdom : Integrable (fun z : Weight d => 4*(fittingFeatureEnvelope O a z)^4)
      (stdGaussian (Weight d)) := by
    simpa only [one_mul] using
      (fittingFeatureEnvelope_gaussian_integrable (d := d) O a 1 4).const_mul 4
  unfold sphericalFittingGradient
  apply continuousOn_of_dominated (bound := fun z => 4*(fittingFeatureEnvelope O a z)^4)
  · intro tw htw
    letI := X.measure_probability 0 tw.1
    letI := X.measure_probability 1 tw.1
    exact (fittingGradientIntegrand_integrable O a (X.measure 0 tw.1) (X.measure 1 tw.1)
      teacher teacher i tw.2).aestronglyMeasurable
  · intro tw htw
    letI := X.measure_probability 0 tw.1
    letI := X.measure_probability 1 tw.1
    exact Eventually.of_forall (fittingGradientIntegrand_norm_le O a
      (X.measure 0 tw.1) (X.measure 1 tw.1) teacher teacher i tw.2)
  · exact hdom
  · exact Eventually.of_forall (X.fittingGradientIntegrand_continuousOn hl hp i)

end PaperFormalization.MatrixFactorization
