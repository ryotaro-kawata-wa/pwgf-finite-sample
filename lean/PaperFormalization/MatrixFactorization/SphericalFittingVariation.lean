import PaperFormalization.MatrixFactorization.SphericalFittingModel

/-! # MF04: two Gaussian differentiations of the actual spherical fitting loss

Both integrations are justified from the original finite activation, probability
measures, and continuous tangent fields. The endpoint differentiates the actual
EXP-pushed modelFitting and retains the full residual term in its second
variation. It does not assume a fitting derivative or claim any of the four
local geometric results of the manuscript.
-/
open MeasureTheory ProbabilityTheory Filter Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def variationMatrixLoss {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d))
    (t : Real) (z : Weight d) : Real :=
  matrixPointLoss (teacherOutput O a teacher1 teacher2 z)
    (variationFeature O a P 0 t z) (variationFeature O a P 1 t z)

noncomputable def variationMatrixFirst {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d))
    (t : Real) (z : Weight d) : Real :=
  matrixPointFirst (teacherOutput O a teacher1 teacher2 z)
    (variationFeature O a P 0 t z) (variationFeature O a P 1 t z)
    (variationFeatureFirst O a P 0 t z) (variationFeatureFirst O a P 1 t z)

noncomputable def variationMatrixSecond {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d))
    (t : Real) (z : Weight d) : Real :=
  matrixPointSecond (teacherOutput O a teacher1 teacher2 z)
    (variationFeature O a P 0 t z) (variationFeature O a P 1 t z)
    (variationFeatureFirst O a P 0 t z) (variationFeatureFirst O a P 1 t z)
    (variationFeatureSecond O a P 0 t z) (variationFeatureSecond O a P 1 t z)

noncomputable def variationFitting {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d)) (t : Real) : Real :=
  modelFitting O a
    ((P.measure 0).map (sphericalExpFamily (P.velocity 0) (P.tangent 0) t))
    ((P.measure 1).map (sphericalExpFamily (P.velocity 1) (P.tangent 1) t)) teacher1 teacher2

noncomputable def variationFittingFirst {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d)) (t : Real) : Real :=
  ∫ z, variationMatrixFirst O a P teacher1 teacher2 t z ∂stdGaussian (Weight d)

noncomputable def variationFittingSecond {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d)) (t : Real) : Real :=
  ∫ z, variationMatrixSecond O a P teacher1 teacher2 t z ∂stdGaussian (Weight d)

/-- The normalization is exactly the original one-half squared Frobenius loss. -/
theorem variationFitting_integral {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d)) (t : Real) :
    variationFitting O a P teacher1 teacher2 t =
      ∫ z, variationMatrixLoss O a P teacher1 teacher2 t z ∂stdGaussian (Weight d) := by
  simp only [variationFitting, modelFitting, fittingEnergy, variationMatrixLoss,
    matrixPointLoss, teacherOutput, variationFeature, meanFeatureJetAlongExp_zero_order,
    integral_div]
  ring

theorem variationMatrix_variations {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d)) (t : Real) (z : Weight d) :
    HasDerivAt (fun s => variationMatrixLoss O a P teacher1 teacher2 s z)
      (variationMatrixFirst O a P teacher1 teacher2 t z) t ∧
    HasDerivAt (fun s => variationMatrixFirst O a P teacher1 teacher2 s z)
      (variationMatrixSecond O a P teacher1 teacher2 t z) t := by
  have h0 := variationFeature_variations O a P 0 t z
  have h1 := variationFeature_variations O a P 1 t z
  exact ⟨matrixPointLoss_hasDerivAt _ h0.1 h1.1,
    matrixPointFirst_hasDerivAt _ h0.1 h1.1 h0.2 h1.2⟩

theorem variationMatrix_stronglyMeasurable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (t : Real) :
    StronglyMeasurable (variationMatrixLoss O a P teacher1 teacher2 t) ∧
    StronglyMeasurable (variationMatrixFirst O a P teacher1 teacher2 t) ∧
    StronglyMeasurable (variationMatrixSecond O a P teacher1 teacher2 t) := by
  have h0 := variationFeature_stronglyMeasurable O a P 0 t
  have h1 := variationFeature_stronglyMeasurable O a P 1 t
  exact matrixPoint_stronglyMeasurable _ _ _ _ _ _ _
    (teacherOutput_stronglyMeasurable O a teacher1 teacher2) h0.1 h1.1 h0.2.1 h1.2.1 h0.2.2 h1.2.2

theorem variationMatrix_uniform_bounds {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (t : Real) (z : Weight d) :
    norm (variationMatrixLoss O a P teacher1 teacher2 t z) ≤ variationFittingBound O a P z ∧
    norm (variationMatrixFirst O a P teacher1 teacher2 t z) ≤ variationFittingBound O a P z ∧
    norm (variationMatrixSecond O a P teacher1 teacher2 t z) ≤ variationFittingBound O a P z := by
  have h0 := variationFeature_bounds O a P 0 t z
  have h1 := variationFeature_bounds O a P 1 t z
  have hb := matrixPoint_uniform_bounds (teacherOutput O a teacher1 teacher2 z)
    _ _ _ _ _ _ (variationFeatureBound O a P z) (variationFeatureBound_nonneg O a P z)
    (teacherOutput_bound O a P teacher1 teacher2 z) h0.1 h1.1 h0.2.1 h1.2.1 h0.2.2 h1.2.2
  have hn : 0 ≤ (variationFeatureBound O a P z)^4 := by positivity
  exact ⟨hb.1.trans (by unfold variationFittingBound; linarith),
    hb.2.1.trans (by unfold variationFittingBound; linarith), hb.2.2⟩

theorem variationMatrix_integrable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (t : Real) :
    Integrable (variationMatrixLoss O a P teacher1 teacher2 t) (stdGaussian (Weight d)) ∧
    Integrable (variationMatrixFirst O a P teacher1 teacher2 t) (stdGaussian (Weight d)) ∧
    Integrable (variationMatrixSecond O a P teacher1 teacher2 t) (stdGaussian (Weight d)) := by
  have hm := variationMatrix_stronglyMeasurable O a P teacher1 teacher2 t
  have hb := variationMatrix_uniform_bounds O a P teacher1 teacher2 t
  have hi := variationFittingBound_integrable O a P
  exact ⟨hi.mono' hm.1.aestronglyMeasurable (Eventually.of_forall (fun z => (hb z).1)),
    hi.mono' hm.2.1.aestronglyMeasurable (Eventually.of_forall (fun z => (hb z).2.1)),
    hi.mono' hm.2.2.aestronglyMeasurable (Eventually.of_forall (fun z => (hb z).2.2))⟩

/-- Both Gaussian derivative exchanges are derived, at every signed time. -/
theorem variationFitting_variations {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (t : Real) :
    HasDerivAt (variationFitting O a P teacher1 teacher2)
      (variationFittingFirst O a P teacher1 teacher2 t) t ∧
    HasDerivAt (variationFittingFirst O a P teacher1 teacher2)
      (variationFittingSecond O a P teacher1 teacher2 t) t := by
  have hi := variationMatrix_integrable O a P teacher1 teacher2 t
  have hm := variationMatrix_stronglyMeasurable O a P teacher1 teacher2
  have hb := variationMatrix_uniform_bounds O a P teacher1 teacher2
  have hd := variationMatrix_variations O a P teacher1 teacher2
  have hbound := variationFittingBound_integrable O a P
  have hfirst := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := variationMatrixLoss O a P teacher1 teacher2)
    (F' := variationMatrixFirst O a P teacher1 teacher2)
    (bound := variationFittingBound O a P) (s := Set.univ) (x₀ := t) Filter.univ_mem
    (Eventually.of_forall (fun s => (hm s).1.aestronglyMeasurable)) hi.1
    (hm t).2.1.aestronglyMeasurable
    (Eventually.of_forall (fun z s _ => (hb s z).2.1)) hbound
    (Eventually.of_forall (fun z s _ => (hd s z).1))
  have hsecond := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := variationMatrixFirst O a P teacher1 teacher2)
    (F' := variationMatrixSecond O a P teacher1 teacher2)
    (bound := variationFittingBound O a P) (s := Set.univ) (x₀ := t) Filter.univ_mem
    (Eventually.of_forall (fun s => (hm s).2.1.aestronglyMeasurable)) hi.2.1
    (hm t).2.2.aestronglyMeasurable
    (Eventually.of_forall (fun z s _ => (hb s z).2.2)) hbound
    (Eventually.of_forall (fun z s _ => (hd s z).2))
  have he : variationFitting O a P teacher1 teacher2 =
      (fun s => ∫ z, variationMatrixLoss O a P teacher1 teacher2 s z ∂stdGaussian (Weight d)) :=
    funext (variationFitting_integral O a P teacher1 teacher2)
  exact ⟨he ▸ hfirst.2, hsecond.2⟩

/-- Source-facing second variation of the actual spherical Gaussian fit term. -/
theorem spherical_fitting_source_variations {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (t : Real) :
    HasDerivAt (variationFitting O a P teacher1 teacher2)
      (variationFittingFirst O a P teacher1 teacher2 t) t ∧
    HasDerivAt (deriv (variationFitting O a P teacher1 teacher2))
      (variationFittingSecond O a P teacher1 teacher2 t) t := by
  have he : deriv (variationFitting O a P teacher1 teacher2) = variationFittingFirst O a P teacher1 teacher2 := by
    funext s
    exact (variationFitting_variations O a P teacher1 teacher2 s).1.deriv
  rw [he]
  exact variationFitting_variations O a P teacher1 teacher2 t

end PaperFormalization.MatrixFactorization
