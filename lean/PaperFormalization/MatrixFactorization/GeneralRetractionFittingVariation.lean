import PaperFormalization.MatrixFactorization.GeneralRetractionFittingModel
import PaperFormalization.MatrixFactorization.TransverseObjectiveExpansion

/-! # The actual Gaussian fit along general normalized spherical paths

Both Gaussian derivatives are proved from the actual normalized feature
integrals and uniform Gaussian bounds. The initial derivatives agree with the
previously verified EXP path for the same original measures and tangent field.
-/
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def variationRetractedMatrixLoss {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d))
    (t : Real) (z : Weight d) : Real :=
  matrixPointLoss (teacherOutput O a teacher1 teacher2 z)
    (variationRetractedFeature O a P 0 t z) (variationRetractedFeature O a P 1 t z)

noncomputable def variationRetractedMatrixFirst {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d))
    (t : Real) (z : Weight d) : Real :=
  matrixPointFirst (teacherOutput O a teacher1 teacher2 z)
    (variationRetractedFeature O a P 0 t z) (variationRetractedFeature O a P 1 t z)
    (variationRetractedFeatureFirst O a P 0 t z) (variationRetractedFeatureFirst O a P 1 t z)

noncomputable def variationRetractedMatrixSecond {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d))
    (t : Real) (z : Weight d) : Real :=
  matrixPointSecond (teacherOutput O a teacher1 teacher2 z)
    (variationRetractedFeature O a P 0 t z) (variationRetractedFeature O a P 1 t z)
    (variationRetractedFeatureFirst O a P 0 t z) (variationRetractedFeatureFirst O a P 1 t z)
    (variationRetractedFeatureSecond O a P 0 t z) (variationRetractedFeatureSecond O a P 1 t z)

noncomputable def variationRetractedFitting {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d)) (t : Real) : Real :=
  modelFitting O a
    ((P.measure 0).map (sphericalRetractFamily (P.velocity 0) (P.tangent 0) t))
    ((P.measure 1).map (sphericalRetractFamily (P.velocity 1) (P.tangent 1) t)) teacher1 teacher2

noncomputable def variationRetractedFittingFirst {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d)) (t : Real) : Real :=
  ∫ z, variationRetractedMatrixFirst O a P teacher1 teacher2 t z ∂stdGaussian (Weight d)

noncomputable def variationRetractedFittingSecond {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d)) (t : Real) : Real :=
  ∫ z, variationRetractedMatrixSecond O a P teacher1 teacher2 t z ∂stdGaussian (Weight d)

/-- The normalization is exactly the original one-half squared Frobenius loss. -/
theorem variationRetractedFitting_integral {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d)) (t : Real) :
    variationRetractedFitting O a P teacher1 teacher2 t =
      ∫ z, variationRetractedMatrixLoss O a P teacher1 teacher2 t z ∂stdGaussian (Weight d) := by
  simp only [variationRetractedFitting, modelFitting, fittingEnergy, variationRetractedMatrixLoss,
    matrixPointLoss, teacherOutput, variationRetractedFeature, meanFeatureJetAlongRetract_zero_order,
    integral_div]
  ring

theorem variationRetractedMatrix_variations {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d)) (t : Real) (z : Weight d) :
    HasDerivAt (fun s => variationRetractedMatrixLoss O a P teacher1 teacher2 s z)
      (variationRetractedMatrixFirst O a P teacher1 teacher2 t z) t ∧
    HasDerivAt (fun s => variationRetractedMatrixFirst O a P teacher1 teacher2 s z)
      (variationRetractedMatrixSecond O a P teacher1 teacher2 t z) t := by
  have h0 := variationRetractedFeature_variations O a P 0 t z
  have h1 := variationRetractedFeature_variations O a P 1 t z
  exact ⟨matrixPointLoss_hasDerivAt _ h0.1 h1.1,
    matrixPointFirst_hasDerivAt _ h0.1 h1.1 h0.2 h1.2⟩

theorem variationRetractedMatrix_stronglyMeasurable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (t : Real) :
    StronglyMeasurable (variationRetractedMatrixLoss O a P teacher1 teacher2 t) ∧
    StronglyMeasurable (variationRetractedMatrixFirst O a P teacher1 teacher2 t) ∧
    StronglyMeasurable (variationRetractedMatrixSecond O a P teacher1 teacher2 t) := by
  have h0 := variationRetractedFeature_stronglyMeasurable O a P 0 t
  have h1 := variationRetractedFeature_stronglyMeasurable O a P 1 t
  exact matrixPoint_stronglyMeasurable _ _ _ _ _ _ _
    (teacherOutput_stronglyMeasurable O a teacher1 teacher2) h0.1 h1.1 h0.2.1 h1.2.1 h0.2.2 h1.2.2

theorem variationRetractedMatrix_uniform_bounds {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (t : Real) (z : Weight d) :
    norm (variationRetractedMatrixLoss O a P teacher1 teacher2 t z) ≤ variationRetractedFittingBound O a P z ∧
    norm (variationRetractedMatrixFirst O a P teacher1 teacher2 t z) ≤ variationRetractedFittingBound O a P z ∧
    norm (variationRetractedMatrixSecond O a P teacher1 teacher2 t z) ≤ variationRetractedFittingBound O a P z := by
  have h0 := variationRetractedFeature_bounds O a P 0 t z
  have h1 := variationRetractedFeature_bounds O a P 1 t z
  have hb := matrixPoint_uniform_bounds (teacherOutput O a teacher1 teacher2 z)
    _ _ _ _ _ _ (variationRetractedFeatureBound O a P z) (variationRetractedFeatureBound_nonneg O a P z)
    (teacherOutput_retracted_bound O a P teacher1 teacher2 z) h0.1 h1.1 h0.2.1 h1.2.1 h0.2.2 h1.2.2
  have hn : 0 ≤ (variationRetractedFeatureBound O a P z)^4 := by positivity
  exact ⟨hb.1.trans (by unfold variationRetractedFittingBound; linarith),
    hb.2.1.trans (by unfold variationRetractedFittingBound; linarith), hb.2.2⟩

theorem variationRetractedMatrix_integrable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (t : Real) :
    Integrable (variationRetractedMatrixLoss O a P teacher1 teacher2 t) (stdGaussian (Weight d)) ∧
    Integrable (variationRetractedMatrixFirst O a P teacher1 teacher2 t) (stdGaussian (Weight d)) ∧
    Integrable (variationRetractedMatrixSecond O a P teacher1 teacher2 t) (stdGaussian (Weight d)) := by
  have hm := variationRetractedMatrix_stronglyMeasurable O a P teacher1 teacher2 t
  have hb := variationRetractedMatrix_uniform_bounds O a P teacher1 teacher2 t
  have hi := variationRetractedFittingBound_integrable O a P
  exact ⟨hi.mono' hm.1.aestronglyMeasurable (Eventually.of_forall (fun z => (hb z).1)),
    hi.mono' hm.2.1.aestronglyMeasurable (Eventually.of_forall (fun z => (hb z).2.1)),
    hi.mono' hm.2.2.aestronglyMeasurable (Eventually.of_forall (fun z => (hb z).2.2))⟩

/-- Both Gaussian derivative exchanges are derived, at every signed time. -/
theorem variationRetractedFitting_variations {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (t : Real) :
    HasDerivAt (variationRetractedFitting O a P teacher1 teacher2)
      (variationRetractedFittingFirst O a P teacher1 teacher2 t) t ∧
    HasDerivAt (variationRetractedFittingFirst O a P teacher1 teacher2)
      (variationRetractedFittingSecond O a P teacher1 teacher2 t) t := by
  have hi := variationRetractedMatrix_integrable O a P teacher1 teacher2 t
  have hm := variationRetractedMatrix_stronglyMeasurable O a P teacher1 teacher2
  have hb := variationRetractedMatrix_uniform_bounds O a P teacher1 teacher2
  have hd := variationRetractedMatrix_variations O a P teacher1 teacher2
  have hbound := variationRetractedFittingBound_integrable O a P
  have hfirst := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := variationRetractedMatrixLoss O a P teacher1 teacher2)
    (F' := variationRetractedMatrixFirst O a P teacher1 teacher2)
    (bound := variationRetractedFittingBound O a P) (s := Set.univ) (x₀ := t) Filter.univ_mem
    (Eventually.of_forall (fun s => (hm s).1.aestronglyMeasurable)) hi.1
    (hm t).2.1.aestronglyMeasurable
    (Eventually.of_forall (fun z s _ => (hb s z).2.1)) hbound
    (Eventually.of_forall (fun z s _ => (hd s z).1))
  have hsecond := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := variationRetractedMatrixFirst O a P teacher1 teacher2)
    (F' := variationRetractedMatrixSecond O a P teacher1 teacher2)
    (bound := variationRetractedFittingBound O a P) (s := Set.univ) (x₀ := t) Filter.univ_mem
    (Eventually.of_forall (fun s => (hm s).2.1.aestronglyMeasurable)) hi.2.1
    (hm t).2.2.aestronglyMeasurable
    (Eventually.of_forall (fun z s _ => (hb s z).2.2)) hbound
    (Eventually.of_forall (fun z s _ => (hd s z).2))
  have he : variationRetractedFitting O a P teacher1 teacher2 =
      (fun s => ∫ z, variationRetractedMatrixLoss O a P teacher1 teacher2 s z ∂stdGaussian (Weight d)) :=
    funext (variationRetractedFitting_integral O a P teacher1 teacher2)
  exact ⟨he ▸ hfirst.2, hsecond.2⟩

/-- Source-facing second variation of the actual spherical Gaussian fit term. -/
theorem normalized_fitting_source_variations {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (t : Real) :
    HasDerivAt (variationRetractedFitting O a P teacher1 teacher2)
      (variationRetractedFittingFirst O a P teacher1 teacher2 t) t ∧
    HasDerivAt (deriv (variationRetractedFitting O a P teacher1 teacher2))
      (variationRetractedFittingSecond O a P teacher1 teacher2 t) t := by
  have he : deriv (variationRetractedFitting O a P teacher1 teacher2) = variationRetractedFittingFirst O a P teacher1 teacher2 := by
    funext s
    exact (variationRetractedFitting_variations O a P teacher1 teacher2 s).1.deriv
  rw [he]
  exact variationRetractedFitting_variations O a P teacher1 teacher2 t

theorem variationRetractedMatrix_initial_jets {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d))
    (z : Weight d) :
    variationRetractedMatrixLoss O a P teacher1 teacher2 0 z = variationMatrixLoss O a P teacher1 teacher2 0 z ∧
    variationRetractedMatrixFirst O a P teacher1 teacher2 0 z = variationMatrixFirst O a P teacher1 teacher2 0 z ∧
    variationRetractedMatrixSecond O a P teacher1 teacher2 0 z = variationMatrixSecond O a P teacher1 teacher2 0 z := by
  have h0 := variationRetractedFeature_initial_jets O a P 0 z
  have h1 := variationRetractedFeature_initial_jets O a P 1 z
  simp only [variationRetractedMatrixLoss, variationMatrixLoss, variationRetractedMatrixFirst,
    variationMatrixFirst, variationRetractedMatrixSecond, variationMatrixSecond,
    h0.1, h1.1, h0.2.1, h1.2.1, h0.2.2, h1.2.2, and_self]

theorem variationRetractedFitting_initial_jets {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d)) :
    variationRetractedFitting O a P teacher1 teacher2 0 = variationFitting O a P teacher1 teacher2 0 ∧
    variationRetractedFittingFirst O a P teacher1 teacher2 0 = variationFittingFirst O a P teacher1 teacher2 0 ∧
    variationRetractedFittingSecond O a P teacher1 teacher2 0 = variationFittingSecond O a P teacher1 teacher2 0 := by
  simp only [variationRetractedFitting_integral, variationFitting_integral,
    variationRetractedFittingFirst, variationFittingFirst, variationRetractedFittingSecond, variationFittingSecond]
  refine ⟨integral_congr_ae ?_, integral_congr_ae ?_, integral_congr_ae ?_⟩
  · exact Eventually.of_forall (fun z => (variationRetractedMatrix_initial_jets O a P teacher1 teacher2 z).1)
  · exact Eventually.of_forall (fun z => (variationRetractedMatrix_initial_jets O a P teacher1 teacher2 z).2.1)
  · exact Eventually.of_forall (fun z => (variationRetractedMatrix_initial_jets O a P teacher1 teacher2 z).2.2)

/-- Equality of the first two fitting derivatives is proved after both actual
Gaussian exchanges, rather than by integrating pointwise little-o terms. -/
theorem variationRetractedFitting_initial_variations {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    HasDerivAt (variationRetractedFitting O a P teacher1 teacher2)
      (variationFittingFirst O a P teacher1 teacher2 0) 0 ∧
    HasDerivAt (deriv (variationRetractedFitting O a P teacher1 teacher2))
      (variationFittingSecond O a P teacher1 teacher2 0) 0 := by
  have hd := normalized_fitting_source_variations O a P teacher1 teacher2 0
  have hj := variationRetractedFitting_initial_jets O a P teacher1 teacher2
  exact ⟨hd.1.congr_deriv hj.2.1, hd.2.congr_deriv hj.2.2⟩

theorem variationRetractedFitting_derivatives_eq_exp {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    deriv (variationRetractedFitting O a P teacher1 teacher2) 0 =
      deriv (variationFitting O a P teacher1 teacher2) 0 ∧
    deriv (deriv (variationRetractedFitting O a P teacher1 teacher2)) 0 =
      deriv (deriv (variationFitting O a P teacher1 teacher2)) 0 := by
  have hr := variationRetractedFitting_initial_variations O a P teacher1 teacher2
  have he := spherical_fitting_source_variations O a P teacher1 teacher2 0
  exact ⟨hr.1.deriv.trans he.1.deriv.symm, hr.2.deriv.trans he.2.deriv.symm⟩

/-- The complete Gaussian fitting losses agree to second order for every
original cap state and continuous tangent field, including zero speed. -/
theorem variationRetractedFitting_sub_exp_littleO {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    (fun t => variationRetractedFitting O a P teacher1 teacher2 t -
      variationFitting O a P teacher1 teacher2 t) =o[𝓝 (0 : Real)] (fun t => t^2) := by
  let R := variationRetractedFitting O a P teacher1 teacher2
  let E := variationFitting O a P teacher1 teacher2
  have hR := variationRetractedFitting_initial_variations O a P teacher1 teacher2
  have hE := spherical_fitting_source_variations O a P teacher1 teacher2 0
  have hfirst : HasDerivAt (fun t => R t-E t) 0 0 :=
    (hR.1.sub hE.1).congr_deriv (sub_self _)
  have heq : deriv (fun t => R t-E t) = (fun t => deriv R t-deriv E t) := by
    funext t
    exact deriv_sub (variationRetractedFitting_variations O a P teacher1 teacher2 t).1.differentiableAt
      (variationFitting_variations O a P teacher1 teacher2 t).1.differentiableAt
  have hsecond : HasDerivAt (deriv (fun t => R t-E t)) 0 0 := by
    rw [heq]
    exact (hR.2.sub hE.2).congr_deriv (sub_self _)
  have hnear : ∀ᶠ t in 𝓝 (0 : Real), DifferentiableAt Real (fun u => R u-E u) t :=
    Eventually.of_forall (fun t =>
      (variationRetractedFitting_variations O a P teacher1 teacher2 t).1.differentiableAt.sub
        (variationFitting_variations O a P teacher1 teacher2 t).1.differentiableAt)
  have hp := peano_second_at_zero (fun t => R t-E t) 0 hfirst hsecond hnear
  have hz : R 0 = E 0 := (variationRetractedFitting_initial_jets O a P teacher1 teacher2).1
  simpa only [hz, sub_self, sub_zero, zero_div, zero_mul] using hp

end PaperFormalization.MatrixFactorization
