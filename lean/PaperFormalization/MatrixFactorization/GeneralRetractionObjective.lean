import PaperFormalization.MatrixFactorization.GeneralRetractionFittingVariation
import PaperFormalization.MatrixFactorization.GeneralRetractionRegularizerFlat
import PaperFormalization.MatrixFactorization.SphericalObjectiveAnnulus
import PaperFormalization.MatrixFactorization.SphericalObjectiveTeacher

/-! # MF10: general normalized paths and the original full objective

Both original-measure and Gaussian differentiation exchanges precede this
closure. For arbitrary initial cap states and continuous tangent fields, the
literal normalized pushforwards have the same initial objective derivatives
as EXP, and their complete objectives differ by o(t^2). The inherited annular
constant is the existing coarse sufficient constant.
-/
open MeasureTheory Set Filter Asymptotics
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

theorem variationRetractedObjective_split {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (lambda p : Real)
    (teacher1 teacher2 : Measure (UnitSphere d)) (t : Real) :
    variationRetractedObjective O a P lambda p teacher1 teacher2 t =
      variationRetractedFitting O a P teacher1 teacher2 t +
        variationRetractedRegularizer P lambda p t := rfl

@[simp] theorem variationRetractedObjective_zero {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (lambda p : Real)
    (teacher1 teacher2 : Measure (UnitSphere d)) :
    variationRetractedObjective O a P lambda p teacher1 teacher2 0 =
      variationObjective O a P lambda p teacher1 teacher2 0 := by
  have hr (i : Fin 2) : sphericalRetractFamily (P.velocity i) (P.tangent i) 0 = id :=
    funext (sphericalRetractFamily_zero (P.velocity i) (P.tangent i))
  have he (i : Fin 2) : sphericalExpFamily (P.velocity i) (P.tangent i) 0 = id :=
    funext (sphericalExpFamily_zero (P.velocity i) (P.tangent i))
  simp only [variationRetractedObjective, variationObjective, hr, he]

theorem variationRetractedObjective_differentiable_near {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (lambda p : Real) (hp : 2 < p)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    ∀ᶠ t in 𝓝 (0 : Real),
      DifferentiableAt Real (variationRetractedObjective O a P lambda p teacher1 teacher2) t := by
  filter_upwards [variationRetractedRegularizer_differentiable_near P lambda p hp] with t ht
  exact (variationRetractedFitting_variations O a P teacher1 teacher2 t).1.differentiableAt.add ht

theorem variationRetractedObjective_deriv_near {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (lambda p : Real) (hp : 2 < p)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    deriv (variationRetractedObjective O a P lambda p teacher1 teacher2) =ᶠ[𝓝 (0 : Real)]
      (fun t => deriv (variationRetractedFitting O a P teacher1 teacher2) t +
        deriv (variationRetractedRegularizer P lambda p) t) := by
  filter_upwards [variationRetractedRegularizer_differentiable_near P lambda p hp] with t ht
  exact deriv_add
    (variationRetractedFitting_variations O a P teacher1 teacher2 t).1.differentiableAt ht

/-- Positive-distance derivatives retain the original gradient and Hessian coefficients. -/
theorem normalized_objective_positive_variations {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (lambda p : Real)
    (hp : 2 < p) (hZ : 0 < variationTransport P 0)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    HasDerivAt (variationRetractedObjective O a P lambda p teacher1 teacher2)
      (variationFittingFirst O a P teacher1 teacher2 0 +
        lambda*(variationTransport P 0)^(p/2-1)*variationFirst P) 0 ∧
    HasDerivAt (deriv (variationRetractedObjective O a P lambda p teacher1 teacher2))
      (variationFittingSecond O a P teacher1 teacher2 0 +
        (lambda*(variationTransport P 0)^(p/2-1)*variationSecond P +
          lambda*(p-2)*(variationTransport P 0)^(p/2-2)*(variationFirst P)^2)) 0 := by
  have hf := variationRetractedFitting_initial_variations O a P teacher1 teacher2
  have hr := metricRegularizer_retracted_positive_variations P lambda p hp hZ
  exact ⟨hf.1.add hr.1, (hf.2.add hr.2).congr_of_eventuallyEq
    (variationRetractedObjective_deriv_near O a P lambda p hp teacher1 teacher2)⟩

/-- At zero target distance the normalized regularizer has zero first and second jets. -/
theorem normalized_objective_zero_variations {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (lambda p : Real)
    (hp : 2 < p) (hZ : variationTransport P 0 = 0)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    HasDerivAt (variationRetractedObjective O a P lambda p teacher1 teacher2)
      (variationFittingFirst O a P teacher1 teacher2 0) 0 ∧
    HasDerivAt (deriv (variationRetractedObjective O a P lambda p teacher1 teacher2))
      (variationFittingSecond O a P teacher1 teacher2 0) 0 := by
  have hf := variationRetractedFitting_initial_variations O a P teacher1 teacher2
  have hr := metricRegularizer_retracted_zero_variations P lambda p hp hZ
  constructor
  · exact (hf.1.add hr.1).congr_deriv (add_zero _)
  · exact ((hf.2.add hr.2).congr_deriv (add_zero _)).congr_of_eventuallyEq
      (variationRetractedObjective_deriv_near O a P lambda p hp teacher1 teacher2)

/-- The ordinary derivatives of the full normalized and EXP objectives coincide. -/
theorem variationRetractedObjective_derivatives_eq_exp {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (lambda p : Real)
    (hlambda : 0 < lambda) (hp : 2 < p)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    deriv (variationRetractedObjective O a P lambda p teacher1 teacher2) 0 =
      deriv (variationObjective O a P lambda p teacher1 teacher2) 0 ∧
    deriv (deriv (variationRetractedObjective O a P lambda p teacher1 teacher2)) 0 =
      deriv (deriv (variationObjective O a P lambda p teacher1 teacher2)) 0 := by
  rcases eq_or_lt_of_le (variationTransport_initial_nonneg P) with hz | hz
  · have hR := normalized_objective_zero_variations O a P lambda p hp hz.symm teacher1 teacher2
    have hE := spherical_objective_zero_variations O a P lambda p hp hz.symm teacher1 teacher2
    exact ⟨hR.1.deriv.trans hE.1.deriv.symm, hR.2.deriv.trans hE.2.deriv.symm⟩
  · have hR := normalized_objective_positive_variations O a P lambda p hp hz teacher1 teacher2
    have hE := spherical_objective_positive_variations O a P lambda p hlambda hp hz teacher1 teacher2
    exact ⟨hR.1.deriv.trans hE.1.deriv.symm, hR.2.deriv.trans hE.2.deriv.symm⟩

/-- The second-order comparison concerns the full integrated objective itself. -/
theorem variationRetractedObjective_sub_exp_littleO {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (lambda p : Real)
    (hlambda : 0 < lambda) (hp : 2 < p)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    (fun t => variationRetractedObjective O a P lambda p teacher1 teacher2 t -
      variationObjective O a P lambda p teacher1 teacher2 t) =o[𝓝 (0 : Real)] (fun t => t^2) := by
  let R := variationRetractedObjective O a P lambda p teacher1 teacher2
  let E := variationObjective O a P lambda p teacher1 teacher2
  have hj := variationRetractedObjective_derivatives_eq_exp O a P lambda p hlambda hp teacher1 teacher2
  have hRn := variationRetractedObjective_differentiable_near O a P lambda p hp teacher1 teacher2
  have hEn := variationObjective_differentiable_near O a P lambda p hp teacher1 teacher2
  have hR1 : DifferentiableAt Real R 0 := hRn.self_of_nhds
  have hE1 : DifferentiableAt Real E 0 := hEn.self_of_nhds
  have hR2 : DifferentiableAt Real (deriv R) 0 := by
    rcases eq_or_lt_of_le (variationTransport_initial_nonneg P) with hz | hz
    · exact (normalized_objective_zero_variations O a P lambda p hp hz.symm teacher1 teacher2).2.differentiableAt
    · exact (normalized_objective_positive_variations O a P lambda p hp hz teacher1 teacher2).2.differentiableAt
  have hE2 : DifferentiableAt Real (deriv E) 0 := by
    rcases eq_or_lt_of_le (variationTransport_initial_nonneg P) with hz | hz
    · exact (spherical_objective_zero_variations O a P lambda p hp hz.symm teacher1 teacher2).2.differentiableAt
    · exact (spherical_objective_positive_variations O a P lambda p hlambda hp hz teacher1 teacher2).2.differentiableAt
  have hfirst : HasDerivAt (fun t => R t-E t) 0 0 :=
    (hR1.hasDerivAt.sub hE1.hasDerivAt).congr_deriv (sub_eq_zero.mpr hj.1)
  have hder : deriv (fun t => R t-E t) =ᶠ[𝓝 (0 : Real)]
      (fun t => deriv R t-deriv E t) := by
    filter_upwards [hRn, hEn] with t hRt hEt
    exact deriv_sub hRt hEt
  have hsecond : HasDerivAt (deriv (fun t => R t-E t)) 0 0 :=
    ((hR2.hasDerivAt.sub hE2.hasDerivAt).congr_deriv
      (sub_eq_zero.mpr hj.2)).congr_of_eventuallyEq hder
  have hnear : ∀ᶠ t in 𝓝 (0 : Real), DifferentiableAt Real (fun u => R u-E u) t := by
    filter_upwards [hRn, hEn] with t hRt hEt
    exact hRt.sub hEt
  have hi := peano_second_at_zero (fun t => R t-E t) 0 hfirst hsecond hnear
  have hz : R 0 = E 0 := variationRetractedObjective_zero O a P lambda p teacher1 teacher2
  simpa only [hz, sub_self, sub_zero, zero_div, zero_mul] using hi

/-- This transfers the existing coarse sufficient curvature bound to normalized paths. -/
theorem normalized_objective_annular_lower {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (lambda p zeta : Real)
    (hlambda : 0 < lambda) (hp : 2 < p) (hzeta : 0 < zeta)
    (hZ : zeta^2 ≤ variationTransport P 0) (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    (lambda*sphericalRadialWeight P.radius*zeta^(p-2) - fittingCurvatureConstant d O a)*variationEnergy P ≤
      deriv (deriv (variationRetractedObjective O a P lambda p teacher1 teacher2)) 0 := by
  rw [(variationRetractedObjective_derivatives_eq_exp O a P lambda p hlambda hp teacher1 teacher2).2]
  exact spherical_objective_annular_lower O a P lambda p zeta hlambda hp hzeta hZ teacher1 teacher2

theorem normalized_objective_annular_pos {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (lambda p zeta : Real)
    (hlambda : 0 < lambda) (hp : 2 < p) (hzeta : 0 < zeta)
    (hZ : zeta^2 ≤ variationTransport P 0) (hE : 0 < variationEnergy P)
    (hthreshold : fittingCurvatureConstant d O a < lambda*sphericalRadialWeight P.radius*zeta^(p-2))
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    0 < deriv (deriv (variationRetractedObjective O a P lambda p teacher1 teacher2)) 0 :=
  (mul_pos (sub_pos.mpr hthreshold) hE).trans_le
    (normalized_objective_annular_lower O a P lambda p zeta hlambda hp hzeta hZ teacher1 teacher2)

/-- One finite sufficient threshold works for every admissible state and
continuous tangent direction at the fixed cap and annulus radii. -/
theorem normalized_annular_curvature_uniform {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (radius zeta p : Real) (hradius : 0 < radius)
    (hrpi : radius < Real.pi/2) (hzeta : 0 < zeta) (hp : 2 < p)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    ∃ L : Real, 0 < L ∧ ∀ lambda : Real, L < lambda →
      ∀ P : SphericalVariation d, P.radius = radius → zeta^2 ≤ variationTransport P 0 →
        0 < variationEnergy P →
        0 < deriv (deriv (variationRetractedObjective O a P lambda p teacher1 teacher2)) 0 := by
  obtain ⟨L, hL, hthreshold⟩ := fitting_annular_threshold_exists d O a (p := p) hradius.le hrpi hzeta
  refine ⟨L, hL, ?_⟩
  intro lambda hlambda P hr hZ hE
  apply normalized_objective_annular_pos O a P lambda p zeta (hL.trans hlambda) hp hzeta hZ hE
  simpa only [hr] using hthreshold lambda hlambda

/-- The exact-fit teacher lower bound holds along the original normalized
paths. A uniform neighborhood of the teacher is not asserted here. -/
theorem normalized_objective_teacher_second_lower {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (lambda p : Real)
    (hlambda : 0 < lambda) (hp : 2 < p) (hZ : 0 < variationTransport P 0) :
    lambda*(variationTransport P 0)^(p/2-1)*sphericalRadialWeight P.radius*variationEnergy P ≤
      deriv (deriv (variationRetractedObjective O a P lambda p (P.measure 0) (P.measure 1))) 0 := by
  letI : IsProbabilityMeasure (P.measure 0) := (P.cap 0).probability
  letI : IsProbabilityMeasure (P.measure 1) := (P.cap 1).probability
  rw [(variationRetractedObjective_derivatives_eq_exp O a P lambda p hlambda hp
    (P.measure 0) (P.measure 1)).2]
  exact spherical_objective_teacher_second_lower O a P lambda p hlambda hp hZ

/-- Strict teacher-point curvature is retained in every nonzero L2 direction. -/
theorem normalized_objective_teacher_second_pos {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (lambda p : Real)
    (hlambda : 0 < lambda) (hp : 2 < p) (hZ : 0 < variationTransport P 0)
    (hE : 0 < variationEnergy P) :
    0 < deriv (deriv (variationRetractedObjective O a P lambda p (P.measure 0) (P.measure 1))) 0 := by
  letI : IsProbabilityMeasure (P.measure 0) := (P.cap 0).probability
  letI : IsProbabilityMeasure (P.measure 1) := (P.cap 1).probability
  rw [(variationRetractedObjective_derivatives_eq_exp O a P lambda p hlambda hp
    (P.measure 0) (P.measure 1)).2]
  exact spherical_objective_teacher_second_pos O a P lambda p hlambda hp hZ hE

end PaperFormalization.MatrixFactorization
