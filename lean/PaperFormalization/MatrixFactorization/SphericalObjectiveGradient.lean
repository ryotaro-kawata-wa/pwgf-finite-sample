import PaperFormalization.MatrixFactorization.SphericalFittingGradientVariation
import PaperFormalization.MatrixFactorization.SphericalMetricGradient

/-! # The original full objective's spherical first-variation field

Both terms are functions of the original state. The Gaussian field is an
actual integral and the radial term is the gradient of the actual transport
regularizer. Their source pairings are proved before they are assembled.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def sphericalObjectiveGradient {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (lambda p : Real)
    (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d)) (i : Fin 2) (w : UnitSphere d) : Weight d :=
  sphericalFittingGradient O a mu1 mu2 teacher1 teacher2 i w +
    metricGradient pole lambda p mu1 mu2 w

theorem sphericalObjectiveGradient_tangent {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (lambda p : Real)
    (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure mu1] [IsProbabilityMeasure mu2]
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (i : Fin 2) (w : UnitSphere d) :
    inner Real w.val (sphericalObjectiveGradient O a pole lambda p mu1 mu2 teacher1 teacher2 i w) = 0 := by
  simp only [sphericalObjectiveGradient,inner_add_right,sphericalFittingGradient_tangent,
    metricGradient_tangent,add_zero]

theorem sphericalObjectiveGradient_measurable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (lambda p : Real)
    (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure mu1] [IsProbabilityMeasure mu2]
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (i : Fin 2) :
    Measurable (sphericalObjectiveGradient O a pole lambda p mu1 mu2 teacher1 teacher2 i) :=
  (sphericalFittingGradient_continuous O a mu1 mu2 teacher1 teacher2 i).measurable.add
    (metricGradient_measurable pole lambda p mu1 mu2)

theorem sphericalObjectiveGradient_integrable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (lambda p : Real)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (i : Fin 2) :
    Integrable (sphericalObjectiveGradient O a P.pole lambda p (P.measure 0) (P.measure 1)
      teacher1 teacher2 i) (P.measure i) := by
  letI : IsProbabilityMeasure (P.measure 0) := (P.cap 0).probability
  letI : IsProbabilityMeasure (P.measure 1) := (P.cap 1).probability
  letI : IsProbabilityMeasure (P.measure i) := (P.cap i).probability
  exact (sphere_integrable (P.measure i) _
    (sphericalFittingGradient_continuous O a (P.measure 0) (P.measure 1) teacher1 teacher2 i)).add
      (metricGradient_integrable P lambda p i)

theorem sphericalObjectiveGradient_pairing_integrable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (lambda p : Real)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (i : Fin 2) :
    Integrable (fun w => inner Real
      (sphericalObjectiveGradient O a P.pole lambda p (P.measure 0) (P.measure 1) teacher1 teacher2 i w)
      (P.velocity i w)) (P.measure i) := by
  have hr := regularizerGradient_pairing_integrable P lambda p i
  rw [regularizerGradient_eq_metricGradient] at hr
  simp only [sphericalObjectiveGradient,inner_add_left]
  exact (sphericalFittingGradient_source_integrable O a P teacher1 teacher2 i).1.add hr

theorem sphericalObjectiveGradient_pairing {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (lambda p : Real)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    (∑ i : Fin 2, ∫ w, inner Real
      (sphericalObjectiveGradient O a P.pole lambda p (P.measure 0) (P.measure 1) teacher1 teacher2 i w)
      (P.velocity i w) ∂P.measure i) =
    (∑ i : Fin 2, ∫ w, inner Real
      (sphericalFittingGradient O a (P.measure 0) (P.measure 1) teacher1 teacher2 i w)
      (P.velocity i w) ∂P.measure i) +
    (∑ i : Fin 2, ∫ w, inner Real
      (metricGradient P.pole lambda p (P.measure 0) (P.measure 1) w)
      (P.velocity i w) ∂P.measure i) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hr := regularizerGradient_pairing_integrable P lambda p i
  rw [regularizerGradient_eq_metricGradient] at hr
  simp only [sphericalObjectiveGradient,inner_add_left]
  exact integral_add (sphericalFittingGradient_source_integrable O a P teacher1 teacher2 i).1 hr

/-- The same state field represents the full normalized first variation,
including zero target transport and every real exponent p>2. -/
theorem normalized_objective_gradient_variation {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (lambda p : Real) (hp : 2 < p)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    HasDerivAt (variationRetractedObjective O a P lambda p teacher1 teacher2)
      (∑ i : Fin 2, ∫ w, inner Real
        (sphericalObjectiveGradient O a P.pole lambda p (P.measure 0) (P.measure 1) teacher1 teacher2 i w)
        (P.velocity i w) ∂P.measure i) 0 := by
  have hd := (normalized_fitting_gradient_variation O a P teacher1 teacher2).add
    (normalized_metricGradient_first_variation P lambda p hp)
  exact hd.congr_deriv (sphericalObjectiveGradient_pairing O a P lambda p teacher1 teacher2).symm

/-- The EXP first variation is represented by that same original field. -/
theorem spherical_objective_gradient_variation {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (lambda p : Real)
    (hlambda : 0 < lambda) (hp : 2 < p)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    HasDerivAt (variationObjective O a P lambda p teacher1 teacher2)
      (∑ i : Fin 2, ∫ w, inner Real
        (sphericalObjectiveGradient O a P.pole lambda p (P.measure 0) (P.measure 1) teacher1 teacher2 i w)
        (P.velocity i w) ∂P.measure i) 0 := by
  have hr := metricRegularizer_first_variation P lambda p hlambda hp
  rw [regularizerGradient_eq_metricGradient] at hr
  have hd := (spherical_fitting_gradient_variation O a P teacher1 teacher2).add hr
  exact hd.congr_deriv (sphericalObjectiveGradient_pairing O a P lambda p teacher1 teacher2).symm

end PaperFormalization.MatrixFactorization
