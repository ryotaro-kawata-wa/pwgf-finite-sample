import PaperFormalization.MatrixFactorization.SphericalFittingVariation
import PaperFormalization.MatrixFactorization.SphericalRegularizerClosure

/-! # MF05: the original fitting-plus-regularizer objective

The objective is the literal sum in the manuscript, evaluated on the same
spherical EXP pushforwards. The regularizer's local differentiability is proved
before identifying the ordinary second derivative of the sum. Positive and
zero target distance are kept separate, so no singular positive-distance
expression is evaluated at the center.
-/
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def modelObjective {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (pole : UnitSphere d) (lambda p : Real)
    (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d)) : Real :=
  modelFitting O a mu1 mu2 teacher1 teacher2 + metricRegularizer pole lambda p mu1 mu2

noncomputable def variationObjective {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (lambda p : Real)
    (teacher1 teacher2 : Measure (UnitSphere d)) (t : Real) : Real :=
  modelObjective O a P.pole lambda p
    ((P.measure 0).map (sphericalExpFamily (P.velocity 0) (P.tangent 0) t))
    ((P.measure 1).map (sphericalExpFamily (P.velocity 1) (P.tangent 1) t)) teacher1 teacher2

theorem variationObjective_split {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (lambda p : Real)
    (teacher1 teacher2 : Measure (UnitSphere d)) (t : Real) :
    variationObjective O a P lambda p teacher1 teacher2 t =
      variationFitting O a P teacher1 teacher2 t + variationRegularizer P lambda p t := rfl

theorem variationRegularizer_differentiable_near {d : Nat} (P : SphericalVariation d)
    (lambda p : Real) (hp : 2 < p) :
    ∀ᶠ t in 𝓝 (0 : Real), DifferentiableAt Real (variationRegularizer P lambda p) t := by
  filter_upwards [(variationTransport_variations P).2.2] with t ht
  exact (ht.rpow_const (p := p/2) (Or.inr (by linarith))).const_mul (lambda/p)

theorem variationObjective_deriv_near {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (lambda p : Real) (hp : 2 < p)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    deriv (variationObjective O a P lambda p teacher1 teacher2) =ᶠ[𝓝 (0 : Real)]
      (fun t => deriv (variationFitting O a P teacher1 teacher2) t +
        deriv (variationRegularizer P lambda p) t) := by
  filter_upwards [variationRegularizer_differentiable_near P lambda p hp] with t ht
  exact deriv_add (variationFitting_variations O a P teacher1 teacher2 t).1.differentiableAt ht

theorem spherical_objective_positive_variations {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (lambda p : Real)
    (hlambda : 0 < lambda) (hp : 2 < p) (hZ : 0 < variationTransport P 0)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    HasDerivAt (variationObjective O a P lambda p teacher1 teacher2)
      (variationFittingFirst O a P teacher1 teacher2 0 +
        lambda*(variationTransport P 0)^(p/2-1)*variationFirst P) 0 ∧
    HasDerivAt (deriv (variationObjective O a P lambda p teacher1 teacher2))
      (variationFittingSecond O a P teacher1 teacher2 0 +
        (lambda*(variationTransport P 0)^(p/2-1)*variationSecond P +
          lambda*(p-2)*(variationTransport P 0)^(p/2-2)*(variationFirst P)^2)) 0 := by
  have hf := spherical_fitting_source_variations O a P teacher1 teacher2 0
  have hr := metricRegularizer_positive_variations P lambda p hlambda hp hZ
  exact ⟨hf.1.add hr.1, (hf.2.add hr.2).congr_of_eventuallyEq
    (variationObjective_deriv_near O a P lambda p hp teacher1 teacher2)⟩

theorem spherical_objective_zero_variations {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (lambda p : Real)
    (hp : 2 < p) (hZ : variationTransport P 0 = 0)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    HasDerivAt (variationObjective O a P lambda p teacher1 teacher2)
      (variationFittingFirst O a P teacher1 teacher2 0) 0 ∧
    HasDerivAt (deriv (variationObjective O a P lambda p teacher1 teacher2))
      (variationFittingSecond O a P teacher1 teacher2 0) 0 := by
  have hf := spherical_fitting_source_variations O a P teacher1 teacher2 0
  have hr := metricRegularizer_zero_variations P lambda p hp hZ
  constructor
  · exact (hf.1.add hr.1).congr_deriv (add_zero _)
  · exact ((hf.2.add hr.2).congr_deriv (add_zero _)).congr_of_eventuallyEq
      (variationObjective_deriv_near O a P lambda p hp teacher1 teacher2)

theorem spherical_objective_second_lower_bound {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (lambda p : Real)
    (hlambda : 0 < lambda) (hp : 2 < p) (hZ : 0 < variationTransport P 0)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    variationFittingSecond O a P teacher1 teacher2 0 +
      lambda*(variationTransport P 0)^(p/2-1)*sphericalRadialWeight P.radius*variationEnergy P ≤
      deriv (deriv (variationObjective O a P lambda p teacher1 teacher2)) 0 := by
  rw [(spherical_objective_positive_variations O a P lambda p hlambda hp hZ teacher1 teacher2).2.deriv]
  have hb := metricRegularizer_second_lower_bound P lambda p hlambda hp hZ
  rw [(metricRegularizer_positive_variations P lambda p hlambda hp hZ).2.deriv] at hb
  linarith

end PaperFormalization.MatrixFactorization
