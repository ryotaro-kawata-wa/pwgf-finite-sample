import PaperFormalization.MatrixFactorization.BoundedFittingFirstVariation
import PaperFormalization.MatrixFactorization.PrimalMetricFirstVariation

/-! # MF24: full source-gradient bounds without classical optimal dual data

Verification status and conditional scope: see `MF24_VALIDATION.md`. The only gradient-existence input is the full objective's
primal L2 first-variation identity. The fitting derivative is proved from the
actual finite Hermite/Gaussian model and subtracted, so a separate regularizer
gradient is NOT a new input. Bounds and cap identification are measure-AE.
The domination constant is not a replacement for sharp source basin constants.
-/
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def partialObjectiveFunctional {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (lambda p : Real)
    (other teacher1 teacher2 : Measure (UnitSphere d)) (mu : Measure (UnitSphere d)) : Real :=
  modelObjective O a pole lambda p mu other teacher1 teacher2

noncomputable def primalObjectiveSpeedBound (d : Nat) {h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (lambda p : Real) : Real :=
  fittingCurvatureConstant d O a + primalMetricSpeedBound lambda p

theorem primalObjectiveSpeedBound_nonneg (d : Nat) {h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (lambda p : Real) (hl : 0 ≤ lambda) :
    0 ≤ primalObjectiveSpeedBound d O a lambda p :=
  add_nonneg (fittingCurvatureConstant_nonneg d O a) (primalMetricSpeedBound_nonneg hl)

/-- The primal metric derivative is obtained by subtraction from the full one. -/
theorem primalMetricGradient_from_full {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (lambda p : Real)
    (mu other teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure other]
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2]
    (g : UnitSphere d → Weight d)
    (H : HasSphereFirstVariation mu (partialObjectiveFunctional O a pole lambda p other teacher1 teacher2) g) :
    HasSphereFirstVariation mu (partialMetricFunctional pole lambda p other)
      (fun w => g w-sphericalFittingGradient O a mu other teacher1 teacher2 0 w) := by
  apply (H.sub (partialFitting_firstVariation O a mu other teacher1 teacher2)).congr_function
  intro nu
  simp only [partialObjectiveFunctional, modelObjective, partialFittingFunctional,
    partialMetricFunctional]
  ring

/-- Uniform essential speed bound for the genuine full gradient on arbitrary
sphere probability laws, before any cap interval is known. -/
theorem primalObjectiveGradient_norm_le {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (lambda p : Real)
    (hl : 0 ≤ lambda) (hp : 2 < p)
    (mu other teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure other]
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2]
    (g : UnitSphere d → Weight d)
    (H : HasSphereFirstVariation mu (partialObjectiveFunctional O a pole lambda p other teacher1 teacher2) g) :
    ∀ᵐ w ∂mu, norm (g w) ≤ primalObjectiveSpeedBound d O a lambda p := by
  have Hreg := primalMetricGradient_from_full O a pole lambda p mu other teacher1 teacher2 g H
  have hb := primalMetricGradient_norm_le pole lambda p hl hp mu other _ Hreg
  filter_upwards [hb] with w hw
  have hf := sphericalFittingGradient_norm_le O a mu other teacher1 teacher2 0 w
  have he : g w = (g w-sphericalFittingGradient O a mu other teacher1 teacher2 0 w) +
      sphericalFittingGradient O a mu other teacher1 teacher2 0 w := by abel
  calc
    _ = norm ((g w-sphericalFittingGradient O a mu other teacher1 teacher2 0 w) +
        sphericalFittingGradient O a mu other teacher1 teacher2 0 w) := congrArg norm he
    _ ≤ norm (g w-sphericalFittingGradient O a mu other teacher1 teacher2 0 w) +
        norm (sphericalFittingGradient O a mu other teacher1 teacher2 0 w) := norm_add_le _ _
    _ ≤ primalMetricSpeedBound lambda p+fittingCurvatureConstant d O a := add_le_add hw hf
    _ = _ := add_comm _ _

/-- On a cap law, the existing full field supplies all the bounded-test derivatives. -/
theorem cap_partialObjective_firstVariation {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (r lambda p : Real) (hp : 2 < p)
    (mu other teacher1 teacher2 : Measure (UnitSphere d)) (hc : TwoCapClass pole r mu)
    [IsProbabilityMeasure other] [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    HasSphereFirstVariation mu (partialObjectiveFunctional O a pole lambda p other teacher1 teacher2)
      (sphericalObjectiveGradient O a pole lambda p mu other teacher1 teacher2 0) := by
  letI : IsProbabilityMeasure mu := hc.probability
  exact (partialFitting_firstVariation O a mu other teacher1 teacher2).add
    (cap_partialMetric_firstVariation pole r lambda p hp mu other hc)

/-- AE local equality follows by uniqueness of primal testing; no optimal-potential
representation or independently supplied local-field identity occurs in the input. -/
theorem cap_primalObjectiveGradient_eq_ae {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (r lambda p : Real) (hp : 2 < p)
    (mu other teacher1 teacher2 : Measure (UnitSphere d)) (hc : TwoCapClass pole r mu)
    [IsProbabilityMeasure other] [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2]
    (g : UnitSphere d → Weight d)
    (H : HasSphereFirstVariation mu (partialObjectiveFunctional O a pole lambda p other teacher1 teacher2) g) :
    g =ᵐ[mu] sphericalObjectiveGradient O a pole lambda p mu other teacher1 teacher2 0 := by
  letI : IsProbabilityMeasure mu := hc.probability
  exact H.unique_ae (cap_partialObjective_firstVariation O a pole r lambda p hp mu other teacher1 teacher2 hc)

end PaperFormalization.MatrixFactorization
