import PaperFormalization.MatrixFactorization.AntisymmetricRadialFittingPairing
import PaperFormalization.MatrixFactorization.ContractionRadialFittingBound
import PaperFormalization.MatrixFactorization.SphericalRadialPairing
import PaperFormalization.MatrixFactorization.SphericalCapSymmetry

/-! # The source-derived static radial lower bound

The actual original-measure fitting pairing is combined with the exact metric
pairing. The finite polynomial envelope coefficient is deliberately stated
explicitly; it is not identified with the manuscript's sharper L4 coefficient.
These are static statements and do not assume or assert a characteristic flow.
-/
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The fitting estimate applies to the actual two original branch measures. -/
theorem antisymmetricRadialFittingPairing_lower {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (r : Real) (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    -(fittingCurvatureConstant d O a/64)*
        (productAntipodalTransportSq pole mu (reflectedMeasure mu))^2 ≤
      antisymmetricRadialFittingPairing O a pole mu teacher := by
  rw [antisymmetricRadialFittingPairing_eq O a hO pole r mu hcap teacher]
  exact contraction_radial_gaussian_lower O a hO pole r mu hcap teacher

noncomputable def antisymmetricRadialObjectivePairing {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (lambda p : Real)
    (mu teacher : Measure (UnitSphere d)) : Real :=
  (∫ w, inner Real (sphericalObjectiveGradient O a pole lambda p mu (reflectedMeasure mu)
    teacher teacher 0 w) (assignedGradient pole w) ∂mu) +
  (∫ w, inner Real (sphericalObjectiveGradient O a pole lambda p mu (reflectedMeasure mu)
    teacher teacher 1 w) (assignedGradient pole w) ∂reflectedMeasure mu)

theorem antisymmetricRadialObjectivePairing_split {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (r lambda p : Real)
    (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    antisymmetricRadialObjectivePairing O a pole lambda p mu teacher =
      antisymmetricRadialFittingPairing O a pole mu teacher +
      lambda*(productAntipodalTransportSq pole mu (reflectedMeasure mu))^(p/2-1)*
        productAntipodalTransportSq pole mu (reflectedMeasure mu) := by
  let nu : Fin 2 → Measure (UnitSphere d) := ![mu, reflectedMeasure mu]
  have hc : ∀ i, TwoCapClass pole r (nu i) := by
    intro i
    fin_cases i
    · exact hcap
    · exact hcap.reflected
  simpa only [nu, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    antisymmetricRadialObjectivePairing, antisymmetricRadialFittingPairing] using
    objective_radial_pairing O a pole r lambda p nu hc teacher teacher

/-- No desired radial estimate or Gaussian identity is assumed in this bound. -/
theorem antisymmetricRadialObjectivePairing_lower {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (r lambda p : Real) (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    lambda*(productAntipodalTransportSq pole mu (reflectedMeasure mu))^(p/2-1)*
        productAntipodalTransportSq pole mu (reflectedMeasure mu) -
      (fittingCurvatureConstant d O a/64)*
        (productAntipodalTransportSq pole mu (reflectedMeasure mu))^2 ≤
      antisymmetricRadialObjectivePairing O a pole lambda p mu teacher := by
  rw [antisymmetricRadialObjectivePairing_split O a pole r lambda p mu hcap teacher]
  linarith [antisymmetricRadialFittingPairing_lower O a hO pole r mu hcap teacher]

end PaperFormalization.MatrixFactorization
