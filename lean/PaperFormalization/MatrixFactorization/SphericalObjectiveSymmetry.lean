import PaperFormalization.MatrixFactorization.SphericalFittingGradientSymmetry
import PaperFormalization.MatrixFactorization.SphericalTransportSymmetry
import PaperFormalization.MatrixFactorization.SphericalObjective

/-! # Exact objective symmetry for the original product model

The fitting statement uses the literal Frobenius matrix residual and one
Gaussian input. The metric statement uses reflection of every admissible
transport plan. These identities prepare branch covariance without making a
claim about existence or uniqueness of a gradient-flow trajectory.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Transposing both rank-one matrices preserves their Frobenius residual. -/
theorem outer_residual_exchange_norm_sq {h : Nat} (x y u v : Weight h) :
    norm (outer y x-outer v u)^2 = norm (outer x y-outer u v)^2 := by
  simp only [norm_sub_sq_real, outer_norm_sq, outer_inner]
  ring

/-- General exchange covariance also exchanges the two teacher factors. -/
theorem modelFitting_exchange {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d)) :
    modelFitting O a mu2 mu1 teacher2 teacher1 = modelFitting O a mu1 mu2 teacher1 teacher2 := by
  simp only [modelFitting, fittingEnergy, outer_residual_exchange_norm_sq]

/-- Odd activation reflection and factor exchange preserve the symmetric-teacher fit. -/
theorem modelFitting_reflection_exchange {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n)
    (mu1 mu2 teacher : Measure (UnitSphere d)) [IsFiniteMeasure mu1] [IsFiniteMeasure mu2] :
    modelFitting O a (reflectedMeasure mu2) (reflectedMeasure mu1) teacher teacher =
      modelFitting O a mu1 mu2 teacher teacher := by
  have he : modelFitting O a (reflectedMeasure mu2) (reflectedMeasure mu1) teacher teacher =
      modelFitting O a mu2 mu1 teacher teacher := by
    simp only [modelFitting, fittingEnergy, finiteHermite_mean_reflected O a hO,
      outer_neg_left, outer_neg_right, neg_neg]
  exact he.trans (modelFitting_exchange O a mu1 mu2 teacher teacher)

/-- The full noninteger-power metric penalty is invariant under reflection and exchange. -/
theorem metricRegularizer_reflection_exchange {d : Nat} (pole : UnitSphere d)
    (lambda p : Real) (mu1 mu2 : Measure (UnitSphere d))
    [IsProbabilityMeasure mu1] [IsProbabilityMeasure mu2] :
    metricRegularizer pole lambda p (reflectedMeasure mu2) (reflectedMeasure mu1) =
      metricRegularizer pole lambda p mu1 mu2 := by
  simp only [metricRegularizer, productAntipodalTransportSq_reflection_exchange]

/-- Source reflection--exchange symmetry for the literal full objective. -/
theorem modelObjective_reflection_exchange {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (pole : UnitSphere d)
    (lambda p : Real) (mu1 mu2 teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure mu1] [IsProbabilityMeasure mu2] :
    modelObjective O a pole lambda p (reflectedMeasure mu2) (reflectedMeasure mu1) teacher teacher =
      modelObjective O a pole lambda p mu1 mu2 teacher teacher := by
  simp only [modelObjective, modelFitting_reflection_exchange O a hO,
    metricRegularizer_reflection_exchange]

/-- Same-density branch exchange uses no activation parity hypothesis. -/
theorem modelObjective_exchange {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (lambda p : Real)
    (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d)) :
    modelObjective O a pole lambda p mu2 mu1 teacher2 teacher1 =
      modelObjective O a pole lambda p mu1 mu2 teacher1 teacher2 := by
  unfold modelObjective
  rw [modelFitting_exchange O a mu1 mu2 teacher1 teacher2]
  simp only [metricRegularizer, productAntipodalTransportSq, add_comm]

end PaperFormalization.MatrixFactorization
