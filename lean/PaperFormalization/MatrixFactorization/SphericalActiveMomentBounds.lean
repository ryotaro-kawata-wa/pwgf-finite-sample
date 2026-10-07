import PaperFormalization.MatrixFactorization.ActiveMomentMapBounds
import PaperFormalization.MatrixFactorization.SphericalRegularizer

/-! # MF34: the printed active moment coefficients on the original source variation

The final application uses the existing source variation record, its exact
original laws and fields, and the previously defined source L2 energy.
-/
open MeasureTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000

/-- The source variation's cap records already contain these probability laws. -/
instance sphericalVariation_probability {d : Nat} (P : SphericalVariation d) (i : Fin 2) :
    IsProbabilityMeasure (P.measure i) := (P.cap i).probability

/-- The product norm is the existing source energy, with no rescaling. -/
theorem productTangentEnergy_eq_variationEnergy {d : Nat} (P : SphericalVariation d) :
    productTangentEnergy P.measure P.velocity = variationEnergy P := by
  rw [variationEnergy, Fin.sum_univ_two]
  rfl

/-- The source sums and product L2 normalization for actual active EXP derivatives. -/
theorem spherical_active_moment_derivative_bounds {d : Nat} (O : Finset Nat)
    (P : SphericalVariation d) (t : Real) :
    ‖deriv (activeMomentMapAlongExp O P.measure P.velocity P.tangent) t‖ ≤
      Real.sqrt (∑ n ∈ O, (n : Real) ^ 2) * Real.sqrt (variationEnergy P) ∧
    ‖deriv (deriv (activeMomentMapAlongExp O P.measure P.velocity P.tangent)) t‖ ≤
      Real.sqrt (∑ n ∈ O, (n : Real) ^ 4) * variationEnergy P := by
  letI : ∀ i, IsProbabilityMeasure (P.measure i) := fun i => (P.cap i).probability
  have h := (activeMomentMapAlongExp_derivative_bounds O P.measure P.velocity P.tangent P.continuous_velocity t).2
  rw [Finset.sum_coe_sort O (fun n : Nat => (n : Real) ^ 2),
    Finset.sum_coe_sort O (fun n : Nat => (n : Real) ^ 4), productTangentEnergy_eq_variationEnergy] at h
  convert h using 1 <;> rfl

end PaperFormalization.MatrixFactorization
