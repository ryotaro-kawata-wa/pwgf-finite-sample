import PaperFormalization.MatrixFactorization.UnitTensorPowerSpan
import PaperFormalization.MatrixFactorization.TensorHermiteBounds
import PaperFormalization.MatrixFactorization.GaussianHermiteCrossCovariance

/-! # MF41: a genuine bilinear Gaussian pairing for tensor Hermite evaluations

True integrability is proved before linearity of the actual integral. The
source tensor orthogonality can therefore be extended from unit pure powers
using MF40's proved spanning result.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

/-- Products of any two tensor Hermite observations have genuine Gaussian integrability. -/
theorem tensorHermite_product_integrable {d n m : Nat} (T : MomentTensor d n) (U : MomentTensor d m) :
    Integrable (fun z : Weight d => tensorHermiteEvaluation d n z T * tensorHermiteEvaluation d m z U)
      (stdGaussian (Weight d)) := by
  have hi := ((tensorHermiteEvaluation_gaussian_power_integrable T 2).add
    (tensorHermiteEvaluation_gaussian_power_integrable U 2)).div_const 2
  have hc := (tensorHermiteEvaluation_continuous_input T).mul (tensorHermiteEvaluation_continuous_input U)
  apply hi.mono' hc.aestronglyMeasurable
  filter_upwards [] with z
  change ‖tensorHermiteEvaluation d n z T * tensorHermiteEvaluation d m z U‖ ≤
    (‖tensorHermiteEvaluation d n z T‖ ^ 2 + ‖tensorHermiteEvaluation d m z U‖ ^ 2) / 2
  rw [norm_mul]
  nlinarith [sq_nonneg (‖tensorHermiteEvaluation d n z T‖ - ‖tensorHermiteEvaluation d m z U‖)]

/-- Linearity in both full tensor inputs is derived from the actual integrable functions. -/
noncomputable def tensorHermiteGaussianPairing (d n m : Nat) :
    MomentTensor d n →ₗ[Real] MomentTensor d m →ₗ[Real] Real where
  toFun T :=
    { toFun U := ∫ z : Weight d, tensorHermiteEvaluation d n z T * tensorHermiteEvaluation d m z U
        ∂stdGaussian (Weight d)
      map_add' U V := by
        simp_rw [map_add, mul_add]
        exact integral_add (tensorHermite_product_integrable T U) (tensorHermite_product_integrable T V)
      map_smul' c U := by
        simp only [map_smul, smul_eq_mul]
        simp_rw [mul_left_comm (tensorHermiteEvaluation d n _ T) c]
        exact integral_const_mul _ _ }
  map_add' T V := by
    apply LinearMap.ext
    intro U
    change (∫ z : Weight d, tensorHermiteEvaluation d n z (T + V) * tensorHermiteEvaluation d m z U
      ∂stdGaussian (Weight d)) = _
    simp_rw [map_add, add_mul]
    exact integral_add (tensorHermite_product_integrable T U) (tensorHermite_product_integrable V U)
  map_smul' c T := by
    apply LinearMap.ext
    intro U
    change (∫ z : Weight d, tensorHermiteEvaluation d n z (c • T) * tensorHermiteEvaluation d m z U
      ∂stdGaussian (Weight d)) = _
    simp only [map_smul, smul_eq_mul]
    simp_rw [mul_assoc]
    exact integral_const_mul _ _

@[simp] theorem tensorHermiteGaussianPairing_apply {d n m : Nat}
    (T : MomentTensor d n) (U : MomentTensor d m) :
    tensorHermiteGaussianPairing d n m T U = ∫ z : Weight d,
      tensorHermiteEvaluation d n z T * tensorHermiteEvaluation d m z U ∂stdGaussian (Weight d) := rfl

noncomputable def symmetricHermiteGaussianPairing (d n m : Nat) :
    SymmetricMomentTensor d n →ₗ[Real] SymmetricMomentTensor d m →ₗ[Real] Real :=
  ((tensorHermiteGaussianPairing d n m).comp (symmetricTensorSubmodule d n).subtype).compl₂
    (symmetricTensorSubmodule d m).subtype

/-- Unit-direction covariance extends to the whole symmetric space with exactly its raw norm. -/
theorem symmetricHermiteGaussianPairing_self {d : Nat} (pole : UnitSphere d) (n : Nat) :
    symmetricHermiteGaussianPairing d n n = innerₗ (SymmetricMomentTensor d n) := by
  apply symmetricTensor_linear_ext_on_units pole
  intro u
  apply symmetricTensor_linear_ext_on_units pole
  intro v
  change (∫ z : Weight d,
    tensorHermiteEvaluation d n z (tensorPower n u.val) *
    tensorHermiteEvaluation d n z (tensorPower n v.val) ∂stdGaussian (Weight d)) =
    inner Real (tensorPower n u.val) (tensorPower n v.val)
  simp_rw [tensorHermiteEvaluation_unit]
  rw [normalizedHermite_gaussian_covariance, if_pos rfl, tensorPower_inner]

/-- Distinct chaos orders are orthogonal for arbitrary symmetric tensors. -/
theorem symmetricHermiteGaussianPairing_of_ne {d : Nat} (pole : UnitSphere d) (n m : Nat)
    (hnm : n ≠ m) : symmetricHermiteGaussianPairing d n m = 0 := by
  apply symmetricTensor_linear_ext_on_units pole
  intro u
  apply symmetricTensor_linear_ext_on_units pole
  intro v
  change (∫ z : Weight d,
    tensorHermiteEvaluation d n z (tensorPower n u.val) *
    tensorHermiteEvaluation d m z (tensorPower m v.val) ∂stdGaussian (Weight d)) = 0
  simp_rw [tensorHermiteEvaluation_unit]
  rw [normalizedHermite_gaussian_covariance, if_neg hnm]

end PaperFormalization.MatrixFactorization
