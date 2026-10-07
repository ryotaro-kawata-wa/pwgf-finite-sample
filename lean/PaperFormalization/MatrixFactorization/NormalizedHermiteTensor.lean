import PaperFormalization.MatrixFactorization.TensorGaussianPairing

/-! # MF41: the normalized symmetric Hermite tensor and Gaussian orthogonality

The polynomial evaluator determines a unique symmetric tensor by Riesz and
unit-power spanning. Its Gaussian pairing is derived from the actual integral.
The density-derivative Rodrigues presentation is not an extra axiom here.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

/-- The unique symmetric tensor representing the normalized polynomial evaluator. -/
noncomputable def normalizedHermiteTensor (d n : Nat) (z : Weight d) : SymmetricMomentTensor d n :=
  (InnerProductSpace.toDual Real (SymmetricMomentTensor d n)).symm
    ((tensorHermiteEvaluation d n z).comp (symmetricTensorSubmodule d n).subtypeL)

theorem normalizedHermiteTensor_pairing_symmetric {d n : Nat} (z : Weight d)
    (T : SymmetricMomentTensor d n) :
    inner Real (normalizedHermiteTensor d n z) T = tensorHermiteEvaluation d n z T.val :=
  InnerProductSpace.toDual_symm_apply

/-- A full tensor observation first projects to the exact factorial symmetric average. -/
theorem normalizedHermiteTensor_pairing {d n : Nat} (z : Weight d) (T : MomentTensor d n) :
    inner Real (normalizedHermiteTensor d n z).val T =
      tensorHermiteEvaluation d n z (tensorSymmetrize d n T) := by
  calc
    _ = inner Real (tensorSymmetrize d n (normalizedHermiteTensor d n z).val) T := by
      rw [tensorSymmetrize_of_symmetric _ (normalizedHermiteTensor d n z).property]
    _ = inner Real (normalizedHermiteTensor d n z).val (tensorSymmetrize d n T) :=
      tensorSymmetrize_inner _ _
    _ = _ := normalizedHermiteTensor_pairing_symmetric z
      ⟨tensorSymmetrize d n T, tensorSymmetrize_symmetric T⟩

/-- The original probabilists' Hermite normalizer is recovered on every unit direction. -/
theorem normalizedHermiteTensor_unit {d n : Nat} (z : Weight d) (w : UnitSphere d) :
    inner Real (normalizedHermiteTensor d n z).val (tensorPower n w.val) =
      normalizedHermite n (inner Real w.val z) := by
  rw [normalizedHermiteTensor_pairing, tensorSymmetrize_tensorPower, tensorHermiteEvaluation_unit]

/-- Unit-direction observations characterize the symmetric tensor, rather than being assumed to do so. -/
theorem normalizedHermiteTensor_unique {d n : Nat} (pole : UnitSphere d) (z : Weight d)
    (T : SymmetricMomentTensor d n)
    (hT : ∀ w : UnitSphere d, inner Real T.val (tensorPower n w.val) =
      normalizedHermite n (inner Real w.val z)) : T = normalizedHermiteTensor d n z := by
  have he : innerₗ (SymmetricMomentTensor d n) T =
      innerₗ (SymmetricMomentTensor d n) (normalizedHermiteTensor d n z) := by
    apply symmetricTensor_linear_ext_on_units pole
    intro w
    exact (hT w).trans (normalizedHermiteTensor_unit z w).symm
  apply (InnerProductSpace.toDual Real (SymmetricMomentTensor d n)).injective
  apply ContinuousLinearMap.ext
  intro U
  exact congrArg (fun L => L U) he

/-- The actual full-tensor observations have a true product integral. -/
theorem normalizedHermiteTensor_product_integrable {d n m : Nat}
    (T : MomentTensor d n) (U : MomentTensor d m) :
    Integrable (fun z : Weight d =>
      inner Real (normalizedHermiteTensor d n z).val T * inner Real (normalizedHermiteTensor d m z).val U)
      (stdGaussian (Weight d)) := by
  simp_rw [normalizedHermiteTensor_pairing]
  exact tensorHermite_product_integrable _ _

/-- The same-order Gaussian identity has exactly the full symmetric Hilbert--Schmidt pairing. -/
theorem normalizedHermiteTensor_gaussian_inner {d n : Nat} (pole : UnitSphere d)
    (T U : MomentTensor d n) :
    (∫ z : Weight d, inner Real (normalizedHermiteTensor d n z).val T *
      inner Real (normalizedHermiteTensor d n z).val U ∂stdGaussian (Weight d)) =
      inner Real (tensorSymmetrize d n T) (tensorSymmetrize d n U) := by
  simp_rw [normalizedHermiteTensor_pairing]
  exact congrArg (fun L => L ⟨tensorSymmetrize d n T, tensorSymmetrize_symmetric T⟩
    ⟨tensorSymmetrize d n U, tensorSymmetrize_symmetric U⟩)
    (symmetricHermiteGaussianPairing_self pole n)

/-- Distinct orders have zero Gaussian pairing, also for nonsymmetric full input tensors. -/
theorem normalizedHermiteTensor_gaussian_inner_of_ne {d n m : Nat} (pole : UnitSphere d)
    (T : MomentTensor d n) (U : MomentTensor d m) (hnm : n ≠ m) :
    (∫ z : Weight d, inner Real (normalizedHermiteTensor d n z).val T *
      inner Real (normalizedHermiteTensor d m z).val U ∂stdGaussian (Weight d)) = 0 := by
  simp_rw [normalizedHermiteTensor_pairing]
  exact congrArg (fun L => L ⟨tensorSymmetrize d n T, tensorSymmetrize_symmetric T⟩
    ⟨tensorSymmetrize d m U, tensorSymmetrize_symmetric U⟩)
    (symmetricHermiteGaussianPairing_of_ne pole n m hnm)

/-- The exact Gaussian L2 norm does not contain a factorial or dimension loss. -/
theorem normalizedHermiteTensor_gaussian_sq {d n : Nat} (pole : UnitSphere d) (T : MomentTensor d n) :
    (∫ z : Weight d, (inner Real (normalizedHermiteTensor d n z).val T) ^ 2
      ∂stdGaussian (Weight d)) = ‖tensorSymmetrize d n T‖ ^ 2 := by
  simpa only [pow_two, real_inner_self_eq_norm_sq] using normalizedHermiteTensor_gaussian_inner pole T T

end PaperFormalization.MatrixFactorization
