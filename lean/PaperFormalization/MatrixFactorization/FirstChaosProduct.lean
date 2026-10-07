import PaperFormalization.MatrixFactorization.HermiteTensorLowOrder

/-! # MF44: the actual normalized first-chaos product formula

The two contraction terms and their sqrt(2), 1 coefficients are identified
with the original product for arbitrary directions, including zero vectors.
This is a proved low-order case, not the general product formula.
-/
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

/-- Every first-order raw tensor is the actual pure tensor of one vector. -/
theorem exists_eq_tensorPower_one {d : Nat} (T : MomentTensor d 1) :
    ∃ u : Weight d, T = tensorPower 1 u := by
  let u : Weight d := WithLp.toLp 2 (fun i => T (fun _ => i))
  refine ⟨u, ?_⟩
  apply PiLp.ext
  intro I
  have hi : (fun _ : Fin 1 => I 0) = I := by
    funext j
    have hj : j = 0 := Fin.eq_zero j
    rw [hj]
  simp [tensorPower_apply, u, hi]

/-- No contraction gives the original unsymmetrized mixed quadratic tensor. -/
theorem tensorContractOrders_one_zero {d : Nat} (u v : Weight d) :
    tensorContractOrders d 1 1 0 (by decide) (by decide)
      (tensorPower 1 u) (tensorPower 1 v) = mixedTensorMap d 2 ![u, v] := by
  change tensorContraction d 1 1 0 (tensorPower (1 + 0) u) (tensorPower (0 + 1) v) = _
  rw [tensorContraction_tensorPower]
  simp only [pow_zero, one_smul]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The one matched slot gives exactly the original Euclidean pairing in
the scalar zeroth-chaos block. -/
theorem tensorContractOrders_one_one {d : Nat} (u v z : Weight d) :
    tensorContractOrders d 1 1 1 (by decide) (by decide)
      (tensorPower 1 u) (tensorPower 1 v) = inner Real u v • tensorPower 0 z := by
  change tensorContraction d 0 0 1 (tensorPower (0 + 1) u) (tensorPower (1 + 0) v) = _
  rw [tensorContraction_tensorPower]
  simp only [pow_one]
  congr 1

/-- A symmetric Hermite observation is unchanged by the actual orthogonal
symmetrization of the other argument. -/
theorem normalizedHermiteTensor_pairing_symmetrize {d n : Nat} (z : Weight d)
    (T : MomentTensor d n) :
    inner Real (normalizedHermiteTensor d n z).val (tensorSymmetrize d n T) =
      inner Real (normalizedHermiteTensor d n z).val T := by
  rw [← tensorSymmetrize_inner,
    tensorSymmetrize_of_symmetric _ (normalizedHermiteTensor d n z).property]

/-- The normalized first-chaos product identity for every actual first-order
tensor, including nonspecial coefficient choices and zero vectors. -/
theorem normalizedHermiteTensor_product_one {d : Nat} (z : Weight d)
    (A B : MomentTensor d 1) :
    inner Real (normalizedHermiteTensor d 1 z).val A *
      inner Real (normalizedHermiteTensor d 1 z).val B =
      normalizedChaosCoefficient 1 1 0 *
        inner Real (normalizedHermiteTensor d 2 z).val
          (tensorSymmetrize d 2 (tensorContractOrders d 1 1 0 (by decide) (by decide) A B)) +
      normalizedChaosCoefficient 1 1 1 *
        inner Real (normalizedHermiteTensor d 0 z).val
          (tensorSymmetrize d 0 (tensorContractOrders d 1 1 1 (by decide) (by decide) A B)) := by
  obtain ⟨u, rfl⟩ := exists_eq_tensorPower_one A
  obtain ⟨v, rfl⟩ := exists_eq_tensorPower_one B
  rw [normalizedHermiteTensor_power_one, normalizedHermiteTensor_power_one,
    tensorContractOrders_one_zero, tensorContractOrders_one_one u v z,
    normalizedHermiteTensor_pairing_symmetrize,
    normalizedHermiteTensor_pairing_symmetrize,
    normalizedHermiteTensor_mixed_two, real_inner_smul_right,
    normalizedHermiteTensor_power_zero, normalizedChaosCoefficient_one_one_zero,
    normalizedChaosCoefficient_one_one_one]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  ring

end PaperFormalization.MatrixFactorization
