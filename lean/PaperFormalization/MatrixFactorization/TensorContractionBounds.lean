import PaperFormalization.MatrixFactorization.TensorContraction

/-! # MF42: dimension-free Hilbert--Schmidt contraction bounds

Finite-index splitting is a genuine bijection. Cauchy--Schwarz over the
matched slots therefore gives constant one in the original tensor norm.
-/
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Split a tensor index into its first and last blocks, with no coordinate
multiplicity or change of norm. -/
def tensorIndexAppendEquiv (d n m : Nat) :
    ((Fin n → Fin d) × (Fin m → Fin d)) ≃ (Fin (n + m) → Fin d) where
  toFun J := Fin.append J.1 J.2
  invFun I := (fun i => I (Fin.castAdd m i), fun j => I (Fin.natAdd n j))
  left_inv J := by simp
  right_inv I := Fin.append_castAdd_natAdd

/-- Summing over the original tensor coordinates equals summing once over
each pair of free coordinate blocks. -/
theorem tensorIndex_sum_append {d n m : Nat} (f : (Fin (n + m) → Fin d) → Real) :
    (∑ I, f I) = ∑ J : Fin n → Fin d, ∑ K : Fin m → Fin d, f (Fin.append J K) := by
  classical
  calc
    _ = ∑ J : (Fin n → Fin d) × (Fin m → Fin d), f (Fin.append J.1 J.2) :=
      (Fintype.sum_equiv (tensorIndexAppendEquiv d n m) _ _ (fun _ => rfl)).symm
    _ = _ := Fintype.sum_prod_type _

/-- The literal matched-index contraction has Hilbert--Schmidt norm at most
the product of the two input norms, with constant one in every dimension. -/
theorem tensorContraction_norm_le {d n m r : Nat}
    (A : MomentTensor d (n + r)) (B : MomentTensor d (r + m)) :
    ‖tensorContraction d n m r A B‖ ≤ ‖A‖ * ‖B‖ := by
  have hs : ‖tensorContraction d n m r A B‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖B‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, tensorIndex_sum_append]
    simp only [tensorContraction_apply, Fin.append_left, Fin.append_right]
    calc
      _ ≤ ∑ J : Fin n → Fin d, ∑ K : Fin m → Fin d,
          (∑ L : Fin r → Fin d, A (Fin.append J L) ^ 2) *
            ∑ L : Fin r → Fin d, B (Fin.append L K) ^ 2 := by
        apply Finset.sum_le_sum
        intro J _
        apply Finset.sum_le_sum
        intro K _
        exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = ‖A‖ ^ 2 * ‖B‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
          tensorIndex_sum_append, tensorIndex_sum_append]
        simp only [← Finset.mul_sum, ← Finset.sum_mul]
        congr 1
        exact Finset.sum_comm
  have hn := mul_nonneg (norm_nonneg A) (norm_nonneg B)
  nlinarith [norm_nonneg (tensorContraction d n m r A B)]

/-- Orthogonal symmetrization preserves the same dimension-free bound. -/
theorem symmetricTensorContraction_norm_le {d n m r : Nat}
    (A : MomentTensor d (n + r)) (B : MomentTensor d (r + m)) :
    ‖symmetricTensorContraction d n m r A B‖ ≤ ‖A‖ * ‖B‖ := by
  exact (tensorSymmetrize_norm_le _).trans (tensorContraction_norm_le A B)

end PaperFormalization.MatrixFactorization
