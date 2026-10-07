import PaperFormalization.MatrixFactorization.SymmetricTensorProjection
import PaperFormalization.MatrixFactorization.IteratedTensorTrace

/-! # MF42: literal matched-index tensor contractions

The free and contracted slot counts are explicit. Every contraction is the
finite sum over the original spatial coordinates, with no rescaling.
-/
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Contract the last `r` slots of the left tensor against the first `r` slots
of the right tensor, retaining all `n + m` free slots in their original order. -/
noncomputable def tensorContraction (d n m r : Nat) :
    MomentTensor d (n + r) →ₗ[Real]
      MomentTensor d (r + m) →ₗ[Real] MomentTensor d (n + m) where
  toFun A :=
    { toFun := fun B => WithLp.toLp 2 (fun I =>
        ∑ K : Fin r → Fin d,
          A (Fin.append (fun i => I (Fin.castAdd m i)) K) *
            B (Fin.append K (fun j => I (Fin.natAdd n j))))
      map_add' := by
        intro B C
        apply PiLp.ext
        intro I
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c B
        apply PiLp.ext
        intro I
        simp [Finset.mul_sum, mul_left_comm] }
  map_add' := by
    intro A B
    apply LinearMap.ext
    intro C
    apply PiLp.ext
    intro I
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c A
    apply LinearMap.ext
    intro B
    apply PiLp.ext
    intro I
    simp [Finset.mul_sum, mul_assoc]

@[simp] theorem tensorContraction_apply {d n m r : Nat}
    (A : MomentTensor d (n + r)) (B : MomentTensor d (r + m))
    (I : Fin (n + m) → Fin d) :
    tensorContraction d n m r A B I =
      ∑ K : Fin r → Fin d,
        A (Fin.append (fun i => I (Fin.castAdd m i)) K) *
          B (Fin.append K (fun j => I (Fin.natAdd n j))) := rfl

/-- On pure powers each matched slot contributes exactly the original inner
product. The remaining slots form the unsymmetrized mixed tensor. -/
theorem tensorContraction_tensorPower {d n m r : Nat} (u v : Weight d) :
    tensorContraction d n m r (tensorPower (n + r) u) (tensorPower (r + m) v) =
      (inner Real u v) ^ r •
        mixedTensorMap d (n + m) (Fin.append (fun _ => u) (fun _ => v)) := by
  apply PiLp.ext
  intro I
  simp only [tensorContraction_apply, tensorPower_apply, Fin.prod_univ_add,
    Fin.append_left, Fin.append_right, PiLp.smul_apply, smul_eq_mul, mixedTensorMap_apply]
  have hs : (∑ K : Fin r → Fin d, (∏ j : Fin r, u (K j)) * ∏ j : Fin r, v (K j)) =
      (inner Real u v) ^ r := by
    simp only [← Finset.prod_mul_distrib]
    have hh := (Fintype.sum_pow (fun j : Fin d => u j * v j) r).symm
    simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm] using hh
  calc
    _ = ((∏ i : Fin n, u (I (Fin.castAdd m i))) *
        (∏ j : Fin m, v (I (Fin.natAdd n j)))) *
        (∑ K : Fin r → Fin d, (∏ j : Fin r, u (K j)) * ∏ j : Fin r, v (K j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro K _
      ring
    _ = _ := by rw [hs]; ring

/-- Zero matched slots give the literal coordinate tensor product, including
order-zero tensors and zero-dimensional spatial spaces. -/
theorem tensorContraction_zero_apply {d n m : Nat}
    (A : MomentTensor d (n + 0)) (B : MomentTensor d (0 + m))
    (I : Fin (n + m) → Fin d) :
    tensorContraction d n m 0 A B I =
      A (Fin.append (fun i => I (Fin.castAdd m i)) Fin.elim0) *
        B (Fin.append Fin.elim0 (fun j => I (Fin.natAdd n j))) := by
  simp only [tensorContraction_apply, Fintype.sum_unique]
  rfl

/-- Rewriting an order preserves every coordinate through the corresponding
finite-index cast. -/
@[simp] theorem tensorOrderEquiv_apply {d n m : Nat} (h : n = m)
    (T : MomentTensor d n) (I : Fin m → Fin d) :
    tensorOrderEquiv h T I = T (I ∘ Fin.cast h) := by
  subst m
  rfl

/-- Full contraction gives the actual Frobenius inner product as the unique
coordinate of an order-zero tensor. -/
theorem tensorContraction_full {d r : Nat} (A B : MomentTensor d r)
    (I : Fin (0 + 0) → Fin d) :
    tensorContraction d 0 0 r
      (tensorOrderEquiv (by omega : r = 0 + r) A)
      (tensorOrderEquiv (by omega : r = r + 0) B) I = inner Real A B := by
  simp only [tensorContraction_apply, tensorOrderEquiv_apply,
    Fin.append_left_nil, Fin.append_right_nil]
  simp [Function.comp_def, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- The symmetric contraction uses the actual orthogonal projection already
identified with the source's factorial-weighted permutation average. -/
noncomputable def symmetricTensorContraction (d n m r : Nat) :
    MomentTensor d (n + r) →ₗ[Real]
      MomentTensor d (r + m) →ₗ[Real] MomentTensor d (n + m) :=
  (tensorContraction d n m r).compr₂ (tensorSymmetrize d (n + m)).toLinearMap

@[simp] theorem symmetricTensorContraction_apply {d n m r : Nat}
    (A : MomentTensor d (n + r)) (B : MomentTensor d (r + m)) :
    symmetricTensorContraction d n m r A B =
      tensorSymmetrize d (n + m) (tensorContraction d n m r A B) := rfl

end PaperFormalization.MatrixFactorization
