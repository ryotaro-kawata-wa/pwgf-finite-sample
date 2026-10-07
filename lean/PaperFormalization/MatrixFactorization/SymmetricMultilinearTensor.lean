import PaperFormalization.MatrixFactorization.HermiteTensorLowOrder

/-! # MF45: symmetric multilinear forms and their actual tensor observations -/
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

/-- Symmetric real multilinear forms are determined by their actual diagonal
values, with the factorial supplied by the derivative of a polynomial. -/
theorem symmetricMultilinear_ext_of_diagonal {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] {n : Nat}
    (L M : ContinuousMultilinearMap Real (fun _ : Fin n => E) Real)
    (hL : ∀ v (e : Equiv.Perm (Fin n)), L (v ∘ e) = L v)
    (hM : ∀ v (e : Equiv.Perm (Fin n)), M (v ∘ e) = M v)
    (he : ∀ u : E, L (fun _ => u) = M (fun _ => u)) : L = M := by
  apply ContinuousMultilinearMap.ext
  intro v
  have hf : (fun u : E => L (fun _ => u)) = fun u => M (fun _ => u) := funext he
  have hd := congrArg (fun f : E → Real => iteratedFDeriv Real n f (0 : E) v) hf
  rw [L.iteratedFDeriv_comp_diagonal, M.iteratedFDeriv_comp_diagonal] at hd
  have hL' (e : Equiv.Perm (Fin n)) : L (fun i => v (e i)) = L v := hL v e
  have hM' (e : Equiv.Perm (Fin n)) : M (fun i => v (e i)) = M v := hM v e
  simp only [hL', hM', Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul] at hd
  exact mul_left_cancel₀ (by positivity : (n.factorial : Real) ≠ 0) hd

/-- Permuting vector slots is the inverse permutation of full tensor indices. -/
theorem mixedTensorMap_comp_perm {d n : Nat} (v : Fin n → Weight d)
    (e : Equiv.Perm (Fin n)) :
    mixedTensorMap d n (v ∘ e) = tensorPermute e.symm (mixedTensorMap d n v) := by
  apply PiLp.ext
  intro I
  simp only [mixedTensorMap_apply, tensorPermute_apply, Function.comp_apply]
  exact Fintype.prod_equiv e _ _ (fun j => by simp)

/-- Pairing against a symmetric tensor is symmetric in every vector slot. -/
theorem symmetricTensor_inner_mixed_perm {d n : Nat} (T : SymmetricMomentTensor d n)
    (v : Fin n → Weight d) (e : Equiv.Perm (Fin n)) :
    inner Real T.val (mixedTensorMap d n (v ∘ e)) = inner Real T.val (mixedTensorMap d n v) := by
  have ht : tensorPermute e.symm T.val = T.val := by
    apply PiLp.ext
    intro I
    exact T.property I e.symm
  rw [mixedTensorMap_comp_perm]
  have he := (tensorPermute (d := d) e.symm).inner_map_map T.val (mixedTensorMap d n v)
  rw [ht] at he
  exact he

end PaperFormalization.MatrixFactorization
