import PaperFormalization.MatrixFactorization.MixedTensorHilbert

/-! # MF33: actual first and second tensor derivatives along ambient curves

Both jets are differentiated from the original tensor-power path. The second
jet retains diagonal acceleration terms and all ordered distinct-slot terms.
-/
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def tensorFirstJet {d : Nat} (n : Nat) (w v : Weight d) : MomentTensor d n :=
  ∑ j : Fin n, mixedTensorMap d n (Function.update (fun _ => w) j v)

noncomputable def tensorSecondJet {d : Nat} (n : Nat) (w v a : Weight d) : MomentTensor d n :=
  ∑ j : Fin n, ∑ k : Fin n,
    mixedTensorMap d n (Function.update (Function.update (fun _ => w) j v) k
      (if k = j then a else v))

/-- First derivative of the literal tensor-power curve, also at degree zero. -/
theorem tensorPower_hasDerivAt {d n : Nat} {f : Real → Weight d} {v : Weight d}
    {t : Real} (hf : HasDerivAt f v t) :
    HasDerivAt (fun s => tensorPower n (f s)) (tensorFirstJet n (f t) v) t := by
  exact mixedTensorMap_hasDerivAt (fun _ : Fin n => hf)

/-- The derivative of the first jet contains the full ambient acceleration. -/
theorem tensorFirstJet_hasDerivAt {d n : Nat} {f v : Real → Weight d} {a : Weight d}
    {t : Real} (hf : HasDerivAt f (v t) t) (hv : HasDerivAt v a t) :
    HasDerivAt (fun s => tensorFirstJet n (f s) (v s))
      (tensorSecondJet n (f t) (v t) a) t := by
  apply HasDerivAt.fun_sum
  intro j hj
  apply mixedTensorMap_hasDerivAt
  intro k
  by_cases hk : k = j
  · subst k
    simpa only [Function.update_self, ↓reduceIte] using hv
  · simpa only [Function.update_of_ne hk, if_neg hk] using hf

/-- Tensor insertion preserves the exact single-slot norm on the unit sphere. -/
theorem mixedTensorMap_single_norm {d n : Nat} (w : UnitSphere d) (v : Weight d) (j : Fin n) :
    ‖mixedTensorMap d n (Function.update (fun _ => w.val) j v)‖ = ‖v‖ := by
  have hw : ‖w.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using w.property
  rw [mixedTensorMap_norm]
  simp [Function.update_apply, apply_ite, hw]

/-- The sharp degree factor has no ambient dimension factor. -/
theorem tensorFirstJet_norm_le {d n : Nat} (w : UnitSphere d) (v : Weight d) :
    ‖tensorFirstJet n w.val v‖ ≤ (n : Real) * ‖v‖ := by
  calc
    ‖tensorFirstJet n w.val v‖ ≤ ∑ j : Fin n,
      ‖mixedTensorMap d n (Function.update (fun _ => w.val) j v)‖ := norm_sum_le _ _
    _ = (n : Real) * ‖v‖ := by simp only [mixedTensorMap_single_norm, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end PaperFormalization.MatrixFactorization
