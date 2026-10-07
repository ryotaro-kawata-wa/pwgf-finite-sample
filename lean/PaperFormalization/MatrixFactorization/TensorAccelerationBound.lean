import PaperFormalization.MatrixFactorization.TensorJetBounds

/-! # MF35: tensor acceleration bound with an independent speed envelope

The normalized retraction has a nonconstant speed. An independent envelope
controls both its squared speed and ambient acceleration before integration.
-/
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Independent acceleration and squared-speed bounds retain the n-squared factor. -/
theorem tensorSecondJet_norm_le_of_bounds {d n : Nat} (w : UnitSphere d) (v a : Weight d)
    (B : Real) (hv : ‖v‖ ^ 2 ≤ B) (ha : ‖a‖ ≤ B) :
    ‖tensorSecondJet n w.val v a‖ ≤ (n : Real) ^ 2 * B := by
  have hterm (j k : Fin n) :
      ‖mixedTensorMap d n (Function.update (Function.update (fun _ => w.val) j v) k
        (if k = j then a else v))‖ ≤ B := by
    by_cases hk : k = j
    · subst k
      simpa only [↓reduceIte, Function.update_idem, mixedTensorMap_single_norm] using ha
    · rw [if_neg hk, mixedTensorMap_double_norm w v j k hk]
      exact hv
  calc
    ‖tensorSecondJet n w.val v a‖ ≤ ∑ j : Fin n, ‖∑ k : Fin n,
      mixedTensorMap d n (Function.update (Function.update (fun _ => w.val) j v) k
        (if k = j then a else v))‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, ∑ _k : Fin n, B := by
      apply Finset.sum_le_sum
      intro j hj
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k hk => hterm j k))
    _ = (n : Real) ^ 2 * B := by simp; ring

end PaperFormalization.MatrixFactorization
