import PaperFormalization.MatrixFactorization.TensorCurveJets

/-! # MF33: sharp full-tensor jet bounds on the sphere

The acceleration hypothesis is satisfied exactly by spherical EXP. The bound
keeps the original n-squared coefficient and includes degree zero and one.
-/
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Two distinct slots contribute the product of their Euclidean norms. -/
theorem mixedTensorMap_double_norm {d n : Nat} (w : UnitSphere d) (v : Weight d)
    (j k : Fin n) (hkj : k ≠ j) :
    ‖mixedTensorMap d n (Function.update (Function.update (fun _ => w.val) j v) k v)‖ = ‖v‖ ^ 2 := by
  have hw : ‖w.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using w.property
  rw [mixedTensorMap_norm]
  have he (i : Fin n) :
      ‖Function.update (Function.update (fun _ : Fin n => w.val) j v) k v i‖ =
        (if i = j then ‖v‖ else 1) * (if i = k then ‖v‖ else 1) := by
    by_cases hij : i = j
    · subst i
      simp [Function.update_apply, hkj, Ne.symm hkj, hw]
    · by_cases hik : i = k
      · subst i
        simp [Function.update_apply, hkj, hw]
      · simp [Function.update_apply, hij, hik, hw]
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  simp [sq]

/-- Each ordered slot pair is bounded by the original squared speed. -/
theorem tensorSecondJet_term_norm_le {d n : Nat} (w : UnitSphere d) (v a : Weight d)
    (ha : ‖a‖ ≤ ‖v‖ ^ 2) (j k : Fin n) :
    ‖mixedTensorMap d n (Function.update (Function.update (fun _ => w.val) j v) k
      (if k = j then a else v))‖ ≤ ‖v‖ ^ 2 := by
  by_cases hk : k = j
  · subst k
    simpa only [↓reduceIte, Function.update_idem, mixedTensorMap_single_norm] using ha
  · rw [if_neg hk, mixedTensorMap_double_norm w v j k hk]

/-- The bound includes radial acceleration, with no sqrt(d) or tensor-size loss. -/
theorem tensorSecondJet_norm_le {d n : Nat} (w : UnitSphere d) (v a : Weight d)
    (ha : ‖a‖ ≤ ‖v‖ ^ 2) :
    ‖tensorSecondJet n w.val v a‖ ≤ (n : Real) ^ 2 * ‖v‖ ^ 2 := by
  calc
    ‖tensorSecondJet n w.val v a‖ ≤ ∑ j : Fin n, ‖∑ k : Fin n,
      mixedTensorMap d n (Function.update (Function.update (fun _ => w.val) j v) k
        (if k = j then a else v))‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, ∑ _k : Fin n, ‖v‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k hk =>
        tensorSecondJet_term_norm_le w v a ha j k))
    _ = (n : Real) ^ 2 * ‖v‖ ^ 2 := by simp; ring

/-- First jets depend continuously on their genuine tensor inputs. -/
theorem tensorFirstJet_continuous (d n : Nat) :
    Continuous (fun z : Weight d × Weight d => tensorFirstJet n z.1 z.2) := by
  unfold tensorFirstJet
  apply continuous_finsetSum
  intro j hj
  apply (mixedTensorMap d n).coe_continuous.comp
  apply continuous_pi
  intro k
  by_cases hk : k = j
  · simpa only [Function.update_self, hk] using continuous_snd
  · simpa only [Function.update_of_ne hk] using continuous_fst

/-- Continuity also retains the independent acceleration variable. -/
theorem tensorSecondJet_continuous (d n : Nat) :
    Continuous (fun z : (Weight d × Weight d) × Weight d => tensorSecondJet n z.1.1 z.1.2 z.2) := by
  unfold tensorSecondJet
  apply continuous_finsetSum
  intro j hj
  apply continuous_finsetSum
  intro k hk
  apply (mixedTensorMap d n).coe_continuous.comp
  apply continuous_pi
  intro i
  by_cases hik : i = k
  · subst i
    simp only [Function.update_self]
    split_ifs
    · exact continuous_snd
    · exact continuous_fst.snd
  · simp only [Function.update_of_ne hik]
    by_cases hij : i = j
    · subst i
      simpa only [Function.update_self] using continuous_fst.snd
    · simpa only [Function.update_of_ne hij] using continuous_fst.fst

end PaperFormalization.MatrixFactorization
