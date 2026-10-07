import PaperFormalization.Manuscript.FiniteHilbertSchmidt

/-! # Orthogonal mixing of finite Hilbert columns

Columns are mixed on the right: the i-th new column is Σ_j Q_{j i} v_j.
The exact relation Q Qᵀ = I preserves the total inner pairing and the sum
of squared column norms. The Hilbert target can be infinite-dimensional
and incomplete, and the finite index type may be empty.
-/

open scoped BigOperators InnerProductSpace

namespace PaperFormalization.Manuscript

variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The actual columns of right multiplication by a real matrix. -/
noncomputable def orthogonalHilbertColumns (Q : Matrix ι ι ℝ) (v : ι → H) (i : ι) : H :=
  ∑ j, Q j i • v j

/-- A right orthogonal mixing preserves the total real inner pairing. -/
theorem orthogonalHilbertColumns_inner_sum (Q : Matrix ι ι ℝ)
    (hQ : Q * Q.transpose = 1) (v u : ι → H) :
    (∑ i, ⟪orthogonalHilbertColumns Q v i, orthogonalHilbertColumns Q u i⟫_ℝ) =
      ∑ i, ⟪v i, u i⟫_ℝ := by
  have hentry (j k : ι) : (∑ i, Q j i * Q k i) = if j = k then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      congrArg (fun A : Matrix ι ι ℝ => A j k) hQ
  simp only [orthogonalHilbertColumns, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, ← mul_assoc]
  calc
    (∑ i, ∑ j, ∑ k, Q j i * Q k i * ⟪v k, u j⟫_ℝ) =
        ∑ j, ∑ k, (∑ i, Q j i * Q k i) * ⟪v k, u j⟫_ℝ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = ∑ i, ⟪v i, u i⟫_ℝ := by simp [hentry]

/-- No dimension factor occurs in the exact column energy identity. -/
theorem orthogonalHilbertColumns_norm_sq_sum (Q : Matrix ι ι ℝ)
    (hQ : Q * Q.transpose = 1) (v : ι → H) :
    (∑ i, ‖orthogonalHilbertColumns Q v i‖ ^ 2) = ∑ i, ‖v i‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using orthogonalHilbertColumns_inner_sum Q hQ v v

/-- The actual finite L2 column norm is preserved. -/
theorem orthogonalHilbertColumns_piLp_norm (Q : Matrix ι ι ℝ)
    (hQ : Q * Q.transpose = 1) (v : ι → H) :
    ‖(WithLp.toLp 2 (orthogonalHilbertColumns Q v) : PiLp 2 (fun _ : ι => H))‖ =
      ‖(WithLp.toLp 2 v : PiLp 2 (fun _ : ι => H))‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [PiLp.norm_sq_eq_of_L2] using orthogonalHilbertColumns_norm_sq_sum Q hQ v

/-- This exact column bound is the tensor triangle-inequality reduction used
in finite nuclear compression. Its right side is the original column energy. -/
theorem orthogonalHilbertColumns_sum_norm_mul_le (Q : Matrix ι ι ℝ)
    (hQ : Q * Q.transpose = 1) (v : ι → H) :
    (∑ i, ‖v i‖ * ‖orthogonalHilbertColumns Q v i‖) ≤ ∑ i, ‖v i‖ ^ 2 := by
  calc
    _ ≤ Real.sqrt (∑ i, ‖v i‖ ^ 2) *
        Real.sqrt (∑ i, ‖orthogonalHilbertColumns Q v i‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by
      rw [orthogonalHilbertColumns_norm_sq_sum Q hQ v, ← sq,
        Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg ‖v i‖))]

end PaperFormalization.Manuscript
