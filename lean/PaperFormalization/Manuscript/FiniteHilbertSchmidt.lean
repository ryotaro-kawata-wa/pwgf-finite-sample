import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic

/-! # The actual finite Hilbert--Schmidt norm and its dimension factor

The norm is the L2 norm of a linear map's images of the standard Euclidean
orthonormal basis. It is the actual Frobenius norm for real matrices, not a
supremum norm on matrix entries. All input-dimension factors are explicit.
-/

open scoped BigOperators Matrix.Norms.Frobenius

namespace PaperFormalization.Manuscript

variable {ι F : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The finite Hilbert--Schmidt norm using the standard orthonormal basis. -/
noncomputable def finiteHilbertSchmidtNorm (A : EuclideanSpace ℝ ι →L[ℝ] F) : ℝ :=
  ‖(WithLp.toLp 2 (fun j => A (PiLp.single 2 j (1 : ℝ))) : PiLp 2 (fun _ : ι => F))‖

/-- The finite Hilbert--Schmidt norm is nonnegative. -/
theorem finiteHilbertSchmidtNorm_nonneg (A : EuclideanSpace ℝ ι →L[ℝ] F) :
    0 ≤ finiteHilbertSchmidtNorm A := norm_nonneg _

/-- Its squared value is exactly the sum of squared column norms. -/
theorem finiteHilbertSchmidtNorm_sq (A : EuclideanSpace ℝ ι →L[ℝ] F) :
    finiteHilbertSchmidtNorm A ^ 2 = ∑ j, ‖A (PiLp.single 2 j (1 : ℝ))‖ ^ 2 := by
  exact PiLp.norm_sq_eq_of_L2 _
    (WithLp.toLp 2 (fun j => A (PiLp.single 2 j (1 : ℝ))) : PiLp 2 (fun _ : ι => F))

/-- The Hilbert--Schmidt triangle inequality follows from the actual column vector. -/
theorem finiteHilbertSchmidtNorm_add_le (A B : EuclideanSpace ℝ ι →L[ℝ] F) :
    finiteHilbertSchmidtNorm (A + B) ≤ finiteHilbertSchmidtNorm A + finiteHilbertSchmidtNorm B := by
  exact norm_add_le
    (WithLp.toLp 2 (fun j => A (PiLp.single 2 j (1 : ℝ))) : PiLp 2 (fun _ : ι => F))
    (WithLp.toLp 2 (fun j => B (PiLp.single 2 j (1 : ℝ))))

/-- Scalar multiplication has its exact absolute-value factor. -/
theorem finiteHilbertSchmidtNorm_smul (a : ℝ) (A : EuclideanSpace ℝ ι →L[ℝ] F) :
    finiteHilbertSchmidtNorm (a • A) = |a| * finiteHilbertSchmidtNorm A := by
  unfold finiteHilbertSchmidtNorm
  have heq : (WithLp.toLp 2 (fun j => (a • A) (PiLp.single 2 j (1 : ℝ))) : PiLp 2 (fun _ : ι => F)) =
      a • (WithLp.toLp 2 (fun j => A (PiLp.single 2 j (1 : ℝ))) : PiLp 2 (fun _ : ι => F)) := by
    ext j
    rfl
  rw [heq, norm_smul, Real.norm_eq_abs]

/-- The exact dimension loss from operator norm to Hilbert--Schmidt norm. -/
theorem finiteHilbertSchmidtNorm_le_sqrt_card_mul (A : EuclideanSpace ℝ ι →L[ℝ] F) :
    finiteHilbertSchmidtNorm A ≤ Real.sqrt (Fintype.card ι) * ‖A‖ := by
  apply (sq_le_sq₀ (finiteHilbertSchmidtNorm_nonneg A) (by positivity)).mp
  rw [finiteHilbertSchmidtNorm_sq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  calc
    _ ≤ ∑ _j : ι, ‖A‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      apply pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      simpa only [PiLp.norm_single, norm_one, mul_one] using A.le_opNorm (PiLp.single 2 j (1 : ℝ))
    _ = _ := by simp

/-- Evaluation of a map is bounded by its genuine Hilbert--Schmidt norm. -/
theorem norm_apply_le_finiteHilbertSchmidtNorm_mul
    (A : EuclideanSpace ℝ ι →L[ℝ] F) (x : EuclideanSpace ℝ ι) :
    ‖A x‖ ≤ finiteHilbertSchmidtNorm A * ‖x‖ := by
  have hx : (∑ j, (x j) • PiLp.single 2 j (1 : ℝ)) = x := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun ι ℝ).sum_repr x
  calc
    ‖A x‖ = ‖∑ j, (x j) • A (PiLp.single 2 j (1 : ℝ))‖ := by
      have heq := congrArg A hx
      simpa only [map_sum, map_smul] using congrArg norm heq.symm
    _ ≤ ∑ j, ‖x j‖ * ‖A (PiLp.single 2 j (1 : ℝ))‖ := by
      simpa only [norm_smul] using norm_sum_le (Finset.univ) (fun j => (x j) • A (PiLp.single 2 j (1 : ℝ)))
    _ ≤ Real.sqrt (∑ j, ‖x j‖ ^ 2) * Real.sqrt (∑ j, ‖A (PiLp.single 2 j (1 : ℝ))‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = finiteHilbertSchmidtNorm A * ‖x‖ := by
      rw [← PiLp.norm_sq_eq_of_L2 _ x, ← finiteHilbertSchmidtNorm_sq A,
        Real.sqrt_sq (norm_nonneg x), Real.sqrt_sq (finiteHilbertSchmidtNorm_nonneg A)]
      ring

/-- The Euclidean operator norm is at most the actual Hilbert--Schmidt norm. -/
theorem opNorm_le_finiteHilbertSchmidtNorm (A : EuclideanSpace ℝ ι →L[ℝ] F) :
    ‖A‖ ≤ finiteHilbertSchmidtNorm A := by
  apply A.opNorm_le_bound (finiteHilbertSchmidtNorm_nonneg A)
  exact norm_apply_le_finiteHilbertSchmidtNorm_mul A


section Matrix

variable {κ : Type*} [Fintype κ]

/-- A real matrix acting between actual Euclidean L2 spaces. -/
noncomputable def matrixEuclideanOperator (M : Matrix κ ι ℝ) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ :=
  (Matrix.toEuclideanLin M).toContinuousLinearMap

/-- Standard-basis evaluation recovers the matrix's actual column. -/
theorem matrixEuclideanOperator_single (M : Matrix κ ι ℝ) (j : ι) (i : κ) :
    matrixEuclideanOperator M (PiLp.single 2 j (1 : ℝ)) i = M i j := by
  simp [matrixEuclideanOperator, Matrix.toEuclideanLin, Matrix.toLpLin_apply]

omit [DecidableEq ι] in
/-- Squaring the actual Frobenius norm gives its exact entry sum. -/
theorem frobenius_norm_sq (M : Matrix κ ι ℝ) :
    ‖M‖ ^ 2 = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp_rw [Real.rpow_two]
  exact Real.sq_sqrt (by positivity)

/-- The basis-defined norm is exactly the actual Frobenius matrix norm. -/
theorem finiteHilbertSchmidtNorm_matrix_eq_frobenius (M : Matrix κ ι ℝ) :
    finiteHilbertSchmidtNorm (matrixEuclideanOperator M) = ‖M‖ := by
  apply (sq_eq_sq₀ (finiteHilbertSchmidtNorm_nonneg _) (norm_nonneg _)).mp
  rw [finiteHilbertSchmidtNorm_sq, frobenius_norm_sq]
  simp_rw [PiLp.norm_sq_eq_of_L2, matrixEuclideanOperator_single]
  exact Finset.sum_comm

/-- Euclidean operator norm is at most Frobenius norm, without dimension loss. -/
theorem matrixEuclideanOperator_norm_le_frobenius (M : Matrix κ ι ℝ) :
    ‖matrixEuclideanOperator M‖ ≤ ‖M‖ := by
  rw [← finiteHilbertSchmidtNorm_matrix_eq_frobenius]
  exact opNorm_le_finiteHilbertSchmidtNorm _

/-- Frobenius norm is bounded by sqrt(input dimension) times operator norm. -/
theorem frobenius_le_sqrt_card_mul_matrixEuclideanOperator_norm (M : Matrix κ ι ℝ) :
    ‖M‖ ≤ Real.sqrt (Fintype.card ι) * ‖matrixEuclideanOperator M‖ := by
  rw [← finiteHilbertSchmidtNorm_matrix_eq_frobenius]
  exact finiteHilbertSchmidtNorm_le_sqrt_card_mul _

omit [DecidableEq ι] in
/-- The Frobenius norm squared is the actual trace of M Mᵀ. -/
theorem frobenius_norm_sq_eq_trace_mul_transpose (M : Matrix κ ι ℝ) :
    ‖M‖ ^ 2 = Matrix.trace (M * M.transpose) := by
  rw [frobenius_norm_sq]
  simp [Matrix.trace, Matrix.mul_apply, Real.norm_eq_abs, pow_two]

/-- Multiplication on the right by an orthogonal matrix preserves the
actual Frobenius norm, including singular matrices M. -/
theorem frobenius_norm_mul_orthogonal (M : Matrix κ ι ℝ) (Q : Matrix ι ι ℝ)
    (hQ : Q * Q.transpose = 1) : ‖M * Q‖ = ‖M‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [frobenius_norm_sq_eq_trace_mul_transpose, frobenius_norm_sq_eq_trace_mul_transpose]
  congr 1
  rw [Matrix.transpose_mul]
  calc
    (M * Q) * (Q.transpose * M.transpose) = M * (Q * Q.transpose) * M.transpose := by
      simp only [Matrix.mul_assoc]
    _ = M * M.transpose := by rw [hQ, Matrix.mul_one]


end Matrix

end PaperFormalization.Manuscript
