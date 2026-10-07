import PaperFormalization.Manuscript.PowersStormer

/-! # Symmetric nuclear-value bounds from actual spectral signs

Only symmetric nuclear values are needed for covariance differences. Their
bounds are derived from the actual trace/spectral construction, without
assuming general nuclear-norm triangle inequalities or a new Norm instance.
Rectangular factors use the actual Frobenius norm.
-/

open Matrix
open scoped MatrixOrder Matrix.Norms.Frobenius BigOperators

namespace PaperFormalization.Manuscript

variable {n d : Type*} [Fintype n] [DecidableEq n] [Fintype d]

/-- Left orthogonal multiplication preserves the actual rectangular Frobenius norm. -/
theorem frobenius_norm_orthogonal_mul (Q : Matrix n n ℝ) (A : Matrix n d ℝ)
    (hQ : Qᵀ * Q = 1) : ‖Q * A‖ = ‖A‖ := by
  rw [← frobenius_norm_transpose (Q * A), transpose_mul,
    frobenius_norm_mul_orthogonal Aᵀ Qᵀ (by simpa only [transpose_transpose] using hQ),
    frobenius_norm_transpose]

omit [DecidableEq n] in
/-- The actual rectangular Frobenius Cauchy–Schwarz trace bound. -/
theorem trace_mul_transpose_le_frobenius_mul (A B : Matrix n d ℝ) :
    trace (A * Bᵀ) ≤ ‖A‖ * ‖B‖ := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (n × d))
    (fun k => A k.1 k.2) (fun k => B k.1 k.2)
  have hA : (∑ k : n × d, A k.1 k.2 ^ 2) = ‖A‖ ^ 2 := by
    rw [frobenius_norm_sq]
    simp only [Fintype.sum_prod_type, Real.norm_eq_abs, sq_abs]
  have hB : (∑ k : n × d, B k.1 k.2 ^ 2) = ‖B‖ ^ 2 := by
    rw [frobenius_norm_sq]
    simp only [Fintype.sum_prod_type, Real.norm_eq_abs, sq_abs]
  rw [hA, hB, Real.sqrt_sq (norm_nonneg A), Real.sqrt_sq (norm_nonneg B)] at h
  simpa only [trace, diag, mul_apply, transpose_apply, Fintype.sum_prod_type] using h

/-- A symmetric nuclear value is attained by its actual constructed spectral sign. -/
theorem matrixNuclearValue_eq_trace_alignedSignMatrix {X : Matrix n n ℝ}
    (hX : X.IsHermitian) : matrixNuclearValue X = trace (alignedSignMatrix hX * X) := by
  rw [alignedSignMatrix_mul hX, matrixNuclearValue_eq_trace_spectralAbsoluteMatrix hX]

/-- The triangle inequality needed here is proved for actual symmetric values. -/
theorem matrixNuclearValue_add_le {X Y : Matrix n n ℝ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    matrixNuclearValue (X + Y) ≤ matrixNuclearValue X + matrixNuclearValue Y := by
  rw [matrixNuclearValue_eq_trace_alignedSignMatrix (hX.add hY), mul_add, trace_add]
  exact add_le_add
    ((alignedSignMatrix_trace_mul_le (hX.add hY) hX).trans_eq
      (matrixNuclearValue_eq_trace_spectralAbsoluteMatrix hX).symm)
    ((alignedSignMatrix_trace_mul_le (hX.add hY) hY).trans_eq
      (matrixNuclearValue_eq_trace_spectralAbsoluteMatrix hY).symm)

/-- Nonnegative scalar multiplication satisfies the exact coefficient bound;
this is enough for empirical averaging, without assuming nuclear norm laws. -/
theorem matrixNuclearValue_smul_le {X : Matrix n n ℝ} (hX : X.IsHermitian)
    (a : ℝ) (ha : 0 ≤ a) : matrixNuclearValue (a • X) ≤ a * matrixNuclearValue X := by
  have hAX : (a • X).IsHermitian := hX.smul (by simp [isSelfAdjoint_iff])
  rw [matrixNuclearValue_eq_trace_alignedSignMatrix hAX, Matrix.mul_smul, trace_smul,
    smul_eq_mul]
  exact mul_le_mul_of_nonneg_left
    ((alignedSignMatrix_trace_mul_le hAX hX).trans_eq
      (matrixNuclearValue_eq_trace_spectralAbsoluteMatrix hX).symm) ha

/-- Genuine symmetric nuclear values are nonnegative. -/
theorem matrixNuclearValue_nonneg_of_isHermitian {X : Matrix n n ℝ}
    (hX : X.IsHermitian) : 0 ≤ matrixNuclearValue X := by
  rw [matrixNuclearValue_eq_trace_spectralAbsoluteMatrix hX]
  exact (spectralAbsoluteMatrix_posSemidef hX).trace_nonneg

omit [Fintype n] [DecidableEq n] in
/-- The difference of two actual rectangular Gram matrices is symmetric. -/
theorem gram_sub_gram_isHermitian (A B : Matrix n d ℝ) :
    (A * Aᵀ - B * Bᵀ).IsHermitian := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    (isHermitian_mul_conjTranspose_self A).sub (isHermitian_mul_conjTranspose_self B)

/-- The exact covariance-product difference bound uses the actual sign of the
symmetric difference; no nonsymmetric nuclear-product estimate is assumed. -/
theorem matrixNuclearValue_gram_sub_gram_le (A B : Matrix n d ℝ) :
    matrixNuclearValue (A * Aᵀ - B * Bᵀ) ≤ ‖A - B‖ * (‖A‖ + ‖B‖) := by
  let hX := gram_sub_gram_isHermitian A B
  let Q := alignedSignMatrix hX
  have hQ : Qᵀ * Q = 1 := (alignedSignMatrix_orthogonal hX).2
  have hsplit : A * Aᵀ - B * Bᵀ = (A - B) * Aᵀ + B * (A - B)ᵀ := by
    rw [transpose_sub, Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [matrixNuclearValue_eq_trace_alignedSignMatrix hX]
  change trace (Q * (A * Aᵀ - B * Bᵀ)) ≤ _
  rw [hsplit, Matrix.mul_add, trace_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  change trace ((Q * (A - B)) * Aᵀ) + trace ((Q * B) * (A - B)ᵀ) ≤ _
  calc
    _ ≤ ‖Q * (A - B)‖ * ‖A‖ + ‖Q * B‖ * ‖A - B‖ :=
      add_le_add (trace_mul_transpose_le_frobenius_mul _ _) (trace_mul_transpose_le_frobenius_mul _ _)
    _ = ‖A - B‖ * (‖A‖ + ‖B‖) := by
      rw [frobenius_norm_orthogonal_mul Q (A - B) hQ, frobenius_norm_orthogonal_mul Q B hQ]
      ring

/-- The finite-sum bound follows from the single actual sign of the sum, so
there is no appeal to unproved general nuclear-norm properties. -/
theorem matrixNuclearValue_sum_le {ι : Type*} (s : Finset ι) (X : ι → Matrix n n ℝ)
    (hX : ∀ i ∈ s, (X i).IsHermitian) :
    matrixNuclearValue (∑ i ∈ s, X i) ≤ ∑ i ∈ s, matrixNuclearValue (X i) := by
  have hs : (∑ i ∈ s, X i).IsHermitian := isSelfAdjoint_sum s hX
  rw [matrixNuclearValue_eq_trace_alignedSignMatrix hs, Matrix.mul_sum, trace_sum]
  apply Finset.sum_le_sum
  intro i hi
  exact (alignedSignMatrix_trace_mul_le hs (hX i hi)).trans_eq
    (matrixNuclearValue_eq_trace_spectralAbsoluteMatrix (hX i hi)).symm

/-- Exact finite nonnegative weights, including empirical reciprocal-count
weights, retain their coefficients in the nuclear-value upper bound. -/
theorem matrixNuclearValue_weighted_sum_le {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) (X : ι → Matrix n n ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hX : ∀ i ∈ s, (X i).IsHermitian) :
    matrixNuclearValue (∑ i ∈ s, a i • X i) ≤ ∑ i ∈ s, a i * matrixNuclearValue (X i) := by
  exact (matrixNuclearValue_sum_le s (fun i => a i • X i)
    (fun i hi => (hX i hi).smul (by simp [isSelfAdjoint_iff]))).trans
    (Finset.sum_le_sum fun i hi => matrixNuclearValue_smul_le (hX i hi) (a i) (ha i hi))

end PaperFormalization.Manuscript
