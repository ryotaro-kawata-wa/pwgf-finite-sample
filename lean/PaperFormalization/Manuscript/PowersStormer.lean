import PaperFormalization.Manuscript.SpectralTraceBounds
import PaperFormalization.Manuscript.FiniteHilbertSchmidt

/-! # Finite real Powers–Størmer inequality with the exact coefficient one

The nuclear value below is the actual trace of sqrt(XᵀX). We identify it with
the sum of absolute eigenvalues for symmetric matrices, but do not postulate a
Norm instance or its norm laws. The inequality is proved from spectral parts,
positive trace products and cyclicity; it is not an input hypothesis.
-/

open Matrix Unitary
open scoped MatrixOrder Matrix.Norms.Frobenius

namespace PaperFormalization.Manuscript

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual finite singular-value sum, expressed by its positive square
root trace. This is a value, not a postulated matrix Norm instance. -/
noncomputable def matrixNuclearValue (X : Matrix n n ℝ) : ℝ :=
  trace (CFC.sqrt (Xᵀ * X))

/-- A real spectral function has trace equal to its actual eigenvalue sum. -/
theorem trace_sourceSpectralMatrix {M : Matrix n n ℝ} (hM : M.IsHermitian)
    (f : ℝ → ℝ) : trace (sourceSpectralMatrix hM f) = ∑ i, f (hM.eigenvalues i) := by
  simp only [sourceSpectralMatrix, conjStarAlgAut_apply, trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, trace_diagonal]

/-- For a symmetric matrix the actual sqrt(XᵀX) is the spectral absolute value. -/
theorem matrixNuclearValue_eq_trace_spectralAbsoluteMatrix {X : Matrix n n ℝ}
    (hX : X.IsHermitian) : matrixNuclearValue X = trace (spectralAbsoluteMatrix hX) := by
  have ht : Xᵀ = X := by rw [← conjTranspose_eq_transpose_of_trivial]; exact hX
  rw [matrixNuclearValue, ht, ← spectralAbsoluteMatrix_eq_sqrt hX]

/-- In the symmetric case this is exactly the source sum of absolute
real eigenvalues, including multiplicities and zero eigenvalues. -/
theorem matrixNuclearValue_eq_sum_abs_eigenvalues {X : Matrix n n ℝ}
    (hX : X.IsHermitian) : matrixNuclearValue X = ∑ i, |hX.eigenvalues i| := by
  rw [matrixNuclearValue_eq_trace_spectralAbsoluteMatrix hX]
  exact trace_sourceSpectralMatrix hX abs

/-- The actual spectral sign commutes with M and gives its magnitude on the
left as well as on the right. -/
theorem alignedSignMatrix_mul {M : Matrix n n ℝ} (hM : M.IsHermitian) :
    alignedSignMatrix hM * M = spectralAbsoluteMatrix hM := by
  conv_lhs => rhs; rw [← sourceSpectralMatrix_id hM]
  change sourceSpectralMatrix hM spectralSignPlus * sourceSpectralMatrix hM id =
    sourceSpectralMatrix hM abs
  rw [sourceSpectralMatrix_mul]
  congr 1
  funext a
  simpa only [id_eq, mul_comm] using mul_spectralSignPlus a

/-- The exact source cyclic-trace identity; A and B need not commute. -/
theorem trace_sign_square_difference {A B : Matrix n n ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    trace (alignedSignMatrix (hA.sub hB) * (A * A - B * B)) =
      trace (spectralAbsoluteMatrix (hA.sub hB) * (A + B)) := by
  have hx : A * A - B * B = A * (A - B) + (A - B) * B := by noncomm_ring
  rw [hx, mul_add, trace_add, ← mul_assoc, trace_mul_cycle,
    mul_alignedSignMatrix (hA.sub hB), ← mul_assoc,
    alignedSignMatrix_mul (hA.sub hB), ← trace_add, ← mul_add]

/-- The lower trace bound follows from two genuine PSD trace products. This
is the algebraic positive/negative-part proof and assumes no scalar estimate. -/
theorem trace_square_sub_le_trace_absolute_sum {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    trace ((A - B) * (A - B)) ≤
      trace (spectralAbsoluteMatrix (hA.isHermitian.sub hB.isHermitian) * (A + B)) := by
  let hD := hA.isHermitian.sub hB.isHermitian
  have hp := trace_mul_nonneg_of_posSemidef (spectral_parts_posSemidef hD).1 hB
  have hn := trace_mul_nonneg_of_posSemidef (spectral_parts_posSemidef hD).2 hA
  have he : trace (spectralAbsoluteMatrix hD * (A + B)) -
      trace ((A - B) * (A - B)) =
      2 * (trace (spectralPositiveMatrix hD * B) + trace (spectralNegativeMatrix hD * A)) := by
    conv_lhs => lhs; arg 1; lhs; rw [← spectral_parts_add hD]
    conv_lhs => rhs; arg 1; lhs; rw [← spectral_parts_sub hD]
    simp only [add_mul, mul_add, sub_mul, mul_sub, trace_add, trace_sub]
    ring
  change trace ((A - B) * (A - B)) ≤ trace (spectralAbsoluteMatrix hD * (A + B))
  linarith

/-- The finite real Powers–Størmer trace inequality, derived with coefficient
one. Singular PSD matrices and the empty finite index type are allowed. -/
theorem powers_stormer_trace {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    trace ((A - B) * (A - B)) ≤ matrixNuclearValue (A * A - B * B) := by
  have hX : (A * A - B * B).IsHermitian := by
    simpa only [pow_two] using (hA.isHermitian.pow 2).sub (hB.isHermitian.pow 2)
  rw [matrixNuclearValue_eq_trace_spectralAbsoluteMatrix hX]
  calc
    _ ≤ trace (spectralAbsoluteMatrix (hA.isHermitian.sub hB.isHermitian) * (A + B)) :=
      trace_square_sub_le_trace_absolute_sum hA hB
    _ = trace (alignedSignMatrix (hA.isHermitian.sub hB.isHermitian) * (A * A - B * B)) :=
      (trace_sign_square_difference hA.isHermitian hB.isHermitian).symm
    _ ≤ trace (spectralAbsoluteMatrix hX) :=
      alignedSignMatrix_trace_mul_le (hA.isHermitian.sub hB.isHermitian) hX

/-- The source square-root form, using the genuine Frobenius norm. -/
theorem powers_stormer_sqrt_frobenius {C E : Matrix n n ℝ}
    (hC : C.PosSemidef) (hE : E.PosSemidef) :
    ‖CFC.sqrt C - CFC.sqrt E‖ ^ 2 ≤ matrixNuclearValue (C - E) := by
  have hA := (CFC.sqrt_nonneg C).posSemidef
  have hB := (CFC.sqrt_nonneg E).posSemidef
  have ht : (CFC.sqrt C - CFC.sqrt E)ᵀ = CFC.sqrt C - CFC.sqrt E := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact hA.isHermitian.sub hB.isHermitian
  rw [frobenius_norm_sq_eq_trace_mul_transpose, ht]
  simpa only [CFC.sqrt_mul_sqrt_self C hC.nonneg,
    CFC.sqrt_mul_sqrt_self E hE.nonneg] using powers_stormer_trace hA hB

/-- The source aligned factor difference has exactly the same Frobenius norm
as the difference of positive square roots. -/
theorem alignedCovarianceFactor_sub_frobenius {M C : Matrix n n ℝ}
    (hM : M.IsHermitian) :
    ‖alignedCovarianceFactor hM C - M‖ = ‖CFC.sqrt C - CFC.sqrt (M * M)‖ := by
  rw [alignedCovarianceFactor_sub hM]
  exact frobenius_norm_mul_orthogonal _ _ (alignedSignMatrix_orthogonal hM).1

/-- The full deterministic factor estimate from the source: actual aligned
B, exact covariance mismatch and coefficient one, without invertibility. -/
theorem alignedCovarianceFactor_frobenius_sq_le_nuclearValue {M C : Matrix n n ℝ}
    (hM : M.IsHermitian) (hC : C.PosSemidef) :
    ‖alignedCovarianceFactor hM C - M‖ ^ 2 ≤ matrixNuclearValue (C - M * M) := by
  have hMM : (M * M).PosSemidef := by
    simpa only [hM.eq] using posSemidef_conjTranspose_mul_self M
  rw [alignedCovarianceFactor_sub_frobenius hM]
  exact powers_stormer_sqrt_frobenius hC hMM

end PaperFormalization.Manuscript
