import PaperFormalization.Manuscript.AlignedCovarianceFactor

/-! # Finite spectral parts and the trace bound needed for Powers–Størmer

The positive and negative parts are constructed in the matrix's actual
orthonormal eigenbasis. Positivity of a trace product is proved using an
actual PSD square root; it does not assume that a product of PSD matrices is
PSD. The eventual sign matrix is the derived orthogonal spectral sign.
-/

open Matrix Unitary
open scoped MatrixOrder

namespace PaperFormalization.Manuscript

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The constant-one spectral function gives the identity matrix. -/
theorem sourceSpectralMatrix_one {M : Matrix n n ℝ} (hM : M.IsHermitian) :
    sourceSpectralMatrix hM (fun _ => 1) = 1 := by
  simp [sourceSpectralMatrix]

/-- Addition of scalar spectral functions is actual matrix addition. -/
theorem sourceSpectralMatrix_add {M : Matrix n n ℝ} (hM : M.IsHermitian)
    (f g : ℝ → ℝ) :
    sourceSpectralMatrix hM f + sourceSpectralMatrix hM g =
      sourceSpectralMatrix hM (fun a => f a + g a) := by
  simp only [sourceSpectralMatrix, ← map_add, ← diagonal_add]

/-- Subtraction of scalar spectral functions is actual matrix subtraction. -/
theorem sourceSpectralMatrix_sub {M : Matrix n n ℝ} (hM : M.IsHermitian)
    (f g : ℝ → ℝ) :
    sourceSpectralMatrix hM f - sourceSpectralMatrix hM g =
      sourceSpectralMatrix hM (fun a => f a - g a) := by
  simp only [sourceSpectralMatrix, ← map_sub, ← diagonal_sub]

/-- Nonnegativity is needed only on the actual spectrum. -/
theorem sourceSpectralMatrix_posSemidef {M : Matrix n n ℝ} (hM : M.IsHermitian)
    (f : ℝ → ℝ) (hf : ∀ i, 0 ≤ f (hM.eigenvalues i)) :
    (sourceSpectralMatrix hM f).PosSemidef := by
  unfold sourceSpectralMatrix
  rw [conjStarAlgAut_apply, Unitary.isUnit_coe.posSemidef_star_right_conjugate_iff]
  exact posSemidef_diagonal_iff.mpr hf

/-- The trace of the product of two PSD matrices is nonnegative, even when
the product is not symmetric. No simultaneous diagonalization is assumed. -/
theorem trace_mul_nonneg_of_posSemidef {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ trace (A * B) := by
  have hs : (CFC.sqrt A)ᴴ = CFC.sqrt A := (CFC.sqrt_nonneg A).posSemidef.isHermitian
  have h := (hB.mul_mul_conjTranspose_same (CFC.sqrt A)).trace_nonneg
  rw [hs, trace_mul_cycle, CFC.sqrt_mul_sqrt_self A hA.nonneg] at h
  exact h

/-- The positive spectral part, including zero eigenvalues. -/
noncomputable def spectralPositiveMatrix {M : Matrix n n ℝ} (hM : M.IsHermitian) :
    Matrix n n ℝ := sourceSpectralMatrix hM (fun a => max a 0)

/-- The negative spectral part has nonnegative eigenvalues max(-lambda,0). -/
noncomputable def spectralNegativeMatrix {M : Matrix n n ℝ} (hM : M.IsHermitian) :
    Matrix n n ℝ := sourceSpectralMatrix hM (fun a => max (-a) 0)

/-- Both constructed spectral parts are PSD. -/
theorem spectral_parts_posSemidef {M : Matrix n n ℝ} (hM : M.IsHermitian) :
    (spectralPositiveMatrix hM).PosSemidef ∧ (spectralNegativeMatrix hM).PosSemidef :=
  ⟨sourceSpectralMatrix_posSemidef hM _ (fun _ => le_max_right _ _),
    sourceSpectralMatrix_posSemidef hM _ (fun _ => le_max_right _ _)⟩

/-- Exact positive-minus-negative decomposition of the original matrix. -/
theorem spectral_parts_sub {M : Matrix n n ℝ} (hM : M.IsHermitian) :
    spectralPositiveMatrix hM - spectralNegativeMatrix hM = M := by
  rw [spectralPositiveMatrix, spectralNegativeMatrix, sourceSpectralMatrix_sub]
  convert sourceSpectralMatrix_id hM using 2
  funext a
  simp only [id_eq]
  by_cases ha : 0 ≤ a
  · rw [max_eq_left ha, max_eq_right (neg_nonpos.mpr ha), sub_zero]
  · rw [max_eq_right (le_of_not_ge ha), max_eq_left (by linarith : 0 ≤ -a)]
    ring

/-- Exact positive-plus-negative decomposition of the spectral absolute value. -/
theorem spectral_parts_add {M : Matrix n n ℝ} (hM : M.IsHermitian) :
    spectralPositiveMatrix hM + spectralNegativeMatrix hM = spectralAbsoluteMatrix hM := by
  rw [spectralPositiveMatrix, spectralNegativeMatrix, spectralAbsoluteMatrix,
    sourceSpectralMatrix_add]
  congr 1
  funext a
  by_cases ha : 0 ≤ a
  · rw [max_eq_left ha, max_eq_right (neg_nonpos.mpr ha), abs_of_nonneg ha, add_zero]
  · rw [max_eq_right (le_of_not_ge ha), max_eq_left (by linarith : 0 ≤ -a),
      abs_of_neg (lt_of_not_ge ha), zero_add]

/-- The actual signPlus matrix obeys both order-contraction inequalities.
These follow from its explicit eigenvalues, not a supplied norm bound. -/
theorem one_sub_add_alignedSignMatrix_posSemidef {M : Matrix n n ℝ}
    (hM : M.IsHermitian) :
    (1 - alignedSignMatrix hM).PosSemidef ∧ (1 + alignedSignMatrix hM).PosSemidef := by
  have hm : 1 - alignedSignMatrix hM =
      sourceSpectralMatrix hM (fun a => 1 - spectralSignPlus a) := by
    conv_lhs => lhs; rw [← sourceSpectralMatrix_one hM]
    exact sourceSpectralMatrix_sub hM _ _
  have hp : 1 + alignedSignMatrix hM =
      sourceSpectralMatrix hM (fun a => 1 + spectralSignPlus a) := by
    conv_lhs => lhs; rw [← sourceSpectralMatrix_one hM]
    exact sourceSpectralMatrix_add hM _ _
  rw [hm, hp]
  constructor <;> apply sourceSpectralMatrix_posSemidef hM <;> intro i <;>
    unfold spectralSignPlus <;> split_ifs <;> norm_num

/-- A finite trace-dual inequality for a symmetric X and a matrix J with
PSD(1-J) and PSD(1+J). No nuclear norm instance is postulated. -/
theorem trace_mul_le_trace_spectralAbsoluteMatrix {X J : Matrix n n ℝ}
    (hX : X.IsHermitian) (hminus : (1 - J).PosSemidef) (hplus : (1 + J).PosSemidef) :
    trace (J * X) ≤ trace (spectralAbsoluteMatrix hX) := by
  have hp := trace_mul_nonneg_of_posSemidef hminus (spectral_parts_posSemidef hX).1
  have hn := trace_mul_nonneg_of_posSemidef hplus (spectral_parts_posSemidef hX).2
  simp only [sub_mul, add_mul, one_mul, trace_sub, trace_add] at hp hn
  conv_lhs => arg 1; rhs; rw [← spectral_parts_sub hX]
  conv_rhs => arg 1; rw [← spectral_parts_add hX]
  rw [mul_sub, trace_sub, trace_add]
  linarith

/-- The trace-dual bound applies to the actual constructed spectral sign of
any symmetric D, regardless of any commutation between D and X. -/
theorem alignedSignMatrix_trace_mul_le {D X : Matrix n n ℝ}
    (hD : D.IsHermitian) (hX : X.IsHermitian) :
    trace (alignedSignMatrix hD * X) ≤ trace (spectralAbsoluteMatrix hX) :=
  trace_mul_le_trace_spectralAbsoluteMatrix hX
    (one_sub_add_alignedSignMatrix_posSemidef hD).1
    (one_sub_add_alignedSignMatrix_posSemidef hD).2

end PaperFormalization.Manuscript
