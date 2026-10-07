import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

/-! # Actual spectral alignment of a finite covariance factor

For a real symmetric matrix M, the spectral sign is +1 at zero, hence it is
orthogonal even when M is singular. The aligned factor uses the actual positive
square root of C. All matrices have the same explicit finite index type n;
no invertibility, Gaussian law, transport optimality, or trace inequality is
assumed or asserted here.
-/

open Matrix Unitary
open scoped MatrixOrder

namespace PaperFormalization.Manuscript

/-- The source sign convention, including the zero eigenspace. -/
noncomputable def spectralSignPlus (a : ℝ) : ℝ := if a < 0 then -1 else 1

@[simp] theorem spectralSignPlus_zero : spectralSignPlus 0 = 1 := by
  simp [spectralSignPlus]

/-- Unlike the three-valued sign, signPlus has unit square at zero. -/
theorem spectralSignPlus_mul_self (a : ℝ) : spectralSignPlus a * spectralSignPlus a = 1 := by
  unfold spectralSignPlus
  split_ifs <;> norm_num

/-- The sign convention recovers the magnitude, including at zero. -/
theorem mul_spectralSignPlus (a : ℝ) : a * spectralSignPlus a = |a| := by
  unfold spectralSignPlus
  split_ifs with h
  · simp [abs_of_neg h]
  · simp [abs_of_nonneg (le_of_not_gt h)]

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Apply a real scalar function in an actual orthonormal eigenbasis of M. -/
noncomputable def sourceSpectralMatrix {M : Matrix n n ℝ} (hM : M.IsHermitian)
    (f : ℝ → ℝ) : Matrix n n ℝ :=
  conjStarAlgAut ℝ _ hM.eigenvectorUnitary (diagonal (fun i => f (hM.eigenvalues i)))

/-- The identity spectral function is exactly the original matrix. -/
theorem sourceSpectralMatrix_id {M : Matrix n n ℝ} (hM : M.IsHermitian) :
    sourceSpectralMatrix hM id = M := by
  simpa only [sourceSpectralMatrix, Function.comp_def, id_eq, RCLike.ofReal_real_eq_id] using
    hM.spectral_theorem.symm

/-- Products are evaluated in one unchanged eigenbasis. -/
theorem sourceSpectralMatrix_mul {M : Matrix n n ℝ} (hM : M.IsHermitian)
    (f g : ℝ → ℝ) :
    sourceSpectralMatrix hM f * sourceSpectralMatrix hM g =
      sourceSpectralMatrix hM (fun a => f a * g a) := by
  simp only [sourceSpectralMatrix, ← map_mul, diagonal_mul_diagonal]

/-- Every real spectral function of a real symmetric matrix is symmetric. -/
theorem sourceSpectralMatrix_transpose {M : Matrix n n ℝ} (hM : M.IsHermitian)
    (f : ℝ → ℝ) : (sourceSpectralMatrix hM f)ᵀ = sourceSpectralMatrix hM f := by
  rw [← conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose]
  simp only [sourceSpectralMatrix, ← map_star, star_eq_conjTranspose,
    diagonal_conjTranspose, star_trivial]

/-- The actual source orthogonal factor Q=U diag(signPlus lambda) Uᵀ. -/
noncomputable def alignedSignMatrix {M : Matrix n n ℝ} (hM : M.IsHermitian) :
    Matrix n n ℝ := sourceSpectralMatrix hM spectralSignPlus

/-- The absolute-value spectral matrix. Its identification with sqrt(M²) is
proved below, rather than imposed as an assumption. -/
noncomputable def spectralAbsoluteMatrix {M : Matrix n n ℝ} (hM : M.IsHermitian) :
    Matrix n n ℝ := sourceSpectralMatrix hM abs

/-- The constructed spectral sign is an involution, without nonsingularity. -/
theorem alignedSignMatrix_mul_self {M : Matrix n n ℝ} (hM : M.IsHermitian) :
    alignedSignMatrix hM * alignedSignMatrix hM = 1 := by
  rw [alignedSignMatrix, sourceSpectralMatrix_mul]
  simp [sourceSpectralMatrix, spectralSignPlus_mul_self]

/-- Both orthogonality identities follow from the construction itself. -/
theorem alignedSignMatrix_orthogonal {M : Matrix n n ℝ} (hM : M.IsHermitian) :
    alignedSignMatrix hM * (alignedSignMatrix hM)ᵀ = 1 ∧
      (alignedSignMatrix hM)ᵀ * alignedSignMatrix hM = 1 := by
  have ht : (alignedSignMatrix hM)ᵀ = alignedSignMatrix hM :=
    sourceSpectralMatrix_transpose hM spectralSignPlus
  rw [ht]
  exact ⟨alignedSignMatrix_mul_self hM, alignedSignMatrix_mul_self hM⟩

/-- Multiplying M by its constructed Q gives the actual spectral magnitude. -/
theorem mul_alignedSignMatrix {M : Matrix n n ℝ} (hM : M.IsHermitian) :
    M * alignedSignMatrix hM = spectralAbsoluteMatrix hM := by
  conv_lhs => lhs; rw [← sourceSpectralMatrix_id hM]
  change sourceSpectralMatrix hM id * sourceSpectralMatrix hM spectralSignPlus =
    sourceSpectralMatrix hM abs
  rw [sourceSpectralMatrix_mul]
  simp only [id_eq, mul_spectralSignPlus]

/-- The source identity M=|M|Q uses the same constructed factor. -/
theorem spectralAbsoluteMatrix_mul_alignedSignMatrix {M : Matrix n n ℝ}
    (hM : M.IsHermitian) : spectralAbsoluteMatrix hM * alignedSignMatrix hM = M := by
  rw [← mul_alignedSignMatrix hM, mul_assoc, alignedSignMatrix_mul_self, mul_one]

/-- Nonnegative spectral magnitudes yield a positive semidefinite matrix. -/
theorem spectralAbsoluteMatrix_posSemidef {M : Matrix n n ℝ} (hM : M.IsHermitian) :
    (spectralAbsoluteMatrix hM).PosSemidef := by
  unfold spectralAbsoluteMatrix sourceSpectralMatrix
  rw [conjStarAlgAut_apply, Unitary.isUnit_coe.posSemidef_star_right_conjugate_iff]
  exact posSemidef_diagonal_iff.mpr (fun i => abs_nonneg _)

/-- The constructed magnitude squares to M². -/
theorem spectralAbsoluteMatrix_mul_self {M : Matrix n n ℝ} (hM : M.IsHermitian) :
    spectralAbsoluteMatrix hM * spectralAbsoluteMatrix hM = M * M := by
  conv_rhs => rw [← sourceSpectralMatrix_id hM]
  change sourceSpectralMatrix hM abs * sourceSpectralMatrix hM abs =
    sourceSpectralMatrix hM id * sourceSpectralMatrix hM id
  rw [sourceSpectralMatrix_mul, sourceSpectralMatrix_mul]
  congr 1
  funext a
  simp only [id_eq, ← sq, sq_abs]

/-- Exact identification with the unique positive square root of M². -/
theorem spectralAbsoluteMatrix_eq_sqrt {M : Matrix n n ℝ} (hM : M.IsHermitian) :
    spectralAbsoluteMatrix hM = CFC.sqrt (M * M) := by
  exact (CFC.sqrt_unique (spectralAbsoluteMatrix_mul_self hM)
    (spectralAbsoluteMatrix_posSemidef hM).nonneg).symm

/-- The finite covariance factor from the manuscript, not an arbitrary factor. -/
noncomputable def alignedCovarianceFactor {M : Matrix n n ℝ} (hM : M.IsHermitian)
    (C : Matrix n n ℝ) : Matrix n n ℝ := CFC.sqrt C * alignedSignMatrix hM

/-- The aligned factor preserves the supplied positive semidefinite covariance. -/
theorem alignedCovarianceFactor_mul_transpose {M C : Matrix n n ℝ}
    (hM : M.IsHermitian) (hC : C.PosSemidef) :
    alignedCovarianceFactor hM C * (alignedCovarianceFactor hM C)ᵀ = C := by
  have hs : (CFC.sqrt C)ᵀ = CFC.sqrt C := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact (CFC.sqrt_nonneg C).posSemidef.isHermitian
  unfold alignedCovarianceFactor
  rw [transpose_mul, hs, mul_assoc, ← mul_assoc (alignedSignMatrix hM),
    (alignedSignMatrix_orthogonal hM).1, one_mul]
  exact CFC.sqrt_mul_sqrt_self C hC.nonneg

/-- The exact difference factorization is the basis for Frobenius invariance. -/
theorem alignedCovarianceFactor_sub {M C : Matrix n n ℝ} (hM : M.IsHermitian) :
    alignedCovarianceFactor hM C - M =
      (CFC.sqrt C - CFC.sqrt (M * M)) * alignedSignMatrix hM := by
  rw [sub_mul, ← spectralAbsoluteMatrix_eq_sqrt hM,
    spectralAbsoluteMatrix_mul_alignedSignMatrix]
  rfl

end PaperFormalization.Manuscript
