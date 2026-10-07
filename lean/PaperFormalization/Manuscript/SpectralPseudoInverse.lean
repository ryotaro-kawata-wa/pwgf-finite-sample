import PaperFormalization.Manuscript.SpectralTraceBounds

/-! # Actual generalized inverse of the aligned covariance factor

A symmetric spectral reciprocal is zero on the zero eigenspace (Lean's real
inverse has 0 inverse = 0). For the aligned B=sqrt(C)Q, its actual inverse is
Q times that spectral reciprocal. No nonsingularity or supplied inverse is
needed. Measurability as C,M vary is a subsequent obligation.
-/

open Matrix
open scoped MatrixOrder

namespace PaperFormalization.Manuscript

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual reciprocal spectral matrix, with zero mapped to zero. -/
noncomputable def symmetricPseudoInverse {S : Matrix n n ℝ} (hS : S.IsHermitian) : Matrix n n ℝ :=
  sourceSpectralMatrix hS (fun a => a⁻¹)

/-- The constructed reciprocal matrix is symmetric. -/
theorem symmetricPseudoInverse_transpose {S : Matrix n n ℝ} (hS : S.IsHermitian) :
    (symmetricPseudoInverse hS)ᵀ = symmetricPseudoInverse hS :=
  sourceSpectralMatrix_transpose hS _

/-- The reciprocal matrix commutes with its actual original symmetric matrix. -/
theorem symmetricPseudoInverse_commute {S : Matrix n n ℝ} (hS : S.IsHermitian) :
    S * symmetricPseudoInverse hS = symmetricPseudoInverse hS * S := by
  conv_lhs => lhs; rw [← sourceSpectralMatrix_id hS]
  conv_rhs => rhs; rw [← sourceSpectralMatrix_id hS]
  unfold symmetricPseudoInverse
  rw [sourceSpectralMatrix_mul, sourceSpectralMatrix_mul]
  congr 1
  funext a
  exact mul_comm _ _

/-- The first Penrose identity holds also at zero eigenvalues. -/
theorem symmetric_mul_pseudoInverse_mul {S : Matrix n n ℝ} (hS : S.IsHermitian) :
    S * symmetricPseudoInverse hS * S = S := by
  conv_lhs => lhs; lhs; rw [← sourceSpectralMatrix_id hS]
  conv_lhs => rhs; rw [← sourceSpectralMatrix_id hS]
  unfold symmetricPseudoInverse
  rw [sourceSpectralMatrix_mul, sourceSpectralMatrix_mul]
  convert sourceSpectralMatrix_id hS using 2
  funext a
  simp only [id_eq]
  by_cases ha : a = 0
  · simp [ha]
  · simp [ha]

/-- The second Penrose identity is also exact on the zero eigenspace. -/
theorem pseudoInverse_mul_symmetric_mul {S : Matrix n n ℝ} (hS : S.IsHermitian) :
    symmetricPseudoInverse hS * S * symmetricPseudoInverse hS = symmetricPseudoInverse hS := by
  conv_lhs => lhs; rhs; rw [← sourceSpectralMatrix_id hS]
  unfold symmetricPseudoInverse
  rw [sourceSpectralMatrix_mul, sourceSpectralMatrix_mul]
  congr 1
  funext a
  simp only [id_eq]
  by_cases ha : a = 0
  · simp [ha]
  · field_simp

/-- The range projector is an actual symmetric product. -/
theorem symmetric_range_projector_transpose {S : Matrix n n ℝ} (hS : S.IsHermitian) :
    (S * symmetricPseudoInverse hS)ᵀ = S * symmetricPseudoInverse hS := by
  have hs : Sᵀ = S := by rw [← conjTranspose_eq_transpose_of_trivial]; exact hS
  rw [transpose_mul, symmetricPseudoInverse_transpose, hs, ← symmetricPseudoInverse_commute]

/-- The range product is idempotent without invertibility. -/
theorem symmetric_range_projector_mul_self {S : Matrix n n ℝ} (hS : S.IsHermitian) :
    (S * symmetricPseudoInverse hS) * (S * symmetricPseudoInverse hS) = S * symmetricPseudoInverse hS := by
  rw [← mul_assoc, symmetric_mul_pseudoInverse_mul]

/-- The actual source aligned inverse is Q times the reciprocal of sqrt(C). -/
noncomputable def alignedCovariancePseudoInverse {M : Matrix n n ℝ} (hM : M.IsHermitian)
    (C : Matrix n n ℝ) : Matrix n n ℝ :=
  alignedSignMatrix hM * symmetricPseudoInverse (CFC.sqrt_nonneg C).posSemidef.isHermitian

/-- The covariance-side projector has exactly the spectral range of sqrt(C). -/
theorem aligned_factor_mul_pseudoInverse {M : Matrix n n ℝ} (hM : M.IsHermitian) (C : Matrix n n ℝ) :
    alignedCovarianceFactor hM C * alignedCovariancePseudoInverse hM C =
      CFC.sqrt C * symmetricPseudoInverse (CFC.sqrt_nonneg C).posSemidef.isHermitian := by
  unfold alignedCovarianceFactor alignedCovariancePseudoInverse
  rw [mul_assoc, ← mul_assoc (alignedSignMatrix hM), alignedSignMatrix_mul_self, one_mul]

/-- The constructed aligned inverse satisfies B D B=B. -/
theorem aligned_factor_pseudoInverse_factor {M : Matrix n n ℝ} (hM : M.IsHermitian) (C : Matrix n n ℝ) :
    alignedCovarianceFactor hM C * alignedCovariancePseudoInverse hM C * alignedCovarianceFactor hM C =
      alignedCovarianceFactor hM C := by
  rw [aligned_factor_mul_pseudoInverse, alignedCovarianceFactor, ← mul_assoc,
    symmetric_mul_pseudoInverse_mul]

/-- The constructed aligned inverse satisfies D B D=D. -/
theorem aligned_pseudoInverse_factor_pseudoInverse {M : Matrix n n ℝ} (hM : M.IsHermitian) (C : Matrix n n ℝ) :
    alignedCovariancePseudoInverse hM C * alignedCovarianceFactor hM C * alignedCovariancePseudoInverse hM C =
      alignedCovariancePseudoInverse hM C := by
  rw [mul_assoc, aligned_factor_mul_pseudoInverse]
  unfold alignedCovariancePseudoInverse
  simp only [mul_assoc]
  rw [← mul_assoc (symmetricPseudoInverse (CFC.sqrt_nonneg C).posSemidef.isHermitian),
    pseudoInverse_mul_symmetric_mul]

/-- The actual covariance-side range projector is symmetric. -/
theorem aligned_factor_pseudoInverse_transpose {M : Matrix n n ℝ} (hM : M.IsHermitian) (C : Matrix n n ℝ) :
    (alignedCovarianceFactor hM C * alignedCovariancePseudoInverse hM C)ᵀ =
      alignedCovarianceFactor hM C * alignedCovariancePseudoInverse hM C := by
  rw [aligned_factor_mul_pseudoInverse]
  exact symmetric_range_projector_transpose _

/-- The actual seed-side range projector is symmetric. -/
theorem aligned_pseudoInverse_factor_transpose {M : Matrix n n ℝ} (hM : M.IsHermitian) (C : Matrix n n ℝ) :
    (alignedCovariancePseudoInverse hM C * alignedCovarianceFactor hM C)ᵀ =
      alignedCovariancePseudoInverse hM C * alignedCovarianceFactor hM C := by
  have hs : (CFC.sqrt C)ᵀ = CFC.sqrt C := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact (CFC.sqrt_nonneg C).posSemidef.isHermitian
  have hq : (alignedSignMatrix hM)ᵀ = alignedSignMatrix hM :=
    sourceSpectralMatrix_transpose hM spectralSignPlus
  unfold alignedCovarianceFactor alignedCovariancePseudoInverse
  rw [transpose_mul, transpose_mul, transpose_mul, symmetricPseudoInverse_transpose, hs]
  change (alignedSignMatrix hM)ᵀ * CFC.sqrt C *
    (symmetricPseudoInverse (CFC.sqrt_nonneg C).posSemidef.isHermitian * (alignedSignMatrix hM)ᵀ) = _
  rw [hq, mul_assoc, ← mul_assoc (CFC.sqrt C), symmetricPseudoInverse_commute]
  simp only [mul_assoc]

/-- The actual seed-side projector is idempotent. -/
theorem aligned_seed_projector_mul_self {M : Matrix n n ℝ} (hM : M.IsHermitian) (C : Matrix n n ℝ) :
    (alignedCovariancePseudoInverse hM C * alignedCovarianceFactor hM C) *
      (alignedCovariancePseudoInverse hM C * alignedCovarianceFactor hM C) =
        alignedCovariancePseudoInverse hM C * alignedCovarianceFactor hM C := by
  rw [← mul_assoc, aligned_pseudoInverse_factor_pseudoInverse]

/-- The orthogonal complement contributes nothing to the population update. -/
theorem aligned_factor_mul_seed_complement {M : Matrix n n ℝ} (hM : M.IsHermitian) (C : Matrix n n ℝ) :
    alignedCovarianceFactor hM C *
      (1 - alignedCovariancePseudoInverse hM C * alignedCovarianceFactor hM C) = 0 := by
  rw [mul_sub, mul_one, ← mul_assoc, aligned_factor_pseudoInverse_factor, sub_self]

end PaperFormalization.Manuscript
