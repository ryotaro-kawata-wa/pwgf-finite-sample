import PaperFormalization.Manuscript.SourceCanonicalWhitening
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! # Choice-free permutation equivariance of the FIXED spectral whitening rule
M13r verified unit (see CODEX_HANDOFF_M13R.md). These identities are obtained from square-root uniqueness and
commuting reflexive-inverse uniqueness. No coherent eigenvector choice or
nonzero/same-rank hypothesis is used. The PSD totalization is equivariant too.
-/
open Matrix
open scoped MatrixOrder BigOperators Matrix.Norms.L2Operator
namespace PaperFormalization.Manuscript
set_option backward.isDefEq.respectTransparency false
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Pull every row and column through the same permutation. -/
abbrev sourceMatrixPermute (s : Equiv.Perm I) : Matrix I I Real ≃ₐ[Real] Matrix I I Real :=
  Matrix.reindexAlgEquiv Real Real s.symm

@[simp] theorem sourceMatrixPermute_apply (s : Equiv.Perm I) (M : Matrix I I Real) (i j : I) :
    sourceMatrixPermute s M i j = M (s i) (s j) := rfl

/-- Positive square roots commute with simultaneous index permutation. -/
theorem source_sqrt_permute (s : Equiv.Perm I) (C : Matrix I I Real) (hC : C.PosSemidef) :
    CFC.sqrt (sourceMatrixPermute s C) = sourceMatrixPermute s (CFC.sqrt C) := by
  apply CFC.sqrt_unique
  · rw [← map_mul, CFC.sqrt_mul_sqrt_self C hC.nonneg]
  · exact ((CFC.sqrt_nonneg C).posSemidef.submatrix s).nonneg

/-- Generalized inverses commute with permutation even at rank changes. -/
theorem source_symmetricPseudoInverse_permute (s : Equiv.Perm I)
    {M : Matrix I I Real} (hM : M.IsHermitian) :
    symmetricPseudoInverse (hM.submatrix s) = sourceMatrixPermute s (symmetricPseudoInverse hM) := by
  let e := sourceMatrixPermute s
  apply commuting_reflexive_inverse_unique (e M)
  · exact (symmetricPseudoInverse_commute (hM.submatrix s)).symm
  · simpa only [map_mul] using congrArg e (symmetricPseudoInverse_commute hM).symm
  · exact symmetric_mul_pseudoInverse_mul (hM.submatrix s)
  · exact pseudoInverse_mul_symmetric_mul (hM.submatrix s)
  · simpa only [map_mul] using congrArg e (symmetric_mul_pseudoInverse_mul hM)
  · simpa only [map_mul] using congrArg e (pseudoInverse_mul_symmetric_mul hM)

theorem source_spectralAbsoluteMatrix_permute (s : Equiv.Perm I)
    {M : Matrix I I Real} (hM : M.IsHermitian) :
    spectralAbsoluteMatrix (hM.submatrix s) = sourceMatrixPermute s (spectralAbsoluteMatrix hM) := by
  rw [spectralAbsoluteMatrix_eq_sqrt (hM.submatrix s)]
  apply CFC.sqrt_unique
  · change sourceMatrixPermute s (spectralAbsoluteMatrix hM) *
      sourceMatrixPermute s (spectralAbsoluteMatrix hM) =
      sourceMatrixPermute s M * sourceMatrixPermute s M
    simpa only [map_mul] using congrArg (sourceMatrixPermute s) (spectralAbsoluteMatrix_mul_self hM)
  · exact ((spectralAbsoluteMatrix_posSemidef hM).submatrix s).nonneg

/-- The signPlus value on the null eigenspace is preserved, not dropped. -/
theorem source_alignedSignMatrix_permute (s : Equiv.Perm I)
    {M : Matrix I I Real} (hM : M.IsHermitian) :
    alignedSignMatrix (hM.submatrix s) = sourceMatrixPermute s (alignedSignMatrix hM) := by
  have habs := source_spectralAbsoluteMatrix_permute s hM
  have hinv : symmetricPseudoInverse (spectralAbsoluteMatrix_posSemidef (hM.submatrix s)).isHermitian =
      sourceMatrixPermute s (symmetricPseudoInverse (spectralAbsoluteMatrix_posSemidef hM).isHermitian) := by
    have hcongr {A B : Matrix I I Real} (hA : A.IsHermitian) (hB : B.IsHermitian)
        (he : A = B) : symmetricPseudoInverse hA = symmetricPseudoInverse hB := by
      subst B
      rfl
    exact (hcongr _ _ habs).trans
      (source_symmetricPseudoInverse_permute s (spectralAbsoluteMatrix_posSemidef hM).isHermitian)
  rw [alignedSignMatrix_reciprocal_formula, alignedSignMatrix_reciprocal_formula]
  rw [hinv, habs]
  simp only [map_sub, map_add, map_one, map_mul]
  rfl

theorem source_alignedCovarianceFactor_permute (s : Equiv.Perm I)
    {M : Matrix I I Real} (hM : M.IsHermitian) (C : Matrix I I Real) (hC : C.PosSemidef) :
    alignedCovarianceFactor (hM.submatrix s) (sourceMatrixPermute s C) =
      sourceMatrixPermute s (alignedCovarianceFactor hM C) := by
  unfold alignedCovarianceFactor
  rw [source_sqrt_permute s C hC, source_alignedSignMatrix_permute s hM, map_mul]

theorem source_alignedCovariancePseudoInverse_permute (s : Equiv.Perm I)
    {M : Matrix I I Real} (hM : M.IsHermitian) (C : Matrix I I Real) (hC : C.PosSemidef) :
    alignedCovariancePseudoInverse (hM.submatrix s) (sourceMatrixPermute s C) =
      sourceMatrixPermute s (alignedCovariancePseudoInverse hM C) := by
  unfold alignedCovariancePseudoInverse
  have hcongr {A B : Matrix I I Real} (hA : A.IsHermitian) (hB : B.IsHermitian)
      (he : A = B) : symmetricPseudoInverse hA = symmetricPseudoInverse hB := by
    subst B
    rfl
  have hinv := (hcongr (CFC.sqrt_nonneg _).posSemidef.isHermitian _ (source_sqrt_permute s C hC)).trans
    (source_symmetricPseudoInverse_permute s (CFC.sqrt_nonneg C).posSemidef.isHermitian)
  rw [source_alignedSignMatrix_permute s hM, hinv, map_mul]

/-- No actual integral is replaced by the clip: this is only the total rule's
algebraic equivariance, for both the PSD and the non-PSD cases. -/
theorem sourcePsdClip_permute (s : Equiv.Perm I) (C : Matrix I I Real) :
    sourcePsdClip (sourceMatrixPermute s C) = sourceMatrixPermute s (sourcePsdClip C) := by
  classical
  by_cases hc : C.PosSemidef
  · rw [sourcePsdClip_eq C hc]
    exact sourcePsdClip_eq _ (hc.submatrix s)
  · have he : ¬ (sourceMatrixPermute s C).PosSemidef := by
      intro hh
      exact hc ((posSemidef_submatrix_equiv s).mp hh)
    simp only [sourcePsdClip, if_neg hc, if_neg he, map_zero]

def sourceEuclideanPermute (s : Equiv.Perm I) (v : EuclideanSpace Real I) : EuclideanSpace Real I :=
  WithLp.toLp 2 (fun i => v (s i))

/-- A reindexed matrix acts on the reindexed vector by reindexing the action. -/
theorem source_toEuclideanCLM_permute (s : Equiv.Perm I) (M : Matrix I I Real)
    (v : EuclideanSpace Real I) :
    Matrix.toEuclideanCLM (𝕜 := Real) (sourceMatrixPermute s M) (sourceEuclideanPermute s v) =
      sourceEuclideanPermute s (Matrix.toEuclideanCLM (𝕜 := Real) M v) := by
  ext i
  change (∑ j, M (s i) (s j) * v (s j)) = ∑ j, M (s i) j * v j
  exact Fintype.sum_equiv s _ _ (fun _ => rfl)

/-- The recursively fixed seed is equivariant, including singular/zero cases. -/
theorem sourceCanonicalWhiteningSeed_permute (s : Equiv.Perm I)
    {M : Matrix I I Real} (hM : M.IsHermitian) (C : Matrix I I Real)
    (v a : EuclideanSpace Real I) :
    sourceCanonicalWhiteningSeed (sourceMatrixPermute s M) (hM.submatrix s)
      (sourceMatrixPermute s C) (sourceEuclideanPermute s v) (sourceEuclideanPermute s a) =
      sourceEuclideanPermute s (sourceCanonicalWhiteningSeed M hM C v a) := by
  have hb := source_alignedCovarianceFactor_permute s hM (sourcePsdClip C) (sourcePsdClip_pos C)
  have hd := source_alignedCovariancePseudoInverse_permute s hM (sourcePsdClip C) (sourcePsdClip_pos C)
  unfold sourceCanonicalWhiteningSeed
  rw [sourcePsdClip_permute, hb, hd]
  change Matrix.toEuclideanCLM (𝕜 := Real) (sourceMatrixPermute s (alignedCovariancePseudoInverse hM (sourcePsdClip C)))
      (sourceEuclideanPermute s v) +
    (sourceEuclideanPermute s a -
      Matrix.toEuclideanCLM (𝕜 := Real) (sourceMatrixPermute s (alignedCovariancePseudoInverse hM (sourcePsdClip C)))
        (Matrix.toEuclideanCLM (𝕜 := Real) (sourceMatrixPermute s (alignedCovarianceFactor hM (sourcePsdClip C)))
          (sourceEuclideanPermute s a))) = _
  simp only [source_toEuclideanCLM_permute]
  rfl
end PaperFormalization.Manuscript
