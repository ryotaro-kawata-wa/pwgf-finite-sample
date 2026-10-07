import PaperFormalization.Manuscript.SymmetricNuclearBounds
import PaperFormalization.Manuscript.EmpiricalFactorNorm

/-! # Exact finite covariance mismatch and its particle normalization

The sample-supported term is a genuine reciprocal-count finite Gram average.
The population matrix C is kept as the supplied symmetric covariance; its
residual against the empirical Gram average is retained literally, with no
local support bound applied to it. The only dimension factor is the source d.
-/

open Matrix
open scoped MatrixOrder Matrix.Norms.Frobenius BigOperators

namespace PaperFormalization.Manuscript

variable {N d : ℕ}

/-- The actual Nd-by-d vertical stack of d-by-d kernel blocks. -/
def stackedKernelMatrix (H : Fin N → Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin N × Fin d) (Fin d) ℝ := Matrix.of (fun i j => H i.1 i.2 j)

/-- Stacking retains exactly the sum of block Frobenius squares. -/
theorem stackedKernelMatrix_norm_sq (H : Fin N → Matrix (Fin d) (Fin d) ℝ) :
    ‖stackedKernelMatrix H‖ ^ 2 = ∑ i, ‖H i‖ ^ 2 := by
  simp only [frobenius_norm_sq, Fintype.sum_prod_type, stackedKernelMatrix, Matrix.of_apply]

/-- Local operator magnitudes give sqrt(Nd)L, with all dimensions explicit. -/
theorem stackedKernelMatrix_norm_le (H : Fin N → Matrix (Fin d) (Fin d) ℝ)
    (L : ℝ) (hL : 0 ≤ L) (hH : ∀ i, ‖matrixEuclideanOperator (H i)‖ ≤ L) :
    ‖stackedKernelMatrix H‖ ≤ Real.sqrt ((N : ℝ) * d) * L := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [stackedKernelMatrix_norm_sq, mul_pow, Real.sq_sqrt (by positivity)]
  calc
    _ ≤ ∑ _i : Fin N, (Real.sqrt d * L) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      exact (frobenius_le_sqrt_card_mul_matrixEuclideanOperator_norm (H i)).trans
        (by simpa only [Fintype.card_fin] using
          mul_le_mul_of_nonneg_left (hH i) (Real.sqrt_nonneg (d : ℝ)))
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)];ring

/-- Local block differences give sqrt(Nd)Gamma without another dimension loss. -/
theorem stackedKernelMatrix_sub_norm_le
    (H G : Fin N → Matrix (Fin d) (Fin d) ℝ) (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (hHG : ∀ i, ‖matrixEuclideanOperator (H i - G i)‖ ≤ gamma) :
    ‖stackedKernelMatrix H - stackedKernelMatrix G‖ ≤ Real.sqrt ((N : ℝ) * d) * gamma := by
  exact stackedKernelMatrix_norm_le (fun i => H i - G i) gamma hgamma hHG

/-- The source pointwise sample-supported Gram difference has coefficient
exactly 2Nd L Gamma, derived from the actual local block operator bounds. -/
theorem stackedKernelMatrix_gram_difference_le
    (H G : Fin N → Matrix (Fin d) (Fin d) ℝ) (L gamma : ℝ)
    (hL : 0 ≤ L) (hgamma : 0 ≤ gamma)
    (hH : ∀ i, ‖matrixEuclideanOperator (H i)‖ ≤ L)
    (hG : ∀ i, ‖matrixEuclideanOperator (G i)‖ ≤ L)
    (hHG : ∀ i, ‖matrixEuclideanOperator (H i - G i)‖ ≤ gamma) :
    matrixNuclearValue (stackedKernelMatrix H * (stackedKernelMatrix H)ᵀ -
      stackedKernelMatrix G * (stackedKernelMatrix G)ᵀ) ≤ 2 * N * d * L * gamma := by
  calc
    _ ≤ ‖stackedKernelMatrix H - stackedKernelMatrix G‖ *
        (‖stackedKernelMatrix H‖ + ‖stackedKernelMatrix G‖) :=
      matrixNuclearValue_gram_sub_gram_le _ _
    _ ≤ (Real.sqrt ((N : ℝ) * d) * gamma) *
        (Real.sqrt ((N : ℝ) * d) * L + Real.sqrt ((N : ℝ) * d) * L) :=
      mul_le_mul (stackedKernelMatrix_sub_norm_le H G gamma hgamma hHG)
        (add_le_add (stackedKernelMatrix_norm_le H L hL hH)
          (stackedKernelMatrix_norm_le G L hL hG)) (by positivity) (by positivity)
    _ = 2 * N * d * L * gamma := by
      calc
        _ = 2 * (Real.sqrt ((N : ℝ) * d)) ^ 2 * L * gamma := by ring
        _ = _ := by rw [Real.sq_sqrt (by positivity)];ring

section Empirical

variable {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k]

/-- Actual reciprocal-count Gram average; no probability or nuclear bound is
encoded in this definition. -/
noncomputable def empiricalGramMatrix (U : Fin N → Matrix n k ℝ) : Matrix n n ℝ :=
  (N : ℝ)⁻¹ • ∑ j, U j * (U j)ᵀ

omit [Fintype n] [DecidableEq n] in
/-- A finite empirical Gram average is genuinely symmetric. -/
theorem empiricalGramMatrix_isHermitian (U : Fin N → Matrix n k ℝ) :
    (empiricalGramMatrix U).IsHermitian := by
  have hgram (j : Fin N) : (U j * (U j)ᵀ).IsHermitian := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using isHermitian_mul_conjTranspose_self (U j)
  have hs : (∑ j, U j * (U j)ᵀ).IsHermitian :=
    isSelfAdjoint_sum (R := Matrix n n ℝ) Finset.univ (fun j _ => hgram j)
  exact hs.smul (by simp [isSelfAdjoint_iff])

omit [Fintype n] [DecidableEq n] in
/-- The empirical difference is exactly the average of pointwise differences. -/
theorem empiricalGramMatrix_sub (U V : Fin N → Matrix n k ℝ) :
    empiricalGramMatrix U - empiricalGramMatrix V =
      ∑ j, (N : ℝ)⁻¹ • (U j * (U j)ᵀ - V j * (V j)ᵀ) := by
  rw [empiricalGramMatrix, empiricalGramMatrix, ← smul_sub, ← Finset.sum_sub_distrib,
    Finset.smul_sum]

/-- Averaging the derived pointwise nuclear bounds has no extra N factor. -/
theorem empiricalGramMatrix_difference_le (U V : Fin N → Matrix n k ℝ)
    (b : ℝ) (hN : 0 < N)
    (hUV : ∀ j, matrixNuclearValue (U j * (U j)ᵀ - V j * (V j)ᵀ) ≤ b) :
    matrixNuclearValue (empiricalGramMatrix U - empiricalGramMatrix V) ≤ b := by
  rw [empiricalGramMatrix_sub]
  have hNr : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  calc
    _ ≤ ∑ j, (N : ℝ)⁻¹ * matrixNuclearValue (U j * (U j)ᵀ - V j * (V j)ᵀ) :=
      matrixNuclearValue_weighted_sum_le Finset.univ _ _
        (fun _ _ => by positivity) (fun j _ => gram_sub_gram_isHermitian (U j) (V j))
    _ ≤ ∑ _j : Fin N, (N : ℝ)⁻¹ * b :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hUV j) (by positivity))
    _ = b := by simp [hNr]

/-- The source decomposition keeps the actual population residual unchanged;
only the finite sample-supported difference receives a local upper bound. -/
theorem covariance_mismatch_le_residual_add (C : Matrix n n ℝ) (hC : C.IsHermitian)
    (U V : Fin N → Matrix n k ℝ) (b : ℝ) (hN : 0 < N)
    (hUV : ∀ j, matrixNuclearValue (U j * (U j)ᵀ - V j * (V j)ᵀ) ≤ b) :
    matrixNuclearValue (C - empiricalGramMatrix V) ≤
      matrixNuclearValue (C - empiricalGramMatrix U) + b := by
  have he : C - empiricalGramMatrix V =
      (C - empiricalGramMatrix U) + (empiricalGramMatrix U - empiricalGramMatrix V) := by abel
  rw [he]
  exact (matrixNuclearValue_add_le (hC.sub (empiricalGramMatrix_isHermitian U))
    ((empiricalGramMatrix_isHermitian U).sub (empiricalGramMatrix_isHermitian V))).trans
    (add_le_add_right (empiricalGramMatrix_difference_le U V b hN hUV) _)

end Empirical

/-- The exact source N^-1 covariance mismatch coefficient. H and G supply the
population and empirical kernel evaluations at the same sample points. No
bound on the population covariance integral itself is used. -/
theorem source_covariance_mismatch_normalized_le
    (C : Matrix (Fin N × Fin d) (Fin N × Fin d) ℝ) (hC : C.IsHermitian)
    (H G : Fin N → Fin N → Matrix (Fin d) (Fin d) ℝ) (L gamma : ℝ)
    (hN : 0 < N) (hL : 0 ≤ L) (hgamma : 0 ≤ gamma)
    (hH : ∀ i j, ‖matrixEuclideanOperator (H i j)‖ ≤ L)
    (hG : ∀ i j, ‖matrixEuclideanOperator (G i j)‖ ≤ L)
    (hHG : ∀ i j, ‖matrixEuclideanOperator (H i j - G i j)‖ ≤ gamma) :
    matrixNuclearValue (C - empiricalGramMatrix (fun j => stackedKernelMatrix (fun i => G i j))) / N ≤
      2 * d * L * gamma +
        matrixNuclearValue (C - empiricalGramMatrix (fun j => stackedKernelMatrix (fun i => H i j))) / N := by
  have hb := covariance_mismatch_le_residual_add C hC
    (fun j => stackedKernelMatrix (fun i => H i j))
    (fun j => stackedKernelMatrix (fun i => G i j))
    (2 * N * d * L * gamma) hN (fun j =>
      stackedKernelMatrix_gram_difference_le _ _ L gamma hL hgamma
        (fun i => hH i j) (fun i => hG i j) (fun i => hHG i j))
  apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
  have hNr : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  calc
    _ ≤ matrixNuclearValue (C - empiricalGramMatrix (fun j => stackedKernelMatrix (fun i => H i j))) +
        2 * N * d * L * gamma := hb
    _ = _ := by field_simp;ring

/-- The block matrix product is exactly the sum of the stacked column Gram
matrices. This is an entrywise identity over all particle/coordinate indices. -/
theorem particleKernelMatrix_mul_transpose_eq_sum
    (G : Fin N → Fin N → Matrix (Fin d) (Fin d) ℝ) :
    particleKernelMatrix G * (particleKernelMatrix G)ᵀ =
      ∑ j, stackedKernelMatrix (fun i => G i j) * (stackedKernelMatrix (fun i => G i j))ᵀ := by
  ext i k
  simp [Matrix.mul_apply, particleKernelMatrix, stackedKernelMatrix, Fintype.sum_prod_type,
    Matrix.sum_apply]

/-- Both reciprocal square roots in the actual empirical factor give the
same reciprocal-count Gram average, including N=0 algebraically. -/
theorem empiricalGramMatrix_stack_eq_factor_mul_transpose
    (G : Fin N → Fin N → Matrix (Fin d) (Fin d) ℝ) :
    empiricalGramMatrix (fun j => stackedKernelMatrix (fun i => G i j)) =
      empiricalKernelFactor G * (empiricalKernelFactor G)ᵀ := by
  calc
    _ = (N : ℝ)⁻¹ • (particleKernelMatrix G * (particleKernelMatrix G)ᵀ) := by
      rw [particleKernelMatrix_mul_transpose_eq_sum]
      rfl
    _ = _ := by
      unfold empiricalKernelFactor
      rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      congr 1
      rw [← _root_.mul_inv_rev, ← sq, Real.sq_sqrt (Nat.cast_nonneg N)]

/-- The source block adjoint symmetry gives actual finite-factor symmetry. -/
theorem empiricalKernelFactor_isHermitian
    (G : Fin N → Fin N → Matrix (Fin d) (Fin d) ℝ)
    (hG : ∀ i j, (G i j)ᵀ = G j i) : (empiricalKernelFactor G).IsHermitian := by
  have hp : (particleKernelMatrix G).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simpa only [particleKernelMatrix, star_trivial, transpose_apply] using
      (congrArg (fun A : Matrix (Fin d) (Fin d) ℝ => A j.2 i.2) (hG i.1 j.1)).symm
  exact hp.smul (by simp [isSelfAdjoint_iff])

/-- The mismatch bound now uses M² for the actual 1/sqrt(N) empirical
kernel factor, with the unchanged empirical covariance residual. -/
theorem source_covariance_mismatch_factor_square_le
    (C : Matrix (Fin N × Fin d) (Fin N × Fin d) ℝ) (hC : C.IsHermitian)
    (H G : Fin N → Fin N → Matrix (Fin d) (Fin d) ℝ) (L gamma : ℝ)
    (hN : 0 < N) (hL : 0 ≤ L) (hgamma : 0 ≤ gamma)
    (hH : ∀ i j, ‖matrixEuclideanOperator (H i j)‖ ≤ L)
    (hG : ∀ i j, ‖matrixEuclideanOperator (G i j)‖ ≤ L)
    (hHG : ∀ i j, ‖matrixEuclideanOperator (H i j - G i j)‖ ≤ gamma)
    (hGsym : ∀ i j, (G i j)ᵀ = G j i) :
    matrixNuclearValue (C - empiricalKernelFactor G * empiricalKernelFactor G) / N ≤
      2 * d * L * gamma +
        matrixNuclearValue (C - empiricalGramMatrix (fun j => stackedKernelMatrix (fun i => H i j))) / N := by
  have ht : (empiricalKernelFactor G)ᵀ = empiricalKernelFactor G := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact empiricalKernelFactor_isHermitian G hGsym
  have hb := source_covariance_mismatch_normalized_le C hC H G L gamma hN hL hgamma hH hG hHG
  rwa [empiricalGramMatrix_stack_eq_factor_mul_transpose, ht] at hb

end PaperFormalization.Manuscript
