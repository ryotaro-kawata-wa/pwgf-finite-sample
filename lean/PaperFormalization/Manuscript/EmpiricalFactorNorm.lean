import PaperFormalization.Manuscript.FiniteHilbertSchmidt

/-! # Exact normalization and dimension of empirical kernel factors

The actual block matrix carries the source 1/sqrt(N). Its outer normalized
Frobenius norm therefore equals 1/N times the unscaled block norm. The source
sqrt(d)(Lambda+2L) coefficient is derived without an additional factor2 or N.
-/

open scoped BigOperators Matrix.Norms.Frobenius

namespace PaperFormalization.Manuscript

variable {N d : ℕ}

/-- The actual Nd-by-Nd matrix obtained from d-by-d kernel blocks. -/
def particleKernelMatrix (B : Fin N → Fin N → Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin N × Fin d) (Fin N × Fin d) ℝ :=
  fun i j => B i.1 j.1 i.2 j.2

/-- The source empirical Gaussian factor carries exactly 1/sqrt(N). -/
noncomputable def empiricalKernelFactor (B : Fin N → Fin N → Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin N × Fin d) (Fin N × Fin d) ℝ :=
  (Real.sqrt N)⁻¹ • particleKernelMatrix B

/-- The true block Frobenius norm squared is the sum of squared block norms. -/
theorem particleKernelMatrix_norm_sq (B : Fin N → Fin N → Matrix (Fin d) (Fin d) ℝ) :
    ‖particleKernelMatrix B‖ ^ 2 = ∑ i, ∑ j, ‖B i j‖ ^ 2 := by
  simp_rw [frobenius_norm_sq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ a, ∑ j, ∑ b, ‖B i j a b‖ ^ 2) = _
  rw [Finset.sum_comm]

/-- Both 1/sqrt(N) factors combine to exactly 1/N. -/
theorem empiricalKernelFactor_normalized_norm
    (B : Fin N → Fin N → Matrix (Fin d) (Fin d) ℝ) (hN : 0 < N) :
    ‖empiricalKernelFactor B‖ / Real.sqrt N = ‖particleKernelMatrix B‖ / N := by
  rw [empiricalKernelFactor, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hroot : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)).ne'
  have hNr : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  field_simp
  rw [Real.sq_sqrt (Nat.cast_nonneg N)]
  ring

/-- Constant N-by-N matrices have exact Frobenius norm N times the scalar norm. -/
theorem frobenius_norm_const_square (a : ℝ) :
    ‖Matrix.of (fun _ _ : Fin N => a)‖ = (N : ℝ) * |a| := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [frobenius_norm_sq]
  simp only [Matrix.of_apply, Real.norm_eq_abs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Replicating a scalar particle displacement over the other index retains
exactly N times its normalized L2 radius. -/
theorem frobenius_norm_particle_row_le (delta : Fin N → ℝ) (L r : ℝ)
    (hL : 0 ≤ L) (hr : 0 ≤ r) (hdelta : ∑ i, delta i ^ 2 ≤ (N : ℝ) * r ^ 2) :
    ‖Matrix.of (fun i _j : Fin N => L * delta i)‖ ≤ (N : ℝ) * L * r := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [frobenius_norm_sq]
  simp only [Matrix.of_apply, Real.norm_eq_abs, sq_abs, mul_pow, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc
    _ = (N : ℝ) * L ^ 2 * (∑ i, delta i ^ 2) := by rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro i _;ring
    _ ≤ (N : ℝ) * L ^ 2 * ((N : ℝ) * r ^ 2) := mul_le_mul_of_nonneg_left hdelta (by positivity)
    _ = _ := by ring

/-- Minkowski on the actual normalized double sum gives Lambda+2L exactly. -/
theorem frobenius_norm_particle_envelope_le (delta : Fin N → ℝ) (Lambda L r : ℝ)
    (hLambda : 0 ≤ Lambda) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hdelta : ∑ i, delta i ^ 2 ≤ (N : ℝ) * r ^ 2) :
    ‖Matrix.of (fun i j : Fin N => Lambda * r + L * delta i + L * delta j)‖ ≤
      (N : ℝ) * (Lambda + 2 * L) * r := by
  let A : Matrix (Fin N) (Fin N) ℝ := fun _ _ => Lambda * r
  let B : Matrix (Fin N) (Fin N) ℝ := fun i _ => L * delta i
  have hA : ‖A‖ = (N : ℝ) * (Lambda * r) := by
    change ‖Matrix.of (fun _ _ : Fin N => Lambda * r)‖ = _
    rw [frobenius_norm_const_square, abs_of_nonneg (mul_nonneg hLambda hr)]
  have hB : ‖B‖ ≤ (N : ℝ) * L * r := frobenius_norm_particle_row_le delta L r hL hr hdelta
  change ‖A + B + B.transpose‖ ≤ _
  have ht := (norm_add_le (A + B) B.transpose).trans
    (add_le_add_left (norm_add_le A B) ‖B.transpose‖)
  rw [Matrix.frobenius_norm_transpose, hA] at ht
  nlinarith

/-- Operator bounds on actual d-by-d blocks give precisely sqrt(d) times
an N-by-N scalar Frobenius envelope. -/
theorem particleKernelMatrix_norm_le_envelope
    (B : Fin N → Fin N → Matrix (Fin d) (Fin d) ℝ)
    (a : Matrix (Fin N) (Fin N) ℝ)
    (hB : ∀ i j, ‖matrixEuclideanOperator (B i j)‖ ≤ a i j) :
    ‖particleKernelMatrix B‖ ≤ Real.sqrt d * ‖a‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [particleKernelMatrix_norm_sq, mul_pow, frobenius_norm_sq]
  calc
    _ ≤ ∑ i, ∑ j, (Real.sqrt d * a i j) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact (frobenius_le_sqrt_card_mul_matrixEuclideanOperator_norm (B i j)).trans
        (by simpa only [Fintype.card_fin] using
          mul_le_mul_of_nonneg_left (hB i j) (Real.sqrt_nonneg (d : ℝ)))
    _ = _ := by
      simp_rw [mul_pow, Real.norm_eq_abs, sq_abs]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]

/-- The actual source empirical factor satisfies the exact normalized
sqrt(d)(Lambda+2L) bound. N>0 is used only for normalization. -/
theorem empiricalKernelFactor_normalized_bound
    (B : Fin N → Fin N → Matrix (Fin d) (Fin d) ℝ)
    (delta : Fin N → ℝ) (Lambda L r : ℝ) (hN : 0 < N)
    (hLambda : 0 ≤ Lambda) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hdelta : ∑ i, delta i ^ 2 ≤ (N : ℝ) * r ^ 2)
    (hB : ∀ i j, ‖matrixEuclideanOperator (B i j)‖ ≤
      Lambda * r + L * delta i + L * delta j) :
    ‖empiricalKernelFactor B‖ / Real.sqrt N ≤
      Real.sqrt d * (Lambda + 2 * L) * r := by
  let a := Matrix.of (fun i j : Fin N => Lambda * r + L * delta i + L * delta j)
  have h1 := particleKernelMatrix_norm_le_envelope B a hB
  have h2 := frobenius_norm_particle_envelope_le delta Lambda L r hLambda hL hr hdelta
  rw [empiricalKernelFactor_normalized_norm B hN]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
  calc
    _ ≤ Real.sqrt d * ‖a‖ := h1
    _ ≤ Real.sqrt d * ((N : ℝ) * (Lambda + 2 * L) * r) :=
      mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- The empirical factor construction preserves exact kernel differences. -/
theorem empiricalKernelFactor_sub
    (A B : Fin N → Fin N → Matrix (Fin d) (Fin d) ℝ) :
    empiricalKernelFactor A - empiricalKernelFactor B =
      empiricalKernelFactor (fun i j => A i j - B i j) := by
  unfold empiricalKernelFactor
  rw [← smul_sub]
  rfl

end PaperFormalization.Manuscript
