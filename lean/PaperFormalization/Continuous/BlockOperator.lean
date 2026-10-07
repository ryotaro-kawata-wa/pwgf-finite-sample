import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Chebyshev
import PaperFormalization.Continuous.RayleighStability

/-! # Dimension-free bounds for normalized particle block operators

The block operators below are constructed on `PiLp 2`, so the ambient norm
is exactly the particle l2 norm. An all-to-all kernel carries the manuscript's
`1 / N` factor; this cancels the particle-count factor in its unnormalized
bound. The fiber can be any real normed space, with no dimension constant.
-/

open scoped BigOperators NNReal

namespace PaperFormalization.Continuous

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite matrix of continuous linear blocks, acting on the l2 particle space. -/
noncomputable def blockOperator (B : ι → ι → E →L[ℝ] E) :
    (PiLp 2 fun _ : ι => E) →L[ℝ] PiLp 2 fun _ : ι => E := by
  classical
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => E)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => ∑ j, (B i j).comp (PiLp.proj 2 (fun _ : ι => E) j))

/-- The constructed map applies the stated blocks, not an assumed norm bound. -/
theorem blockOperator_apply (B : ι → ι → E →L[ℝ] E)
    (x : PiLp 2 fun _ : ι => E) (i : ι) :
    blockOperator B x i = ∑ j, B i j (x j) := by
  simp [blockOperator]

/-- A diagonal family of continuous linear blocks on the same l2 space. -/
noncomputable def diagonalOperator (D : ι → E →L[ℝ] E) :
    (PiLp 2 fun _ : ι => E) →L[ℝ] PiLp 2 fun _ : ι => E :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => E)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => (D i).comp (PiLp.proj 2 (fun _ : ι => E) i))

omit [Fintype ι] in
theorem diagonalOperator_apply (D : ι → E →L[ℝ] E)
    (x : PiLp 2 fun _ : ι => E) (i : ι) :
    diagonalOperator D x i = D i (x i) := rfl

/-- The normalized all-to-all kernel used by the sampled Hessian. -/
noncomputable def averagedBlockOperator (B : ι → ι → E →L[ℝ] E) :
    (PiLp 2 fun _ : ι => E) →L[ℝ] PiLp 2 fun _ : ι => E :=
  (Fintype.card ι : ℝ)⁻¹ • blockOperator B

/-- Each row of the unnormalized block operator has its direct triangle bound. -/
theorem norm_blockOperator_apply_le (B : ι → ι → E →L[ℝ] E)
    (K : ℝ) (hB : ∀ i j, ‖B i j‖ ≤ K)
    (x : PiLp 2 fun _ : ι => E) (i : ι) :
    ‖blockOperator B x i‖ ≤ K * ∑ j, ‖x j‖ := by
  rw [blockOperator_apply, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  exact Finset.sum_le_sum fun j _ =>
    ((B i j).le_opNorm (x j)).trans (mul_le_mul_of_nonneg_right (hB i j) (norm_nonneg _))

/-- The block-matrix bound, retaining the particle-count factor before normalization. -/
theorem blockOperator_norm_le (B : ι → ι → E →L[ℝ] E)
    (K : ℝ) (hK : 0 ≤ K) (hB : ∀ i j, ‖B i j‖ ≤ K) :
    ‖blockOperator B‖ ≤ (Fintype.card ι : ℝ) * K := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hK)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have hrow : ∀ i, ‖blockOperator B x i‖ ^ 2 ≤ (K * ∑ j, ‖x j‖) ^ 2 := by
    intro i
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      (norm_blockOperator_apply_le B K hB x i)
  have hCS : (∑ j, ‖x j‖) ^ 2 ≤ (Fintype.card ι : ℝ) * ‖x‖ ^ 2 := by
    simpa [PiLp.norm_sq_eq_of_L2] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => ‖x j‖))
  calc
    ‖blockOperator B x‖ ^ 2 = ∑ i, ‖blockOperator B x i‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ _
    _ ≤ ∑ _i : ι, (K * ∑ j, ‖x j‖) ^ 2 := Finset.sum_le_sum fun i _ => hrow i
    _ = (Fintype.card ι : ℝ) * K ^ 2 * (∑ j, ‖x j‖) ^ 2 := by simp; ring
    _ ≤ (Fintype.card ι : ℝ) * K ^ 2 * ((Fintype.card ι : ℝ) * ‖x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hCS (by positivity)
    _ = ((Fintype.card ι : ℝ) * K * ‖x‖) ^ 2 := by ring

/-- A diagonal block family has a bound independent of particle count. -/
theorem diagonalOperator_norm_le (D : ι → E →L[ℝ] E)
    (C : ℝ) (hC : 0 ≤ C) (hD : ∀ i, ‖D i‖ ≤ C) :
    ‖diagonalOperator D‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    ‖diagonalOperator D x‖ ^ 2 = ∑ i, ‖D i (x i)‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]; rfl
    _ ≤ ∑ i, (C * ‖x i‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      exact ((D i).le_opNorm (x i)).trans (mul_le_mul_of_nonneg_right (hD i) (norm_nonneg _))
    _ = (C * ‖x‖) ^ 2 := by rw [mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]; simp [mul_pow]

/-- The manuscript's reciprocal particle count cancels the unnormalized factor. -/
theorem averagedBlockOperator_norm_le [Nonempty ι] (B : ι → ι → E →L[ℝ] E)
    (K : ℝ) (hK : 0 ≤ K) (hB : ∀ i j, ‖B i j‖ ≤ K) :
    ‖averagedBlockOperator B‖ ≤ K := by
  have hN : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [averagedBlockOperator, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  calc
    (Fintype.card ι : ℝ)⁻¹ * ‖blockOperator B‖ ≤
        (Fintype.card ι : ℝ)⁻¹ * ((Fintype.card ι : ℝ) * K) :=
      mul_le_mul_of_nonneg_left (blockOperator_norm_le B K hK hB) (by positivity)
    _ = K := by field_simp

/-- The actual normalized block Hessian: a diagonal part plus the averaged kernel. -/
noncomputable def sampledBlockOperator (D : ι → E →L[ℝ] E)
    (B : ι → ι → E →L[ℝ] E) :
    (PiLp 2 fun _ : ι => E) →L[ℝ] PiLp 2 fun _ : ι => E :=
  diagonalOperator D + averagedBlockOperator B

/-- Dimension-free sampled-Hessian norm estimate from the individual blocks. -/
theorem sampledBlockOperator_norm_le [Nonempty ι] (D : ι → E →L[ℝ] E)
    (B : ι → ι → E →L[ℝ] E) (C K : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hD : ∀ i, ‖D i‖ ≤ C) (hB : ∀ i j, ‖B i j‖ ≤ K) :
    ‖sampledBlockOperator D B‖ ≤ C + K :=
  (norm_add_le _ _).trans (add_le_add
    (diagonalOperator_norm_le D C hC hD) (averagedBlockOperator_norm_le B K hK hB))

/-- The constructed Hessian applies the diagonal and the averaged row kernel. -/
theorem sampledBlockOperator_apply (D : ι → E →L[ℝ] E)
    (B : ι → ι → E →L[ℝ] E) (x : PiLp 2 fun _ : ι => E) (i : ι) :
    sampledBlockOperator D B x i =
      D i (x i) + (Fintype.card ι : ℝ)⁻¹ • ∑ j, B i j (x j) := by
  change diagonalOperator D x i +
    (Fintype.card ι : ℝ)⁻¹ • blockOperator B x i = _
  rw [diagonalOperator_apply, blockOperator_apply]

/-- Differences of two sampled block Hessians are constructed from block differences. -/
theorem sampledBlockOperator_sub (D D' : ι → E →L[ℝ] E)
    (B B' : ι → ι → E →L[ℝ] E) :
    sampledBlockOperator D B - sampledBlockOperator D' B' =
      sampledBlockOperator (fun i => D i - D' i) (fun i j => B i j - B' i j) := by
  ext x i
  change sampledBlockOperator D B x i - sampledBlockOperator D' B' x i = _
  simp only [sampledBlockOperator_apply]
  change D i (x i) + (Fintype.card ι : ℝ)⁻¹ • (∑ j, B i j (x j)) -
      (D' i (x i) + (Fintype.card ι : ℝ)⁻¹ • (∑ j, B' i j (x j))) =
    (D i (x i) - D' i (x i)) +
      (Fintype.card ι : ℝ)⁻¹ • (∑ j, (B i j (x j) - B' i j (x j)))
  rw [Finset.sum_sub_distrib, smul_sub]
  abel

/-- Blockwise difference bounds yield the same dimension-free operator estimate. -/
theorem sampledBlockOperator_sub_norm_le [Nonempty ι] (D D' : ι → E →L[ℝ] E)
    (B B' : ι → ι → E →L[ℝ] E) (C K : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hD : ∀ i, ‖D i - D' i‖ ≤ C) (hB : ∀ i j, ‖B i j - B' i j‖ ≤ K) :
    ‖sampledBlockOperator D B - sampledBlockOperator D' B'‖ ≤ C + K := by
  rw [sampledBlockOperator_sub]
  exact sampledBlockOperator_norm_le _ _ C K hC hK hD hB

/-- Branchwise block Lipschitz bounds give a dimension-free operator-path bound. -/
theorem sampledBlockOperator_lipschitzOn [Nonempty ι]
    (D : ℝ → ι → E →L[ℝ] E) (B : ℝ → ι → ι → E →L[ℝ] E)
    (C K : ℝ≥0) (s : Set ℝ)
    (hD : ∀ i, LipschitzOnWith C (fun t => D t i) s)
    (hB : ∀ i j, LipschitzOnWith K (fun t => B t i j) s) :
    LipschitzOnWith (C + K) (fun t => sampledBlockOperator (D t) (B t)) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht u hu
  rw [dist_eq_norm]
  calc
    ‖sampledBlockOperator (D t) (B t) - sampledBlockOperator (D u) (B u)‖ ≤
        (C : ℝ) * dist t u + (K : ℝ) * dist t u := by
      apply sampledBlockOperator_sub_norm_le _ _ _ _ _ _ (by positivity) (by positivity)
      · intro i
        simpa only [dist_eq_norm] using (hD i).dist_le_mul t ht u hu
      · intro i j
        simpa only [dist_eq_norm] using (hB i j).dist_le_mul t ht u hu
    _ = ((C + K : ℝ≥0) : ℝ) * dist t u := by rw [NNReal.coe_add, add_mul]

section Curvature

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [Nontrivial F] [Nonempty ι]

/-- The literal Rayleigh infimum of the actual block operator has the same bound. -/
theorem abs_sampledBlockOperator_curvature_le (D : ι → F →L[ℝ] F)
    (B : ι → ι → F →L[ℝ] F) (C K : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hD : ∀ i, ‖D i‖ ≤ C) (hB : ∀ i j, ‖B i j‖ ≤ K) :
    |rayleighInf (sampledBlockOperator D B)| ≤ C + K :=
  (abs_rayleighInf_le_opNorm _).trans (sampledBlockOperator_norm_le D B C K hC hK hD hB)

/-- Blockwise perturbations control the sampled curvature without dimension loss. -/
theorem abs_sampledBlockOperator_curvature_sub_le (D D' : ι → F →L[ℝ] F)
    (B B' : ι → ι → F →L[ℝ] F) (C K : ℝ) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hD : ∀ i, ‖D i - D' i‖ ≤ C) (hB : ∀ i j, ‖B i j - B' i j‖ ≤ K) :
    |rayleighInf (sampledBlockOperator D B) - rayleighInf (sampledBlockOperator D' B')| ≤
      C + K :=
  (abs_rayleighInf_sub_le_opNorm _ _).trans
    (sampledBlockOperator_sub_norm_le D D' B B' C K hC hK hD hB)

/-- The same sum of block Lipschitz constants controls sampled curvature. -/
theorem sampledBlockOperator_curvature_lipschitzOn
    (D : ℝ → ι → F →L[ℝ] F) (B : ℝ → ι → ι → F →L[ℝ] F)
    (C K : ℝ≥0) (s : Set ℝ)
    (hD : ∀ i, LipschitzOnWith C (fun t => D t i) s)
    (hB : ∀ i j, LipschitzOnWith K (fun t => B t i j) s) :
    LipschitzOnWith (C + K) (fun t => rayleighInf (sampledBlockOperator (D t) (B t))) s :=
  rayleighInf_lipschitzOn _ _ s (sampledBlockOperator_lipschitzOn D B C K s hD hB)

/-- Closed-branch block regularity supplies curvature absolute continuity. -/
theorem sampledBlockOperator_curvature_ac
    (D : ℝ → ι → F →L[ℝ] F) (B : ℝ → ι → ι → F →L[ℝ] F)
    (C K : ℝ≥0) (a b : ℝ)
    (hD : ∀ i, LipschitzOnWith C (fun t => D t i) (Set.uIcc a b))
    (hB : ∀ i j, LipschitzOnWith K (fun t => B t i j) (Set.uIcc a b)) :
    AbsolutelyContinuousOnInterval (fun t => rayleighInf (sampledBlockOperator (D t) (B t))) a b :=
  (sampledBlockOperator_curvature_lipschitzOn D B C K (Set.uIcc a b) hD hB).absolutelyContinuousOnInterval

end Curvature

end PaperFormalization.Continuous
