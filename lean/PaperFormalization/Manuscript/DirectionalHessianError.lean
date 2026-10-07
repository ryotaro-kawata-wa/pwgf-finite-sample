import PaperFormalization.Manuscript.ParticleDiscrepancy
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Directional Hessian error with the manuscript's particle normalization

The integral-Hessian sum contains every ordered pair, including i=j, with
factor N^(-2). The spatial-Jacobian sum has factor N^(-1). Operator-block
estimates and the normalized cubic anti-spikiness condition are explicit.
-/

open Set
open scoped BigOperators InnerProductSpace

namespace PaperFormalization.Manuscript

variable {E : Type*} [NormedAddCommGroup E] {N : ℕ}

/-- The exact normalized Euclidean product norm of one displacement configuration. -/
noncomputable def particleRMS (delta : Fin N → E) : ℝ :=
  ‖(WithLp.toLp 2 delta : PiLp 2 (fun _ : Fin N => E))‖ / Real.sqrt N

/-- The normalized particle norm is nonnegative. -/
theorem particleRMS_nonneg (delta : Fin N → E) : 0 ≤ particleRMS delta :=
  div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

/-- The pointwise normalized norm is exactly the manuscript discrepancy. -/
theorem particleRMS_eq_normalizedDiscrepancy (X Y : ℝ → Fin N → E) (t : ℝ) :
    particleRMS (X t - Y t) = normalizedDiscrepancy X Y t := rfl

/-- Squared coordinate norms sum to N times the squared normalized discrepancy. -/
theorem sum_norm_sq_eq_card_mul_particleRMS_sq (delta : Fin N → E) (hN : 0 < N) :
    (∑ i : Fin N, ‖delta i‖ ^ 2) = (N : ℝ) * particleRMS delta ^ 2 := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold particleRMS
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg N), PiLp.norm_sq_eq_of_L2]
  field_simp

/-- Cauchy--Schwarz with the actual RMS normalization gives sum_i ||delta_i|| <= N*r. -/
theorem sum_norm_le_card_mul_particleRMS (delta : Fin N → E) (hN : 0 < N) :
    (∑ i : Fin N, ‖delta i‖) ≤ (N : ℝ) * particleRMS delta := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N))
    (fun i => ‖delta i‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hcs
  rw [sum_norm_sq_eq_card_mul_particleRMS_sq delta hN] at hcs
  have hr := particleRMS_nonneg delta
  apply (sq_le_sq₀
    (Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => norm_nonneg (delta i)))
    (mul_nonneg (Nat.cast_nonneg N) hr)).mp
  nlinarith only [hcs]

variable [InnerProductSpace ℝ E]

/-- Normalized integral-Hessian quadratic form; the double sum includes its diagonal. -/
noncomputable def offDiagonalForm (delta : Fin N → E) (K : Fin N → Fin N → E →L[ℝ] E) : ℝ :=
  (N : ℝ)⁻¹ ^ 2 * ∑ i : Fin N, ∑ j : Fin N, ⟪delta i, K i j (delta j)⟫_ℝ

/-- Normalized spatial-Jacobian quadratic form. -/
noncomputable def diagonalForm (delta : Fin N → E) (D : Fin N → E →L[ℝ] E) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i : Fin N, ⟪delta i, D i (delta i)⟫_ℝ

/-- A block's operator norm bounds its actual bilinear pairing. -/
theorem abs_inner_block_le (x y : E) (K : E →L[ℝ] E) (C : ℝ) (hK : ‖K‖ ≤ C) :
    |⟪x, K y⟫_ℝ| ≤ ‖x‖ * ‖y‖ * C := by
  calc
    |⟪x, K y⟫_ℝ| ≤ ‖x‖ * ‖K y‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖K‖ * ‖y‖) := mul_le_mul_of_nonneg_left (K.le_opNorm y) (norm_nonneg x)
    _ ≤ ‖x‖ * (C * ‖y‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hK (norm_nonneg y)) (norm_nonneg x)
    _ = _ := by ring

/-- Finite-sum domination of the actual off-diagonal form by coordinate block bounds. -/
theorem abs_offDiagonalForm_le_sum (delta : Fin N → E)
    (K : Fin N → Fin N → E →L[ℝ] E) (C : Fin N → Fin N → ℝ)
    (hK : ∀ i j, ‖K i j‖ ≤ C i j) :
    |offDiagonalForm delta K| ≤
      (N : ℝ)⁻¹ ^ 2 * ∑ i : Fin N, ∑ j : Fin N, ‖delta i‖ * ‖delta j‖ * C i j := by
  unfold offDiagonalForm
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  calc
    |∑ i : Fin N, ∑ j : Fin N, ⟪delta i, K i j (delta j)⟫_ℝ| ≤
        ∑ i : Fin N, |∑ j : Fin N, ⟪delta i, K i j (delta j)⟫_ℝ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin N, ∑ j : Fin N, |⟪delta i, K i j (delta j)⟫_ℝ| :=
      Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      abs_inner_block_le (delta i) (delta j) (K i j) (C i j) (hK i j)

/-- Finite-sum domination of the actual diagonal form by coordinate block bounds. -/
theorem abs_diagonalForm_le_sum (delta : Fin N → E)
    (D : Fin N → E →L[ℝ] E) (C : Fin N → ℝ) (hD : ∀ i, ‖D i‖ ≤ C i) :
    |diagonalForm delta D| ≤ (N : ℝ)⁻¹ * ∑ i : Fin N, ‖delta i‖ ^ 2 * C i := by
  unfold diagonalForm
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
  calc
    |∑ i : Fin N, ⟪delta i, D i (delta i)⟫_ℝ| ≤
        ∑ i : Fin N, |⟪delta i, D i (delta i)⟫_ℝ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum fun i _ => by
      simpa only [pow_two] using abs_inner_block_le (delta i) (delta i) (D i) (C i) (hD i)

/-- Algebraic factorization of the complete two-slot spatial error sum. -/
theorem double_sum_spatial_factorization (u : Fin N → ℝ) (L : ℝ) :
    (∑ i : Fin N, ∑ j : Fin N, u i * u j * (L * u i + L * u j)) =
      2 * L * (∑ i : Fin N, u i ^ 2) * (∑ i : Fin N, u i) := by
  have hterm : ∀ i j, u i * u j * (L * u i + L * u j) =
      L * u i ^ 2 * u j + L * u i * u j ^ 2 := by intros; ring
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- Both spatial kernel slots together contribute exactly 2*L*r^3. -/
theorem abs_offDiagonalForm_le_spatial (delta : Fin N → E)
    (K : Fin N → Fin N → E →L[ℝ] E) (L : ℝ) (hN : 0 < N) (hL : 0 ≤ L)
    (hK : ∀ i j, ‖K i j‖ ≤ L * ‖delta i‖ + L * ‖delta j‖) :
    |offDiagonalForm delta K| ≤ 2 * L * particleRMS delta ^ 3 := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hr := particleRMS_nonneg delta
  have hsum := sum_norm_le_card_mul_particleRMS delta hN
  calc
    |offDiagonalForm delta K| ≤ (N : ℝ)⁻¹ ^ 2 *
        ∑ i : Fin N, ∑ j : Fin N, ‖delta i‖ * ‖delta j‖ * (L * ‖delta i‖ + L * ‖delta j‖) :=
      abs_offDiagonalForm_le_sum delta K _ hK
    _ = (N : ℝ)⁻¹ ^ 2 * (2 * L * ((N : ℝ) * particleRMS delta ^ 2) *
        (∑ i : Fin N, ‖delta i‖)) := by
      rw [double_sum_spatial_factorization, sum_norm_sq_eq_card_mul_particleRMS_sq delta hN]
    _ ≤ (N : ℝ)⁻¹ ^ 2 * (2 * L * ((N : ℝ) * particleRMS delta ^ 2) *
        ((N : ℝ) * particleRMS delta)) := by gcongr
    _ = _ := by field_simp

/-- The diagonal point-slot contribution uses precisely the normalized cubic anti-spike input. -/
theorem abs_diagonalForm_le_spatial (delta : Fin N → E)
    (D : Fin N → E →L[ℝ] E) (L A : ℝ) (hL : 0 ≤ L)
    (hD : ∀ i, ‖D i‖ ≤ L * ‖delta i‖)
    (hanti : (N : ℝ)⁻¹ * ∑ i : Fin N, ‖delta i‖ ^ 3 ≤ A * particleRMS delta ^ 3) :
    |diagonalForm delta D| ≤ L * A * particleRMS delta ^ 3 := by
  calc
    |diagonalForm delta D| ≤ (N : ℝ)⁻¹ * ∑ i : Fin N, ‖delta i‖ ^ 2 * (L * ‖delta i‖) :=
      abs_diagonalForm_le_sum delta D _ hD
    _ = L * ((N : ℝ)⁻¹ * ∑ i : Fin N, ‖delta i‖ ^ 3) := by
      have heq : ∀ i : Fin N, ‖delta i‖ ^ 2 * (L * ‖delta i‖) = L * ‖delta i‖ ^ 3 := by
        intro i
        ring
      simp_rw [heq, ← Finset.mul_sum]
      ring
    _ ≤ L * (A * particleRMS delta ^ 3) := mul_le_mul_of_nonneg_left hanti hL
    _ = _ := by ring

/-- The two actual point-slot quadratic forms give the source coefficient (2+A)*L. -/
theorem abs_spatial_forms_le (delta : Fin N → E)
    (K : Fin N → Fin N → E →L[ℝ] E) (D : Fin N → E →L[ℝ] E)
    (L A : ℝ) (hN : 0 < N) (hL : 0 ≤ L)
    (hK : ∀ i j, ‖K i j‖ ≤ L * ‖delta i‖ + L * ‖delta j‖)
    (hD : ∀ i, ‖D i‖ ≤ L * ‖delta i‖)
    (hanti : (N : ℝ)⁻¹ * ∑ i : Fin N, ‖delta i‖ ^ 3 ≤ A * particleRMS delta ^ 3) :
    |offDiagonalForm delta K + diagonalForm delta D| ≤
      (2 + A) * L * particleRMS delta ^ 3 := by
  exact (abs_add_le _ _).trans ((add_le_add
    (abs_offDiagonalForm_le_spatial delta K L hN hL hK)
    (abs_diagonalForm_le_spatial delta D L A hL hD hanti)).trans_eq (by ring))

/-- Uniform integral-Hessian block errors cost C*r^2 after both N normalizations. -/
theorem abs_offDiagonalForm_le_uniform (delta : Fin N → E)
    (K : Fin N → Fin N → E →L[ℝ] E) (C : ℝ) (hN : 0 < N) (hC : 0 ≤ C)
    (hK : ∀ i j, ‖K i j‖ ≤ C) :
    |offDiagonalForm delta K| ≤ C * particleRMS delta ^ 2 := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hsum := sum_norm_le_card_mul_particleRMS delta hN
  have hsum0 : 0 ≤ ∑ i : Fin N, ‖delta i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hr := particleRMS_nonneg delta
  calc
    |offDiagonalForm delta K| ≤ (N : ℝ)⁻¹ ^ 2 *
        ∑ i : Fin N, ∑ j : Fin N, ‖delta i‖ * ‖delta j‖ * C :=
      abs_offDiagonalForm_le_sum delta K (fun _ _ => C) hK
    _ = (N : ℝ)⁻¹ ^ 2 * (C * (∑ i : Fin N, ‖delta i‖) ^ 2) := by
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul]
      ring
    _ ≤ (N : ℝ)⁻¹ ^ 2 * (C * ((N : ℝ) * particleRMS delta) ^ 2) := by gcongr
    _ = _ := by field_simp

/-- Uniform spatial-Jacobian block errors cost C*r^2 under the exact N normalization. -/
theorem abs_diagonalForm_le_uniform (delta : Fin N → E)
    (D : Fin N → E →L[ℝ] E) (C : ℝ) (hN : 0 < N)
    (hD : ∀ i, ‖D i‖ ≤ C) :
    |diagonalForm delta D| ≤ C * particleRMS delta ^ 2 := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  calc
    |diagonalForm delta D| ≤ (N : ℝ)⁻¹ * ∑ i : Fin N, ‖delta i‖ ^ 2 * C :=
      abs_diagonalForm_le_sum delta D (fun _ => C) hD
    _ = (N : ℝ)⁻¹ * (((N : ℝ) * particleRMS delta ^ 2) * C) := by
      rw [← Finset.sum_mul, sum_norm_sq_eq_card_mul_particleRMS_sq delta hN]
    _ = _ := by field_simp

/-- Half-size measure errors in each of the two Hessians sum to b*r^2, not 2*b*r^2. -/
theorem abs_measure_forms_le (delta : Fin N → E)
    (K : Fin N → Fin N → E →L[ℝ] E) (D : Fin N → E →L[ℝ] E)
    (b : ℝ) (hN : 0 < N) (hb : 0 ≤ b)
    (hK : ∀ i j, ‖K i j‖ ≤ b / 2) (hD : ∀ i, ‖D i‖ ≤ b / 2) :
    |offDiagonalForm delta K + diagonalForm delta D| ≤ b * particleRMS delta ^ 2 := by
  exact (abs_add_le _ _).trans ((add_le_add
    (abs_offDiagonalForm_le_uniform delta K (b / 2) hN (by positivity) hK)
    (abs_diagonalForm_le_uniform delta D (b / 2) hN hD)).trans_eq (by ring))

/-- The complete integral-Hessian quadratic form is additive in its actual blocks. -/
theorem offDiagonalForm_add (delta : Fin N → E)
    (K K' : Fin N → Fin N → E →L[ℝ] E) :
    offDiagonalForm delta (fun i j => K i j + K' i j) =
      offDiagonalForm delta K + offDiagonalForm delta K' := by
  simp [offDiagonalForm, inner_add_right,
    Finset.sum_add_distrib, mul_add]

/-- The spatial-Jacobian quadratic form is additive in its actual blocks. -/
theorem diagonalForm_add (delta : Fin N → E) (D D' : Fin N → E →L[ℝ] E) :
    diagonalForm delta (fun i => D i + D' i) = diagonalForm delta D + diagonalForm delta D' := by
  simp [diagonalForm, inner_add_right,
    Finset.sum_add_distrib, mul_add]

/-- Combining the measure and point slots gives the exact source cubic-plus-quadratic bound. -/
theorem abs_combined_directional_forms_le (delta : Fin N → E)
    (Km Kp : Fin N → Fin N → E →L[ℝ] E) (Dm Dp : Fin N → E →L[ℝ] E)
    (L A Lambda Gamma b : ℝ) (hN : 0 < N) (hL : 0 ≤ L) (hb : 0 ≤ b)
    (hbupper : b ≤ Lambda * particleRMS delta + Gamma)
    (hKm : ∀ i j, ‖Km i j‖ ≤ b / 2) (hDm : ∀ i, ‖Dm i‖ ≤ b / 2)
    (hKp : ∀ i j, ‖Kp i j‖ ≤ L * ‖delta i‖ + L * ‖delta j‖)
    (hDp : ∀ i, ‖Dp i‖ ≤ L * ‖delta i‖)
    (hanti : (N : ℝ)⁻¹ * ∑ i : Fin N, ‖delta i‖ ^ 3 ≤ A * particleRMS delta ^ 3) :
    |offDiagonalForm delta (fun i j => Km i j + Kp i j) +
      diagonalForm delta (fun i => Dm i + Dp i)| ≤
        (Lambda + (2 + A) * L) * particleRMS delta ^ 3 + Gamma * particleRMS delta ^ 2 := by
  rw [offDiagonalForm_add, diagonalForm_add]
  rw [show offDiagonalForm delta Km + offDiagonalForm delta Kp +
      (diagonalForm delta Dm + diagonalForm delta Dp) =
      (offDiagonalForm delta Km + diagonalForm delta Dm) +
      (offDiagonalForm delta Kp + diagonalForm delta Dp) by ring]
  calc
    _ ≤ |offDiagonalForm delta Km + diagonalForm delta Dm| +
        |offDiagonalForm delta Kp + diagonalForm delta Dp| := abs_add_le _ _
    _ ≤ b * particleRMS delta ^ 2 + (2 + A) * L * particleRMS delta ^ 3 :=
      add_le_add (abs_measure_forms_le delta Km Dm b hN hb hKm hDm)
        (abs_spatial_forms_le delta Kp Dp L A hN hL hKp hDp hanti)
    _ ≤ (Lambda * particleRMS delta + Gamma) * particleRMS delta ^ 2 +
        (2 + A) * L * particleRMS delta ^ 3 :=
      add_le_add (mul_le_mul_of_nonneg_right hbupper (sq_nonneg _)) le_rfl
    _ = _ := by ring

/-- The actual supremum of normalized directional block-Hessian errors over s in [0,1]. -/
noncomputable def directionalHessianError (delta : Fin N → E)
    (K : ℝ → Fin N → Fin N → E →L[ℝ] E) (D : ℝ → Fin N → E →L[ℝ] E) : ℝ :=
  sSup ((fun s : ℝ => |offDiagonalForm delta (K s) + diagonalForm delta (D s)|) '' Icc 0 1)

/-- The manuscript's combined iota bound, derived from the actual quadratic
forms and the actual supremum, with the N^-2 and N^-1 factors intact. -/
theorem directionalHessianError_le (delta : Fin N → E)
    (Km Kp : ℝ → Fin N → Fin N → E →L[ℝ] E)
    (Dm Dp : ℝ → Fin N → E →L[ℝ] E) (b : ℝ → ℝ)
    (L A Lambda Gamma : ℝ) (hN : 0 < N) (hL : 0 ≤ L)
    (hb : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ b s)
    (hbupper : ∀ s ∈ Icc (0 : ℝ) 1, b s ≤ Lambda * particleRMS delta + Gamma)
    (hKm : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i j, ‖Km s i j‖ ≤ b s / 2)
    (hDm : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i, ‖Dm s i‖ ≤ b s / 2)
    (hKp : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i j, ‖Kp s i j‖ ≤ L * ‖delta i‖ + L * ‖delta j‖)
    (hDp : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i, ‖Dp s i‖ ≤ L * ‖delta i‖)
    (hanti : (N : ℝ)⁻¹ * ∑ i : Fin N, ‖delta i‖ ^ 3 ≤ A * particleRMS delta ^ 3) :
    directionalHessianError delta (fun s i j => Km s i j + Kp s i j)
      (fun s i => Dm s i + Dp s i) ≤
        (Lambda + (2 + A) * L) * particleRMS delta ^ 3 + Gamma * particleRMS delta ^ 2 := by
  apply csSup_le
  · exact ⟨_, 0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact abs_combined_directional_forms_le delta (Km s) (Kp s) (Dm s) (Dp s)
      L A Lambda Gamma (b s) hN hL (hb s hs) (hbupper s hs)
      (hKm s hs) (hDm s hs) (hKp s hs) (hDp s hs) hanti

end PaperFormalization.Manuscript
