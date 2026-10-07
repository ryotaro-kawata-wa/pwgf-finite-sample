import PaperFormalization.Manuscript.CoordinateMoments
import PaperFormalization.Manuscript.MomentResidual
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! # Actual bounded differences of the weighted sample residual

The center is fixed while one sample is replaced. The countable series is
proved convergent from the amplitude sum before subtraction or rearrangement.
This is the deterministic sensitivity input, not McDiarmid's inequality.
-/

open scoped BigOperators NNReal

namespace PaperFormalization.Manuscript

variable {E : Type*} {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, NormedSpace ℝ (H n)] {N : ℕ}

/-- The literal weighted residual of one configuration around fixed centers. -/
noncomputable def weightedSampleResidual (w : ℕ → ℝ≥0) (φ : ∀ n, E → H n)
    (P : ∀ n, H n) (X : Fin N → E) : ℝ :=
  ∑' n, (w n : ℝ) * ‖(N : ℝ)⁻¹ • ∑ i, φ n (X i) - P n‖

/-- The exact reciprocal-N sample mean inherits its coordinate amplitude. -/
theorem norm_bounded_sampleMean_le (hN : 0 < N) (φ : ∀ n, E → H n)
    (A : ℕ → ℝ) (hφ : ∀ n x, ‖φ n x‖ ≤ A n) (X : Fin N → E) (n : ℕ) :
    ‖(N : ℝ)⁻¹ • ∑ i, φ n (X i)‖ ≤ A n := by
  letI : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  simpa only [finiteFeatureMean, Fintype.card_fin] using
    norm_finiteFeatureMean_le (fun i => φ n (X i)) (A n) (fun i => hφ n (X i))

/-- The countable weighted residual converges under the finite amplitude sum. -/
theorem weightedSampleResidual_summable (hN : 0 < N)
    (w : ℕ → ℝ≥0) (φ : ∀ n, E → H n) (P : ∀ n, H n) (A : ℕ → ℝ)
    (hA : Summable (fun n => (w n : ℝ) * A n))
    (hφ : ∀ n x, ‖φ n x‖ ≤ A n) (hP : ∀ n, ‖P n‖ ≤ A n) (X : Fin N → E) :
    Summable (fun n => (w n : ℝ) * ‖(N : ℝ)⁻¹ • ∑ i, φ n (X i) - P n‖) := by
  apply (hA.mul_left 2).of_norm_bounded
  intro n
  rw [Real.norm_of_nonneg (mul_nonneg (w n).coe_nonneg (norm_nonneg _))]
  have hb := (norm_sub_le _ _).trans
    (add_le_add (norm_bounded_sampleMean_le hN φ A hφ X n) (hP n))
  nlinarith [mul_le_mul_of_nonneg_left hb (w n).coe_nonneg]

/-- Its exact uniform envelope is twice the weighted amplitude sum. -/
theorem weightedSampleResidual_le (hN : 0 < N)
    (w : ℕ → ℝ≥0) (φ : ∀ n, E → H n) (P : ∀ n, H n) (A : ℕ → ℝ)
    (hA : Summable (fun n => (w n : ℝ) * A n))
    (hφ : ∀ n x, ‖φ n x‖ ≤ A n) (hP : ∀ n, ‖P n‖ ≤ A n) (X : Fin N → E) :
    weightedSampleResidual w φ P X ≤ 2 * ∑' n, (w n : ℝ) * A n := by
  unfold weightedSampleResidual
  rw [← tsum_mul_left]
  apply (weightedSampleResidual_summable hN w φ P A hA hφ hP X).tsum_le_tsum _ (hA.mul_left 2)
  intro n
  have hb := (norm_sub_le _ _).trans
    (add_le_add (norm_bounded_sampleMean_le hN φ A hφ X n) (hP n))
  nlinarith [mul_le_mul_of_nonneg_left hb (w n).coe_nonneg]

/-- One actual sample replacement changes the countable source statistic by
at most its amplitude envelope divided by N. No law is changed or invoked. -/
theorem weightedSampleResidual_one_sample_change_le (hN : 0 < N)
    (w : ℕ → ℝ≥0) (φ : ∀ n, E → H n) (P : ∀ n, H n) (A : ℕ → ℝ)
    (hA : Summable (fun n => (w n : ℝ) * A n))
    (hφ : ∀ n x, ‖φ n x‖ ≤ A n) (hP : ∀ n, ‖P n‖ ≤ A n)
    (X Y : Fin N → E) (i : Fin N) (hXY : ∀ j, j ≠ i → X j = Y j) :
    |weightedSampleResidual w φ P X - weightedSampleResidual w φ P Y| ≤
      (2 * ∑' n, (w n : ℝ) * A n) / N := by
  have hx := weightedSampleResidual_summable hN w φ P A hA hφ hP X
  have hy := weightedSampleResidual_summable hN w φ P A hA hφ hP Y
  have hn : 0 ≤ (N : ℝ)⁻¹ := by positivity
  unfold weightedSampleResidual
  rw [← hx.tsum_sub hy, ← Real.norm_eq_abs]
  have hs : HasSum (fun n => (2 / N) * ((w n : ℝ) * A n))
      ((2 * ∑' n, (w n : ℝ) * A n) / N) := by
    have hs0 := hA.hasSum.mul_left (2 / (N : ℝ))
    have he : (2 / (N : ℝ)) * (∑' n, (w n : ℝ) * A n) =
        (2 * ∑' n, (w n : ℝ) * A n) / N := by ring
    rw [he] at hs0
    exact hs0
  apply tsum_of_norm_bounded hs
  intro n
  let MX := (N : ℝ)⁻¹ • ∑ j, φ n (X j)
  let MY := (N : ℝ)⁻¹ • ∑ j, φ n (Y j)
  have heq : MX - MY = (N : ℝ)⁻¹ • (φ n (X i) - φ n (Y i)) := by
    dsimp [MX,MY]
    rw [← smul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_eq_single i
    · intro j _ hji
      simp only [hXY j hji, sub_self]
    · simp
  have hm : ‖MX-MY‖ ≤ (N : ℝ)⁻¹ * (2 * A n) := by
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hn]
    apply mul_le_mul_of_nonneg_left _ hn
    have h := (norm_sub_le _ _).trans (add_le_add (hφ n (X i)) (hφ n (Y i)))
    linarith
  change ‖(w n : ℝ) * ‖MX-P n‖ - (w n : ℝ) * ‖MY-P n‖‖ ≤ _
  rw [← mul_sub, norm_mul, Real.norm_of_nonneg (w n).coe_nonneg, Real.norm_eq_abs]
  have hd : |‖MX-P n‖ - ‖MY-P n‖| ≤ ‖MX-MY‖ := by
    simpa only [sub_sub_sub_cancel_right] using abs_norm_sub_norm_le (MX-P n) (MY-P n)
  calc
    _ ≤ (w n : ℝ) * ((N : ℝ)⁻¹ * (2 * A n)) :=
      mul_le_mul_of_nonneg_left (hd.trans hm) (w n).coe_nonneg
    _ = (2 / N) * ((w n : ℝ) * A n) := by ring

end PaperFormalization.Manuscript
