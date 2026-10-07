import PaperFormalization.Manuscript.SourceHilbertSchmidtFourthMoment
import PaperFormalization.Manuscript.UniformSourceCoefficients

/-! # Uniform growth of the exact source fourth-moment coefficient

The coefficient itself retains the original population scale K. Fixed scale
inflation is used only in the upper bound. The strongest statement keeps d²
explicit and chooses its constant before both d and K; the source-style
fixed-d corollary then absorbs d² into a constant still chosen before K.
-/

open scoped BigOperators

namespace PaperFormalization.Manuscript

/-- The sum of squared nonnegative summable terms is bounded by the square
of their actual sum; convergence of the squared series is proved internally. -/
theorem tsum_sq_le_sq_tsum_nonneg (b : ℕ → ℝ) (hb : Summable b)
    (hb0 : ∀ n, 0 ≤ b n) : (∑' n, b n ^ 2) ≤ (∑' n, b n) ^ 2 := by
  have hpoint (n : ℕ) : b n ^ 2 ≤ (∑' i, b i) * b n := by
    have hle := hb.le_tsum n (fun i _ => hb0 i)
    nlinarith [mul_le_mul_of_nonneg_right hle (hb0 n)]
  have hs := hb.mul_left (∑' n, b n)
  have hsq : Summable (fun n => b n ^ 2) :=
    hs.of_nonneg_of_le (fun n => sq_nonneg _) hpoint
  have h := hsq.tsum_le_tsum hpoint hs
  simpa only [tsum_mul_left, pow_two] using h

/-- A fixed enlargement of K controls every derivative-coordinate factor.
The coefficient on the left is exactly the original source factor. -/
theorem sourceDerivativeL4Factor_le_amplitude (alpha K : ℝ)
    (halpha : 0 < alpha) (hK : 0 < K) (n : ℕ) :
    sourceDerivativeL4Factor alpha K n ≤
      2 + (1 : ℝ) ^ (n + 1) +
        ((1 + (4 : ℝ) ^ (1 / alpha)) * (1 + K)) ^ (n + 1) *
          ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha) := by
  let K4 := (4 : ℝ) ^ (1 / alpha) * K
  let Kstar := (1 + (4 : ℝ) ^ (1 / alpha)) * (1 + K)
  have hK4 : 0 ≤ K4 := by dsimp [K4]; positivity
  have hscale : 1 + K4 ≤ Kstar := by
    dsimp [K4, Kstar]
    nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) (1 / alpha)]
  have hpow : (K * (4 * (n : ℝ)) ^ (1 / alpha)) ^ n ≤
      (K4 * ((n + 1 : ℕ) : ℝ) ^ (1 / alpha)) ^ n := by
    apply pow_le_pow_left₀ (by positivity)
    calc
      _ ≤ K * (4 * ((n + 1 : ℕ) : ℝ)) ^ (1 / alpha) := by
        gcongr
        omega
      _ = _ := by
        rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4) (by positivity)]
        dsimp [K4]
        ring
  have hprev := previous_moment_le_full K4 alpha hK4 halpha n
  have hfull : (1 + K4) ^ (n + 1) *
      ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha) ≤
      Kstar ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha) := by
    gcongr
  rw [sourceDerivativeL4Factor_eq]
  have h := hpow.trans (hprev.trans hfull)
  change 1 + _ ≤ 2 + 1 ^ (n + 1) + Kstar ^ (n + 1) * _
  simpa only [one_pow] using (by linarith : 1 + (K * (4 * (n : ℝ)) ^ (1 / alpha)) ^ n ≤
    2 + 1 + Kstar ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha))

/-- The derivative L4 coordinate series has one uniform chi(K) envelope,
with its constant fixed before the original population scale K. -/
theorem exists_uniform_sourceDerivativeL4_series_bound (c C g p q alpha : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (halpha : 0 < alpha) :
    ∃ M : ℝ, 0 < M ∧ ∀ K : ℝ, 0 < K →
      (∑' n, featureWeight c C g p q n * sourceDerivativeL4Factor alpha K n) ≤
        M * Real.exp (M * featureScaleChi p K) := by
  obtain ⟨A, hA, hbound⟩ := exists_uniform_feature_series_bound c C g p q alpha
    hc hC hp hq halpha
  let s : ℝ := 1 + (4 : ℝ) ^ (1 / alpha)
  let B : ℝ := (1 + Real.log (s + 2)) ^ (p / (p - 1))
  have hs : 0 < s := by dsimp [s]; positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Real.rpow_nonneg (by linarith [Real.log_nonneg (by linarith : 1 ≤ s + 2)]) _
  let M : ℝ := A * (B + 1) + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hAM : A ≤ M := by dsimp [M]; nlinarith
  have hABM : A * B ≤ M := by dsimp [M]; nlinarith
  refine ⟨M, hM, ?_⟩
  intro K hK
  let Kstar := s * (1 + K)
  have hKstar : 0 < Kstar := by dsimp [Kstar]; positivity
  have hterm (n : ℕ) : featureWeight c C g p q n * sourceDerivativeL4Factor alpha K n ≤
      featureWeight c C g p q n * (2 + (1 : ℝ) ^ (n + 1) + Kstar ^ (n + 1) *
        ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha)) :=
    mul_le_mul_of_nonneg_left (sourceDerivativeL4Factor_le_amplitude alpha K halpha hK n)
      (featureWeight_nonneg c C g p q hC n)
  have hsmall : Summable (fun n => featureWeight c C g p q n * sourceDerivativeL4Factor alpha K n) := by
    simpa only [sourceDerivativeL4Factor_eq] using
      summable_source_derivative_L4_majorant c C g p q alpha K hc hC hp hq halpha hK
  have hlarge := summable_feature_amplitude c C g p q Kstar 1 alpha hc hp hq hKstar (by norm_num)
  have hsum := hsmall.tsum_le_tsum hterm hlarge
  have hchi := featureScaleChi_scale_le p s K hp hs hK.le
  have hchi0 : 0 ≤ featureScaleChi p K := (by norm_num : (0 : ℝ) ≤ 1).trans
    (one_le_featureScaleChi p K hp hK.le)
  calc
    _ ≤ A * Real.exp (A * featureScaleChi p (Kstar + 1)) :=
      hsum.trans (hbound Kstar hKstar 1 le_rfl)
    _ ≤ A * Real.exp ((A * B) * featureScaleChi p K) := by
      apply mul_le_mul_of_nonneg_left _ hA.le
      apply Real.exp_le_exp.mpr
      change A * featureScaleChi p (s * (1 + K) + 1) ≤ _
      nlinarith [mul_le_mul_of_nonneg_left hchi hA.le]
    _ ≤ M * Real.exp (M * featureScaleChi p K) :=
      mul_le_mul hAM (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hABM hchi0))
        (Real.exp_pos _).le hM.le

/-- The exact source coefficient is controlled by d² times the fourth power
of its genuine derivative L4 coordinate sum, without changing that coefficient. -/
theorem sourceHilbertSchmidtFourthMoment_le_series_four
    (d : ℕ) (c C g p q alpha K : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (halpha : 0 < alpha) (hK : 0 < K) :
    sourceHilbertSchmidtFourthMoment d c C g p q alpha K ≤
      (d : ℝ) ^ 2 * (∑' n, featureWeight c C g p q n * sourceDerivativeL4Factor alpha K n) ^ 4 := by
  let b := fun n => featureWeight c C g p q n * sourceDerivativeL4Factor alpha K n
  have hb : Summable b := by
    simpa only [b, sourceDerivativeL4Factor_eq] using
      summable_source_derivative_L4_majorant c C g p q alpha K hc hC hp hq halpha hK
  have hb0 (n : ℕ) : 0 ≤ b n := by
    dsimp [b, sourceDerivativeL4Factor]
    exact mul_nonneg (featureWeight_nonneg c C g p q hC n) (by positivity)
  have hsum := tsum_sq_le_sq_tsum_nonneg b hb hb0
  have hid (n : ℕ) : (sourceFeatureScale c p n) ^ 2 * (featureGrowth C g q n) ^ 2 *
      (sourceDerivativeL4Factor alpha K n) ^ 2 = b n ^ 2 := by
    dsimp [b, sourceFeatureScale, featureGrowth, featureWeight]
    ring
  unfold sourceHilbertSchmidtFourthMoment
  simp_rw [hid]
  calc
    _ ≤ ((d : ℝ) * (∑' n, b n) ^ 2) ^ 2 := by
      apply pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (tsum_nonneg (fun n => sq_nonneg _)))
      exact mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ = _ := by dsimp [b]; ring

/-- Uniform source C_Phi,4 growth with the dimension factor explicit. The
same constant works for every finite input dimension and all K>0. -/
theorem exists_uniform_sourceHilbertSchmidtFourthMoment_dim_bound
    (c C g p q alpha : ℝ) (hc : 0 < c) (hC : 0 ≤ C)
    (hp : 1 < p) (hq : q < p) (halpha : 0 < alpha) :
    ∃ M : ℝ, 0 < M ∧ ∀ d : ℕ, ∀ K : ℝ, 0 < K →
      sourceHilbertSchmidtFourthMoment d c C g p q alpha K ≤
        (d : ℝ) ^ 2 * (M * Real.exp (M * featureScaleChi p K)) := by
  obtain ⟨A, hA, hbound⟩ := exists_uniform_sourceDerivativeL4_series_bound
    c C g p q alpha hc hC hp hq halpha
  let M : ℝ := 1 + A ^ 4 + 4 * A
  have hM : 0 < M := by dsimp [M]; positivity
  have hcoef : A ^ 4 ≤ M := by dsimp [M]; linarith
  have hexp : 4 * A ≤ M := by dsimp [M]; nlinarith [pow_nonneg hA.le 4]
  refine ⟨M, hM, ?_⟩
  intro d K hK
  have hS : 0 ≤ ∑' n, featureWeight c C g p q n * sourceDerivativeL4Factor alpha K n := by
    apply tsum_nonneg
    intro n
    exact mul_nonneg (featureWeight_nonneg c C g p q hC n)
      (by unfold sourceDerivativeL4Factor; positivity)
  have hchi0 : 0 ≤ featureScaleChi p K := (by norm_num : (0 : ℝ) ≤ 1).trans
    (one_le_featureScaleChi p K hp hK.le)
  calc
    _ ≤ (d : ℝ) ^ 2 * (∑' n, featureWeight c C g p q n * sourceDerivativeL4Factor alpha K n) ^ 4 :=
      sourceHilbertSchmidtFourthMoment_le_series_four d c C g p q alpha K hc hC hp hq halpha hK
    _ ≤ (d : ℝ) ^ 2 * (A * Real.exp (A * featureScaleChi p K)) ^ 4 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hS (hbound K hK) 4) (sq_nonneg _)
    _ = (d : ℝ) ^ 2 * (A ^ 4 * Real.exp ((4 * A) * featureScaleChi p K)) := by
      simp only [mul_pow, ← Real.exp_nat_mul, Nat.cast_ofNat, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul hcoef (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hexp hchi0))
        (Real.exp_pos _).le hM.le) (sq_nonneg _)

/-- The source-style fixed-d constant is still chosen before the population
scale K; no K-dependent coefficient is hidden in this quantifier order. -/
theorem exists_uniform_sourceHilbertSchmidtFourthMoment_bound
    (d : ℕ) (c C g p q alpha : ℝ) (hc : 0 < c) (hC : 0 ≤ C)
    (hp : 1 < p) (hq : q < p) (halpha : 0 < alpha) :
    ∃ M : ℝ, 0 < M ∧ ∀ K : ℝ, 0 < K →
      sourceHilbertSchmidtFourthMoment d c C g p q alpha K ≤
        M * Real.exp (M * featureScaleChi p K) := by
  obtain ⟨A, hA, hbound⟩ := exists_uniform_sourceHilbertSchmidtFourthMoment_dim_bound
    c C g p q alpha hc hC hp hq halpha
  let M : ℝ := 1 + A + (d : ℝ) ^ 2 * A
  have hM : 0 < M := by dsimp [M]; positivity
  have hcoef : (d : ℝ) ^ 2 * A ≤ M := by dsimp [M]; linarith
  have hexp : A ≤ M := by dsimp [M]; nlinarith [sq_nonneg (d : ℝ)]
  refine ⟨M, hM, ?_⟩
  intro K hK
  have hchi0 : 0 ≤ featureScaleChi p K := (by norm_num : (0 : ℝ) ≤ 1).trans
    (one_le_featureScaleChi p K hp hK.le)
  calc
    _ ≤ (d : ℝ) ^ 2 * (A * Real.exp (A * featureScaleChi p K)) := hbound d K hK
    _ = ((d : ℝ) ^ 2 * A) * Real.exp (A * featureScaleChi p K) := by ring
    _ ≤ _ := mul_le_mul hcoef
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hexp hchi0)) (Real.exp_pos _).le hM.le

end PaperFormalization.Manuscript
