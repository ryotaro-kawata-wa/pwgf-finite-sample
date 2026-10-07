import PaperFormalization.Manuscript.UniformFeatureSeries
import PaperFormalization.Manuscript.SourceRegionObjective
import PaperFormalization.Manuscript.FeatureDisplacement

/-! # Uniform source radius and comparison coefficients

Constants are chosen before K,D. The objective anchor is fixed throughout;
its dependence is retained. Literal radius and Lambda series are used.
-/

open scoped NNReal

namespace PaperFormalization.Manuscript

/-- Adding the anchor one preserves the exact uniform chi(K+D) scale. -/
theorem exists_uniform_sourceMomentRadius_bound (c C g p q alpha : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (halpha : 0 < alpha) :
    ∃ M : ℝ, 0 < M ∧ ∀ K : ℝ, 0 < K → ∀ D : ℝ, 1 ≤ D →
      sourceMomentRadius c C g p q K D alpha ≤
        M * Real.exp (M * featureScaleChi p (K + D)) := by
  obtain ⟨A, hA, hbound⟩ := exists_uniform_feature_series_bound c C g p q alpha
    hc hC hp hq halpha
  refine ⟨A + 1, by positivity, ?_⟩
  intro K hK D hD
  have hchi : 0 ≤ featureScaleChi p (K + D) :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_featureScaleChi p (K + D) hp (by linarith))
  have he : 1 ≤ Real.exp ((A + 1) * featureScaleChi p (K + D)) :=
    Real.one_le_exp (by positivity)
  have hmono : Real.exp (A * featureScaleChi p (K + D)) ≤
      Real.exp ((A + 1) * featureScaleChi p (K + D)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  unfold sourceMomentRadius
  have hb := hbound K hK D hD
  nlinarith [mul_le_mul_of_nonneg_left hmono hA.le]

/-- Every fixed nonnegative polynomial monomial in the actual radius has
one uniform coefficient chosen before the population/localization scales. -/
theorem exists_uniform_sourceMomentRadius_power_bound (c C g p q alpha A : ℝ) (k : ℕ)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (halpha : 0 < alpha)
    (hA : 0 ≤ A) :
    ∃ M : ℝ, 0 < M ∧ ∀ K : ℝ, 0 < K → ∀ D : ℝ, 1 ≤ D →
      A * sourceMomentRadius c C g p q K D alpha ^ k ≤
        M * Real.exp (M * featureScaleChi p (K + D)) := by
  obtain ⟨B, hB, hb⟩ := exists_uniform_sourceMomentRadius_bound c C g p q alpha
    hc hC hp hq halpha
  let M := 1 + (k : ℝ) * B + A * B ^ k
  have hM : 0 < M := by dsimp [M]; positivity
  have hcoef : A * B ^ k ≤ M := by dsimp [M]; nlinarith [mul_nonneg (Nat.cast_nonneg k) hB.le]
  have hexp : (k : ℝ) * B ≤ M := by dsimp [M]; nlinarith [mul_nonneg hA (pow_nonneg hB.le k)]
  refine ⟨M, hM, ?_⟩
  intro K hK D hD
  have hchi : 0 ≤ featureScaleChi p (K + D) :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_featureScaleChi p (K + D) hp (by linarith))
  have hR : 0 ≤ sourceMomentRadius c C g p q K D alpha :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_sourceMomentRadius c C g p q K D alpha hC hK.le (by linarith))
  calc
    _ ≤ A * (B * Real.exp (B * featureScaleChi p (K + D))) ^ k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR (hb K hK D hD) k) hA
    _ = (A * B ^ k) * Real.exp (((k : ℝ) * B) * featureScaleChi p (K + D)) := by
      simp only [mul_pow, ← Real.exp_nat_mul, mul_assoc]
    _ ≤ M * Real.exp (M * featureScaleChi p (K + D)) :=
      mul_le_mul hcoef (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hexp hchi))
        (Real.exp_pos _).le hM.le

/-- The original Lambda sum is controlled by twice L times the original
radius, with convergence and every scale retained. -/
theorem featureDisplacementLambda_le_radius (c C g p q K D alpha : ℝ) (L : ℝ≥0)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (hD : 1 ≤ D) :
    featureDisplacementLambda c C g p q D L ≤
      2 * (L : ℝ) * sourceMomentRadius c C g p q K D alpha := by
  have hs := (summable_sourceMomentRadius_summand c C g p q K D alpha hc hp hq hK hD).mul_left
    (2 * (L : ℝ))
  have ht : ∀ n, (featureResidualWeight c p L n : ℝ) *
      (featureGrowth C g q n * (1 + 2 * D ^ n)) ≤
      2 * (L : ℝ) * (featureWeight c C g p q n *
        (2 + D ^ (n + 1) + K ^ (n + 1) *
          ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha))) := by
    intro n
    have hDpow : D ^ n ≤ D ^ (n + 1) := pow_le_pow_right₀ hD (Nat.le_succ n)
    have hpop : 0 ≤ K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha) := by positivity
    have hw : 0 ≤ (L : ℝ) * featureWeight c C g p q n :=
      mul_nonneg L.coe_nonneg (featureWeight_nonneg c C g p q hC n)
    have hsmall : 1 + 2 * D ^ n ≤ 2 * (2 + D ^ (n + 1) +
        K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha)) := by linarith
    have h := mul_le_mul_of_nonneg_left hsmall hw
    calc
      _ = (L : ℝ) * featureWeight c C g p q n * (1 + 2 * D ^ n) := by
        rw [featureResidualWeight_coe]
        unfold featureGrowth featureWeight
        ring
      _ ≤ _ := h
      _ = _ := by ring

  have hsum := (summable_featureDisplacement c C g p q D L hc hC hp hq hD).tsum_le_tsum ht hs
  rw [tsum_mul_left] at hsum
  unfold featureDisplacementLambda sourceMomentRadius
  nlinarith [L.coe_nonneg]

section Objective
variable {E : Type*} [Zero E] {H : ℕ → Type*}
  [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℝ (H n)]

/-- The literal 4QR³ envelope has the same uniform scale, with the actual
fixed anchor Q retained in the dependence of the existential constant. -/
theorem exists_uniform_sourceComparisonEnvelope_bound
    (c C g p q alpha C3 : ℝ) (φ : ∀ n, E → H n) (G : lp H 2 → ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (halpha : 0 < alpha) :
    ∃ M : ℝ, 0 < M ∧ ∀ K : ℝ, 0 < K → ∀ D : ℝ, 1 ≤ D →
      |sourceComparisonEnvelope c C g p q K D alpha C3 φ G| ≤
        M * Real.exp (M * featureScaleChi p (K + D)) := by
  obtain ⟨M, hM, hb⟩ := exists_uniform_sourceMomentRadius_power_bound c C g p q alpha
    (4 * |sourceObjectiveAnchorFactor c p C3 φ G|) 3 hc hC hp hq halpha (by positivity)
  refine ⟨M, hM, ?_⟩
  intro K hK D hD
  have hR : 0 ≤ sourceMomentRadius c C g p q K D alpha :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_sourceMomentRadius c C g p q K D alpha hC hK.le (by linarith))
  simpa only [sourceComparisonEnvelope, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
    abs_pow, abs_of_nonneg hR] using hb K hK D hD

end Objective
end PaperFormalization.Manuscript
