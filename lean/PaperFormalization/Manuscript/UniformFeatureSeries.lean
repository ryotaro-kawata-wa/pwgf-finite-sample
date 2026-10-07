import PaperFormalization.Manuscript.UniformFeatureEnvelope

/-! # The manuscript's uniform weighted-series estimate

The constants are quantified before K,D and the source feature index m=n+1.
Thus this strengthens the existing fixed-scale summability result to the
literal uniform logarithmic-exponential estimate.
-/

open scoped BigOperators

namespace PaperFormalization.Manuscript

/-- The literal amplitude is bounded by the common exponential used in the
source proof, with no constant depending on K,D. -/
theorem feature_amplitude_le_common_power (K D alpha : ℝ)
    (hK : 0 < K) (hD : 1 ≤ D) (halpha : 0 < alpha) (n : ℕ) :
    2 + D ^ (n + 1) + K ^ (n + 1) *
        ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha) ≤
      4 * (Real.exp 1 + (K + D)) ^ (n + 1) *
        ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha) := by
  let a : ℝ := (Real.exp 1 + (K + D)) ^ (n + 1)
  let b : ℝ := ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha)
  have he : 0 < Real.exp (1 : ℝ) := Real.exp_pos 1
  have ha : 1 ≤ a := one_le_pow₀ (by linarith)
  have hb : 1 ≤ b := Real.one_le_rpow (by norm_cast; omega) (by positivity)
  have hab : 1 ≤ a * b := one_le_mul_of_one_le_of_one_le ha hb
  have hDa : D ^ (n + 1) ≤ a := by
    exact pow_le_pow_left₀ (by linarith) (by linarith : D ≤ Real.exp 1 + (K + D)) (n + 1)
  have hKa : K ^ (n + 1) ≤ a := by
    exact pow_le_pow_left₀ hK.le (by linarith : K ≤ Real.exp 1 + (K + D)) (n + 1)
  have hDab : D ^ (n + 1) ≤ a * b := hDa.trans (by nlinarith)
  have hKab : K ^ (n + 1) * b ≤ a * b := mul_le_mul_of_nonneg_right hKa (by linarith)
  change 2 + D ^ (n + 1) + K ^ (n + 1) * b ≤ 4 * a * b
  nlinarith

/-- The exact source summand bound, with one positive constant chosen before
all population and localization scales. -/
theorem exists_uniform_feature_amplitude_bound (c C g p q alpha : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (halpha : 0 < alpha) :
    ∃ M : ℝ, 0 < M ∧ ∀ K : ℝ, 0 < K → ∀ D : ℝ, 1 ≤ D → ∀ n : ℕ,
      featureWeight c C g p q n *
        (2 + D ^ (n + 1) + K ^ (n + 1) *
          ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha)) ≤
      M * Real.exp (M * featureScaleChi p (K + D) -
        (c / 4) * ((n + 1 : ℕ) : ℝ) ^ p) := by
  obtain ⟨B, hB, hexponent⟩ := exists_uniform_feature_exponent_bound c g p q alpha hc hp hq
  let M : ℝ := B + 4 * C
  have hM : 0 < M := by dsimp [M]; positivity
  have hBM : B ≤ M := by dsimp [M]; linarith
  have hCM : 4 * C ≤ M := by dsimp [M]; linarith
  refine ⟨M, hM, ?_⟩
  intro K hK D hD n
  have hu : 0 ≤ K + D := by linarith
  have hm : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hbase : 0 < Real.exp 1 + (K + D) := by positivity
  let E : ℝ := -c * ((n + 1 : ℕ) : ℝ) ^ p + g * ((n + 1 : ℕ) : ℝ) ^ q +
    (1 / alpha) * (((n + 1 : ℕ) : ℝ) * Real.log (n + 1)) + Real.log (n + 1) +
    ((n + 1 : ℕ) : ℝ) * Real.log (Real.exp 1 + (K + D))
  have hE : E ≤ M * featureScaleChi p (K + D) - (c / 4) * ((n + 1 : ℕ) : ℝ) ^ p := by
    have he := hexponent (K + D) hu n
    have hchi : 0 ≤ featureScaleChi p (K + D) := (by norm_num : (0 : ℝ) ≤ 1).trans
      (one_le_featureScaleChi p (K + D) hp hu)
    exact he.trans (sub_le_sub_right (mul_le_mul_of_nonneg_right hBM hchi) _)
  have hidentity :
      featureWeight c C g p q n *
        (4 * (Real.exp 1 + (K + D)) ^ (n + 1) *
          ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha)) =
      4 * C * Real.exp E := by
    have hlog : (1 / alpha) * (((n + 1 : ℕ) : ℝ) * Real.log (n + 1)) =
        Real.log (n + 1) * (((n + 1 : ℕ) : ℝ) / alpha) := by ring
    dsimp [E]
    rw [hlog]
    have hm' : 0 < (n : ℝ) + 1 := by positivity
    have hrpow : ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha) =
        Real.exp (Real.log (n + 1) * (((n + 1 : ℕ) : ℝ) / alpha)) := by
      rw [Real.rpow_def_of_pos hm]
      push_cast
      rfl
    rw [hrpow]
    simp only [featureWeight, Real.exp_add, Real.exp_log hm', Real.exp_nat_mul, Real.exp_log hbase]
    push_cast
    ring
  calc
    _ ≤ featureWeight c C g p q n *
        (4 * (Real.exp 1 + (K + D)) ^ (n + 1) *
          ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha)) :=
      mul_le_mul_of_nonneg_left (feature_amplitude_le_common_power K D alpha hK hD halpha n)
        (featureWeight_nonneg c C g p q hC n)
    _ = 4 * C * Real.exp E := hidentity
    _ ≤ M * Real.exp (M * featureScaleChi p (K + D) -
        (c / 4) * ((n + 1 : ℕ) : ℝ) ^ p) :=
      mul_le_mul hCM (Real.exp_le_exp.mpr hE) (Real.exp_pos _).le hM.le

/-- Summing the genuine convergent weighted amplitude gives the source
uniform bound, with the constant still independent of K,D. -/
theorem exists_uniform_feature_series_bound (c C g p q alpha : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (halpha : 0 < alpha) :
    ∃ R : ℝ, 0 < R ∧ ∀ K : ℝ, 0 < K → ∀ D : ℝ, 1 ≤ D →
      (∑' n : ℕ, featureWeight c C g p q n *
        (2 + D ^ (n + 1) + K ^ (n + 1) *
          ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha))) ≤
      R * Real.exp (R * featureScaleChi p (K + D)) := by
  obtain ⟨M, hM, hterm⟩ := exists_uniform_feature_amplitude_bound c C g p q alpha
    hc hC hp hq halpha
  let a : ℕ → ℝ := fun n => Real.exp (-(c / 4) * ((n + 1 : ℕ) : ℝ) ^ p)
  have ha : Summable a := by
    apply Real.summable_exp_nat_mul_of_ge (by linarith : -(c / 4) < 0)
    intro n
    have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_cast; omega
    have hpower := Real.rpow_le_rpow_of_exponent_le hn hp.le
    simp only [Real.rpow_one] at hpower
    exact le_trans (by norm_cast; omega) hpower
  let S : ℝ := ∑' n, a n
  have hS : 0 ≤ S := tsum_nonneg (fun _ => (Real.exp_pos _).le)
  let R : ℝ := M * (S + 1) + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hMR : M ≤ R := by dsimp [R]; nlinarith
  have hMSR : M * S ≤ R := by dsimp [R]; nlinarith
  refine ⟨R, hR, ?_⟩
  intro K hK D hD
  have hu : 0 ≤ K + D := by linarith
  have hchi : 0 ≤ featureScaleChi p (K + D) := (by norm_num : (0 : ℝ) ≤ 1).trans
    (one_le_featureScaleChi p (K + D) hp hu)
  have hbound : ∀ n : ℕ, featureWeight c C g p q n *
      (2 + D ^ (n + 1) + K ^ (n + 1) *
        ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha)) ≤
      (M * Real.exp (M * featureScaleChi p (K + D))) * a n := by
    intro n
    simpa only [a, sub_eq_add_neg, Real.exp_add, neg_mul, mul_assoc] using hterm K hK D hD n
  have hsum := (summable_feature_amplitude c C g p q K D alpha hc hp hq hK
    (by linarith)).tsum_le_tsum hbound (ha.mul_left (M * Real.exp (M * featureScaleChi p (K + D))))
  calc
    _ ≤ ∑' n : ℕ, (M * Real.exp (M * featureScaleChi p (K + D))) * a n := hsum
    _ = (M * S) * Real.exp (M * featureScaleChi p (K + D)) := by
      rw [tsum_mul_left]
      dsimp [S]
      ring
    _ ≤ R * Real.exp (R * featureScaleChi p (K + D)) :=
      mul_le_mul hMSR (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hMR hchi))
        (Real.exp_pos _).le hR.le

end PaperFormalization.Manuscript
