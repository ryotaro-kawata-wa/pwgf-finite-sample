import PaperFormalization.Manuscript.GrowthSummability

/-! # Summability of the manuscript's actual feature-weight envelopes

The index n represents m=n+1. `featureWeight` is exactly a_m L_m. All
statements are for fixed finite scales; quantitative uniform dependence
on K,D is not replaced by a claimed dimension-free constant.
-/

namespace PaperFormalization.Manuscript

/-- The manuscript product a_m L_m at m=n+1. -/
noncomputable def featureWeight (c C g p q : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ p) *
    (C * (n + 1) * Real.exp (g * ((n + 1 : ℕ) : ℝ) ^ q))

/-- Feature weights are nonnegative for a nonnegative feature amplitude. -/
theorem featureWeight_nonneg (c C g p q : ℝ) (hC : 0 ≤ C) (n : ℕ) :
    0 ≤ featureWeight c C g p q n := by
  unfold featureWeight
  positivity

/-- Exponential localization growth and moment-log growth remain summable. -/
theorem summable_featureWeight_exp (c C g p q s a : ℝ)
    (hc : 0 < c) (hp : 1 < p) (hq : q < p) :
    Summable (fun n : ℕ => featureWeight c C g p q n *
      Real.exp (s * (n + 1) + a * (((n + 1 : ℕ) : ℝ) * Real.log (n + 1)))) := by
  have h := (summable_exp_decay_growth c p q g a s 1 hc hp hq).mul_left C
  apply h.congr
  intro n
  have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  simp only [featureWeight, Real.exp_add, one_mul, Real.exp_log hm, Nat.cast_add,
    Nat.cast_one, mul_assoc]
  ring

/-- The feature-weight sequence itself is summable. -/
theorem summable_featureWeight (c C g p q : ℝ)
    (hc : 0 < c) (hp : 1 < p) (hq : q < p) :
    Summable (featureWeight c C g p q) := by
  simpa only [zero_mul, add_zero, Real.exp_zero, mul_one] using
    summable_featureWeight_exp c C g p q 0 0 hc hp hq

/-- Bounded-support powers have a summable weighted feature envelope. -/
theorem summable_featureWeight_pow (c C g p q D : ℝ)
    (hc : 0 < c) (hp : 1 < p) (hq : q < p) (hD : 0 < D) :
    Summable (fun n : ℕ => featureWeight c C g p q n * D ^ (n + 1)) := by
  have h := summable_featureWeight_exp c C g p q (Real.log D) 0 hc hp hq
  apply h.congr
  intro n
  simp only [zero_mul, add_zero]
  congr 1
  rw [mul_comm, ← Nat.cast_add_one, Real.exp_nat_mul, Real.exp_log hD]

/-- The population moment scale K^m m^(m/alpha) is summable against a_m L_m. -/
theorem summable_featureWeight_moment (c C g p q K alpha : ℝ)
    (hc : 0 < c) (hp : 1 < p) (hq : q < p) (hK : 0 < K) :
    Summable (fun n : ℕ => featureWeight c C g p q n *
      (K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha))) := by
  have h := summable_featureWeight_exp c C g p q (Real.log K) (1 / alpha) hc hp hq
  apply h.congr
  intro n
  have hm : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [Real.exp_add]
  congr 1
  congr 1
  · rw [mul_comm, ← Nat.cast_add_one, Real.exp_nat_mul, Real.exp_log hK]
  · rw [Real.rpow_def_of_pos hm]
    congr 1
    push_cast
    ring

/-- The complete amplitude majorant displayed in the manuscript is summable. -/
theorem summable_feature_amplitude (c C g p q K D alpha : ℝ)
    (hc : 0 < c) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (hD : 0 < D) :
    Summable (fun n : ℕ => featureWeight c C g p q n *
      (2 + D ^ (n + 1) + K ^ (n + 1) *
        ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha))) := by
  have h := ((summable_featureWeight c C g p q hc hp hq).mul_right 2).add
    (summable_featureWeight_pow c C g p q D hc hp hq hD) |>.add
      (summable_featureWeight_moment c C g p q K alpha hc hp hq hK)
  apply h.congr
  intro n
  ring

/-- The m-1 population time envelope is controlled by the existing m-th moment
scale, enlarged only from K to 1+K as in the manuscript. -/
theorem previous_moment_le_full (K alpha : ℝ) (hK : 0 ≤ K) (halpha : 0 < alpha)
    (n : ℕ) :
    (K * ((n + 1 : ℕ) : ℝ) ^ (1 / alpha)) ^ n ≤
      (1 + K) ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha) := by
  have hm : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_cast; omega
  have hz : 1 ≤ ((n + 1 : ℕ) : ℝ) ^ (1 / alpha) :=
    Real.one_le_rpow hm (by positivity)
  have hb : 1 ≤ (1 + K) * ((n + 1 : ℕ) : ℝ) ^ (1 / alpha) := by nlinarith
  calc
    (K * ((n + 1 : ℕ) : ℝ) ^ (1 / alpha)) ^ n ≤
        ((1 + K) * ((n + 1 : ℕ) : ℝ) ^ (1 / alpha)) ^ n := by
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)) (1 / alpha)]
    _ ≤ ((1 + K) * ((n + 1 : ℕ) : ℝ) ^ (1 / alpha)) ^ (n + 1) :=
      pow_le_pow_right₀ hb (Nat.le_succ n)
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast (by positivity)]
      congr 2
      ring

/-- The temporal majorant for the empirical/population moment residual is summable. -/
theorem summable_feature_time_majorant (c C g p q K D alpha : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hK : 0 ≤ K) (hD : 1 ≤ D) (halpha : 0 < alpha) :
    Summable (fun n : ℕ => featureWeight c C g p q n *
      (2 + D ^ n + 2 * (K * ((n + 1 : ℕ) : ℝ) ^ (1 / alpha)) ^ n)) := by
  have h := (summable_feature_amplitude c C g p q (1 + K) D alpha hc hp hq
    (by linarith) (by linarith)).mul_left 2
  apply h.of_nonneg_of_le
  · intro n
    exact mul_nonneg (featureWeight_nonneg c C g p q hC n) (by positivity)
  · intro n
    have hw := featureWeight_nonneg c C g p q hC n
    have hDn : D ^ n ≤ D ^ (n + 1) := pow_le_pow_right₀ hD (Nat.le_succ n)
    have hprev := previous_moment_le_full K alpha hK halpha n
    have hdnonneg := pow_nonneg (by linarith : 0 ≤ D) (n + 1)
    calc
      featureWeight c C g p q n *
          (2 + D ^ n + 2 * (K * ((n + 1 : ℕ) : ℝ) ^ (1 / alpha)) ^ n) ≤
        featureWeight c C g p q n *
          (2 * (2 + D ^ (n + 1) + (1 + K) ^ (n + 1) *
            ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha))) := by
          apply mul_le_mul_of_nonneg_left _ hw
          nlinarith
      _ = _ := by ring

end PaperFormalization.Manuscript
