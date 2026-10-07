import PaperFormalization.Manuscript.FeatureRegularityBounds
import PaperFormalization.Manuscript.SourceFeatureSecondMoment

/-! # Concrete source series for clipping amplitude, time rate, and bias

All three scalar convergence inputs use the actual source weight L*a_(n+1)
and derivative-growth factor L_(n+1). The population L2 envelope retains its
order-2m moment exactly, represented by the effective scale K*2^(1/alpha).
No convergence of the desired residual or additional population moment is
assumed in this unit.
-/

open scoped NNReal

namespace PaperFormalization.Manuscript

/-- The clipped amplitude series converges for the actual source weights. -/
theorem summable_source_clipped_amplitude (c C g p q D : ℝ) (L : ℝ≥0)
    (hc : 0 < c) (hp : 1 < p) (hq : q < p) (hD : 1 ≤ D) :
    Summable (fun n => (featureResidualWeight c p L n : ℝ) *
      (featureGrowth C g q n * (1 + D ^ (n + 1)))) := by
  have hs := (summable_feature_regularity_envelope c C g p q D hc hp hq hD).mul_left (L : ℝ)
  apply hs.congr
  intro n
  rw [featureResidualWeight_coe]
  unfold featureWeight featureGrowth
  ring

/-- The exact source time-rate series with 1+2D^(m-1) also converges. -/
theorem summable_source_clipped_rate (c C g p q D : ℝ) (L : ℝ≥0)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hD : 1 ≤ D) :
    Summable (fun n => (featureResidualWeight c p L n : ℝ) *
      (featureGrowth C g q n * (1 + 2 * D ^ n))) := by
  apply (summable_source_clipped_amplitude c C g p q D L hc hp hq hD).mul_left 2
    |>.of_nonneg_of_le
  · intro n
    exact mul_nonneg (featureResidualWeight c p L n).coe_nonneg
      (mul_nonneg (featureGrowth_nonneg C g q hC n) (by positivity))
  · intro n
    have hpow : D ^ n ≤ D ^ (n + 1) := pow_le_pow_right₀ hD (Nat.le_succ n)
    have hG := featureGrowth_nonneg C g q hC n
    have hw := (featureResidualWeight c p L n).coe_nonneg
    have hm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (show 1 + 2 * D ^ n ≤ 2 * (1 + D ^ (n + 1)) by linarith) hG) hw
    exact hm.trans_eq (by ring)

/-- The displayed source L2 envelope is exactly an m-th-moment envelope at
scale K*2^(1/alpha); no bound or numerical enlargement is used here. -/
theorem sourceCoordinateL2Envelope_eq_scaled_moment
    (C g q alpha K : ℝ) (n : ℕ) :
    sourceCoordinateL2Envelope C g q alpha K n = featureGrowth C g q n *
      (1 + (K * (2 : ℝ) ^ (1 / alpha)) ^ (n + 1) *
        ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha)) := by
  have he : (K * (2 * ((n + 1 : ℕ) : ℝ)) ^ (1 / alpha)) ^ (n + 1) =
      (K * (2 : ℝ) ^ (1 / alpha)) ^ (n + 1) *
        ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg _),
      ← mul_assoc, mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    congr 2
    ring
  simp only [sourceCoordinateL2Envelope, he]

/-- The exact source order-2m L2-envelope sum S converges against the original
super-exponential weights, with unchanged alpha and K in its displayed form. -/
theorem summable_source_clipping_L2_envelope (c C g p q alpha K : ℝ) (L : ℝ≥0)
    (hc : 0 < c) (hp : 1 < p) (hq : q < p) (hK : 0 < K) :
    Summable (fun n => (featureResidualWeight c p L n : ℝ) *
      sourceCoordinateL2Envelope C g q alpha K n) := by
  have hs := ((summable_featureWeight c C g p q hc hp hq).add
    (summable_featureWeight_moment c C g p q (K * (2 : ℝ) ^ (1 / alpha)) alpha
      hc hp hq (by positivity))).mul_left (L : ℝ)
  apply hs.congr
  intro n
  rw [featureResidualWeight_coe, sourceCoordinateL2Envelope_eq_scaled_moment]
  unfold featureWeight featureGrowth
  ring

end PaperFormalization.Manuscript
