import PaperFormalization.Manuscript.FeatureResidual
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-! # Coordinate majorants for weighted feature regularity

Index n denotes m=n+1. These bounds keep the exact source local envelope
L_m (1+D^m), including the truncated m-r exponent when m is small. The
spatial-difference theorem applies to each derivative field with its actual
Frechet derivative; it requires no continuity of that next derivative.
-/

namespace PaperFormalization.Manuscript

/-- The exact weighted common local envelope is summable. -/
theorem summable_feature_regularity_envelope (c C g p q D : ℝ)
    (hc : 0 < c) (hp : 1 < p) (hq : q < p) (hD : 1 ≤ D) :
    Summable (fun n : ℕ => featureWeight c C g p q n * (1 + D ^ (n + 1))) := by
  have h := (summable_featureWeight c C g p q hc hp hq).add
    (summable_featureWeight_pow c C g p q D hc hp hq (by linarith))
  apply h.congr
  intro n
  ring

/-- All source truncated powers are bounded by D^m on the D-ball. -/
theorem feature_truncated_power_le (D x : ℝ) (n r : ℕ)
    (hD : 1 ≤ D) (hx0 : 0 ≤ x) (hx : x ≤ D) :
    x ^ (n + 1 - r) ≤ D ^ (n + 1) := by
  exact (pow_le_pow_left₀ hx0 hx _).trans
    (pow_le_pow_right₀ hD (Nat.sub_le _ _))

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Coordinate value or derivative growth gives the common local majorant. -/
theorem feature_norm_le_local_envelope (f : E → F) (D L : ℝ) (n r : ℕ)
    (hD : 1 ≤ D) (hL : 0 ≤ L)
    (hgrowth : ∀ x, ‖f x‖ ≤ L * (1 + ‖x‖ ^ (n + 1 - r)))
    (x : E) (hx : ‖x‖ ≤ D) :
    ‖f x‖ ≤ L * (1 + D ^ (n + 1)) := by
  exact (hgrowth x).trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (feature_truncated_power_le D ‖x‖ n r hD (norm_nonneg _) hx)) hL)

/-- The common local spatial bound follows from the actual next derivative.
Apply to D phi or D² phi; continuity of D³ phi is unnecessary. -/
theorem feature_derivative_sub_le_local_envelope (f : E → F) (D L : ℝ) (n r : ℕ)
    (hD : 1 ≤ D) (hL : 0 ≤ L)
    (hdiff : ∀ x ∈ Metric.closedBall (0 : E) D, DifferentiableAt ℝ f x)
    (hderiv : ∀ x ∈ Metric.closedBall (0 : E) D,
      ‖fderiv ℝ f x‖ ≤ L * (1 + ‖x‖ ^ (n + 1 - r)))
    (x y : E) (hx : ‖x‖ ≤ D) (hy : ‖y‖ ≤ D) :
    ‖f x - f y‖ ≤ L * (1 + D ^ (n + 1)) * ‖x - y‖ := by
  have hbound : ∀ z ∈ Metric.closedBall (0 : E) D,
      ‖fderiv ℝ f z‖ ≤ L * (1 + D ^ (n + 1)) := by
    intro z hz
    have hz' : ‖z‖ ≤ D := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    exact (hderiv z hz).trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (feature_truncated_power_le D ‖z‖ n r hD (norm_nonneg _) hz')) hL)
  exact (convex_closedBall (0 : E) D).norm_image_sub_le_of_norm_fderiv_le hdiff hbound
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hy)
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Source-weighted coordinate norms are controlled by the proved summable envelope. -/
theorem feature_weighted_norm_le_local_envelope (f : E → F)
    (c C g p q D : ℝ) (n r : ℕ) (hC : 0 ≤ C) (hD : 1 ≤ D)
    (hgrowth : ∀ x, ‖f x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1 - r)))
    (x : E) (hx : ‖x‖ ≤ D) :
    Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ p) * ‖f x‖ ≤
      featureWeight c C g p q n * (1 + D ^ (n + 1)) := by
  have h := mul_le_mul_of_nonneg_left
    (feature_norm_le_local_envelope f D (featureGrowth C g q n) n r hD
      (featureGrowth_nonneg C g q hC n) hgrowth x hx)
    (Real.exp_pos (-c * ((n + 1 : ℕ) : ℝ) ^ p)).le
  simpa only [featureWeight, featureGrowth, mul_assoc] using h

/-- Currying preserves the source bilinear operator norm exactly. -/
theorem norm_second_fderiv_eq_iterated (f : E → F) (x : E) :
    ‖fderiv ℝ (fderiv ℝ f) x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
  rw [← norm_iteratedFDeriv_one (fderiv ℝ f), norm_iteratedFDeriv_fderiv]

set_option maxSynthPendingDepth 8 in
/-- The same exact norm identity holds for the nested third derivative. -/
theorem norm_third_fderiv_eq_iterated (f : E → F) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x‖ = ‖iteratedFDeriv ℝ 3 f x‖ := by
  rw [← norm_iteratedFDeriv_one (fderiv ℝ (fderiv ℝ f)),
    norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv]

end PaperFormalization.Manuscript
