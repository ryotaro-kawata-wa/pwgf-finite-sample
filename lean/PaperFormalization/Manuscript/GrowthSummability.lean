import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! # Decay dominates the manuscript's feature and moment growth

Indices are shifted by one to represent the manuscript's m >= 1. This module
proves convergence for each fixed localization/population scale. It does not
assert the uniform quantitative C exp(C chi(K+D)) estimate.
-/

open Filter Asymptotics
open scoped Topology

namespace PaperFormalization.Manuscript

/-- A smaller real power is little-o of a larger one at infinity. -/
theorem rpow_isLittleO_of_lt (q p : ℝ) (hqp : q < p) :
    (fun x : ℝ => x ^ q) =o[atTop] (fun x => x ^ p) := by
  apply isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact fun h => False.elim ((Real.rpow_pos_of_pos hx p).ne' h)
  · apply (tendsto_rpow_neg_atTop (sub_pos.mpr hqp)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_sub hx]
    congr 1
    ring

/-- The feature power, moment logarithm, linear scale, and prefactor logarithm
are all lower order than the decay power. -/
theorem growth_isLittleO (p q A B C D : ℝ) (hp : 1 < p) (hq : q < p) :
    (fun x : ℝ => A * x ^ q + B * (x * Real.log x) + C * x + D * Real.log x)
      =o[atTop] (fun x => x ^ p) := by
  have hx : (fun x : ℝ => x) =o[atTop] (fun x => x ^ p) := by
    simpa only [Real.rpow_one] using rpow_isLittleO_of_lt 1 p hp
  have hlog := isLittleO_log_rpow_atTop (by linarith : 0 < p)
  have hxlog : (fun x : ℝ => x * Real.log x) =o[atTop] (fun x => x ^ p) := by
    have h := (isBigO_refl (fun x : ℝ => x ^ (1 : ℝ)) atTop).mul_isLittleO
      (isLittleO_log_rpow_atTop (by linarith : 0 < p - 1))
    apply h.congr'
    · exact Eventually.of_forall (fun x => by simp only [Real.rpow_one])
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [← Real.rpow_add hx]
      congr 1
      ring
  exact (((rpow_isLittleO_of_lt q p hq).const_mul_left A).add
    (hxlog.const_mul_left B) |>.add (hx.const_mul_left C)).add (hlog.const_mul_left D)

/-- Superlinear exponential decay remains summable after the lower-order growth terms. -/
theorem summable_exp_decay_growth (c p q A B C D : ℝ)
    (hc : 0 < c) (hp : 1 < p) (hq : q < p) :
    Summable (fun n : ℕ => Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ p +
      (A * ((n + 1 : ℕ) : ℝ) ^ q + B * (((n + 1 : ℕ) : ℝ) * Real.log (n + 1)) +
        C * (n + 1) + D * Real.log (n + 1)))) := by
  have hdom : Summable (fun n : ℕ => Real.exp (-(c / 2) * ((n + 1 : ℕ) : ℝ) ^ p)) := by
    apply Real.summable_exp_nat_mul_of_ge (by linarith : -(c / 2) < 0)
    intro n
    have hbase : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_cast; omega
    have hpower := Real.rpow_le_rpow_of_exponent_le hbase hp.le
    simp only [Real.rpow_one] at hpower
    exact le_trans (by norm_cast; omega) hpower
  apply hdom.of_norm_bounded_eventually_nat
  have hlimit : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hsmall := hlimit.eventually ((growth_isLittleO p q A B C D hp hq).bound
    (by linarith : 0 < c / 2))
  filter_upwards [hsmall] with n hn
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  simp only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hnpos p)] at hn
  have h := le_trans (le_abs_self _) hn
  push_cast at h ⊢
  linarith

end PaperFormalization.Manuscript
