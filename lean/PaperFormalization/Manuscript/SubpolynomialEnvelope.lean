import PaperFormalization.Manuscript.UniformFeatureEnvelope
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Subpolynomial logarithmic envelopes

These deterministic bounds justify absorption of the logarithmic envelopes.
They do not assert that a stochastic concentration coefficient has this
form; that source identification remains a separate proof obligation.
-/

open Filter Asymptotics
open scoped Topology

namespace PaperFormalization.Manuscript

/-- Every fixed real power of log(log x) is little-o of log x at infinity. -/
theorem loglog_rpow_isLittleO_log (r : ℝ) :
    (fun x : ℝ => (Real.log (Real.log x)) ^ r) =o[atTop] Real.log := by
  simpa only [Function.comp_def, Real.rpow_one] using
    (isLittleO_log_rpow_rpow_atTop r (show 0 < (1 : ℝ) by norm_num)).comp_tendsto
      Real.tendsto_log_atTop

/-- The source logarithmic exponential is below every positive power,
with the threshold chosen only from the fixed envelope parameters. -/
theorem eventually_loglog_envelope_le_rpow (A r epsilon : ℝ)
    (hA : 0 ≤ A) (hr : 0 ≤ r) (he : 0 < epsilon) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (A * (1 + Real.log (Real.log x)) ^ r) ≤ x ^ epsilon := by
  let B := A * (2 : ℝ) ^ r
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hd : 0 < epsilon / (B + 1) := by positivity
  have hsmall := (loglog_rpow_isLittleO_log r).bound hd
  have hloglog : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [hsmall, hloglog.eventually (eventually_ge_atTop 1),
    eventually_gt_atTop (1 : ℝ)] with x hsmall hll hx
  have hxpos : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx.le
  have hllpos : 0 ≤ Real.log (Real.log x) := by linarith
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hllpos r), abs_of_nonneg hl] at hsmall
  have hpow : (1 + Real.log (Real.log x)) ^ r ≤
      (2 : ℝ) ^ r * (Real.log (Real.log x)) ^ r := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hllpos]
    exact Real.rpow_le_rpow (by linarith) (by linarith) hr
  have hcoef : B * (epsilon / (B + 1)) ≤ epsilon := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ (by positivity : 0 < B + 1)).mpr (by nlinarith)
  have hexponent : A * (1 + Real.log (Real.log x)) ^ r ≤ epsilon * Real.log x := by
    calc
      _ ≤ B * (Real.log (Real.log x)) ^ r := by dsimp [B]; nlinarith [mul_le_mul_of_nonneg_left hpow hA]
      _ ≤ B * ((epsilon / (B + 1)) * Real.log x) := mul_le_mul_of_nonneg_left hsmall hB
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hcoef hl]
  rw [Real.rpow_def_of_pos hxpos]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- The actual e+x shift and any fixed nonnegative prefactor preserve the
same arbitrary positive power bound. All parameters precede the threshold. -/
theorem eventually_shifted_loglog_envelope_le_rpow (A B r epsilon : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 0 ≤ r) (he : 0 < epsilon) :
    ∀ᶠ x : ℝ in atTop,
      B * Real.exp (A * (1 + Real.log (Real.log (Real.exp 1 + x))) ^ r) ≤
        x ^ epsilon := by
  have hshift : Tendsto (fun x : ℝ => Real.exp 1 + x) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with x hx
    linarith [Real.exp_pos (1 : ℝ)]
  have henv := hshift.eventually
    (eventually_loglog_envelope_le_rpow A r (epsilon / 2) hA hr (by positivity))
  have hcoef := (tendsto_rpow_atTop (show 0 < epsilon / 2 by positivity)).eventually
    (eventually_ge_atTop (B * (2 : ℝ) ^ (epsilon / 2)))
  filter_upwards [henv, hcoef, eventually_ge_atTop (Real.exp 1),
    eventually_gt_atTop (0 : ℝ)] with x hxenv hxcoef hxe hx
  calc
    _ ≤ B * (Real.exp 1 + x) ^ (epsilon / 2) := mul_le_mul_of_nonneg_left hxenv hB
    _ ≤ B * (2 * x) ^ (epsilon / 2) := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
    _ = (B * (2 : ℝ) ^ (epsilon / 2)) * x ^ (epsilon / 2) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx.le, mul_assoc]
    _ ≤ x ^ (epsilon / 2) * x ^ (epsilon / 2) :=
      mul_le_mul_of_nonneg_right hxcoef (Real.rpow_nonneg hx.le _)
    _ = x ^ epsilon := by rw [← Real.rpow_add hx]; congr 1; ring

end PaperFormalization.Manuscript
