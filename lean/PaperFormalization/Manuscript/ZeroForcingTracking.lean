import PaperFormalization.Manuscript.NonlinearComparison
import PaperFormalization.Manuscript.ExitAttainment

/-! # The complete deterministic zero-forcing alternative

A fixed positive auxiliary radius is used solely to localize the quadratic
term. There is no smallness assumption and no zero exit radius. The stopped
nonpositive estimate is derived from the actual full-schedule nonlinear
comparison, with both continuous and additive jump forcing set to zero.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PaperFormalization.Manuscript

open Piecewise

/-- Zero initial discrepancy, zero forcing and multiplicative jumps imply zero
throughout the finite horizon, without a nonlinear smallness condition. -/
theorem zero_forcing_tracking
    (tau pre J : ℕ → ℝ) (r kappa : ℝ → ℝ) (c R T : ℝ) (L : ℕ)
    (htau0 : tau 0 = 0) (htime : ∀ k < L, tau k < tau (k + 1))
    (hT : tau L ≤ T) (hc : 0 ≤ c) (hR : 0 < R)
    (hbranch : ∀ k < L, AbsolutelyContinuousOnInterval
      (closedBranch r (tau (k + 1)) (pre k)) (tau k) (tau (k + 1)))
    (hkappa : IntervalIntegrable kappa volume 0 T)
    (hr : ∀ u ∈ Icc 0 T, 0 ≤ r u)
    (hpos : ∀ k < L, ∀ᵐ (u : ℝ) ∂volume.restrict (Ioo (tau k) (tau (k + 1))),
      (u : WithTop ℝ) < exitTime r R T → 0 < r u →
      deriv r u ≤ -kappa u * r u + c * (r u) ^ 2)
    (hJ : ∀ k < L, 0 ≤ J k)
    (hjump : ∀ k < L, (tau (k + 1) : WithTop ℝ) ≤ exitTime r R T →
      r (tau (k + 1)) ≤ J k * pre k)
    (hfinal : AbsolutelyContinuousOnInterval r (tau L) T)
    (hpos_final : ∀ᵐ (u : ℝ) ∂volume.restrict (Ioo (tau L) T),
      (u : WithTop ℝ) < exitTime r R T → 0 < r u →
      deriv r u ≤ -kappa u * r u + c * (r u) ^ 2)
    (hzero : r 0 = 0) : ∀ t ∈ Icc 0 T, r t = 0 := by
  apply eq_zero_on_horizon_of_nonpos_stopped_bound r R T hR
  · intro t ht
    exact finite_schedule_right_continuous tau pre r L T t
      (fun k hk => (htime k hk).le) hbranch hfinal
      (by simpa only [htau0] using ht.1) ht.2
  · exact hr
  · intro t ht htexit
    have hcomparison := nonlinear_full_schedule_gronwall
      tau pre J (fun _ => 0) r kappa (fun _ => 0) c R T t L
      htau0 htime hT hc hbranch hkappa intervalIntegrable_const hr
      (fun _ _ => le_rfl)
      (fun k hk => by simpa only [zero_mul, add_zero] using hpos k hk)
      hJ (fun k hk hstop => by simpa only [add_zero] using hjump k hk hstop)
      hfinal (by simpa only [zero_mul, add_zero] using hpos_final)
      hzero ht.1 ht.2 htexit
    simpa only [mul_zero, intervalIntegral.integral_zero, Finset.sum_const_zero,
      add_zero] using hcomparison

end PaperFormalization.Manuscript
