import PaperFormalization.Manuscript.StoppedComparison

/-! # Stopped comparison for a pre-jump trace

The observation is the left trace at the next prescribed jump. Only earlier
jumps contribute their multipliers and defects. No inequality or sign premise
is required for the jump at the observation time. That time may equal the
finite candidate exit; the differential inequalities are used only before it.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PaperFormalization.Manuscript

open Continuous Piecewise

/-- Bound the pre-jump value at `tau (n + 1)` using precisely the `n` earlier jumps. -/
theorem stopped_piecewise_gronwall_pre_jump
    (tau pre J b : ℕ → ℝ) (r beta f : ℝ → ℝ) (R T : ℝ) (n : ℕ)
    (htau0 : tau 0 = 0)
    (htime : ∀ k < n + 1, tau k < tau (k + 1))
    (hbranch : ∀ k < n + 1, AbsolutelyContinuousOnInterval
      (closedBranch r (tau (k + 1)) (pre k)) (tau k) (tau (k + 1)))
    (hbeta : IntervalIntegrable beta volume 0 (tau (n + 1)))
    (hf : IntervalIntegrable f volume 0 (tau (n + 1)))
    (hineq : ∀ k < n + 1, ∀ᵐ (u : ℝ) ∂volume.restrict (Ioo (tau k) (tau (k + 1))),
      (u : WithTop ℝ) < exitTime r R T → deriv r u ≤ -beta u * r u + f u)
    (hJ : ∀ k < n, 0 ≤ J k)
    (hjump : ∀ k < n, (tau (k + 1) : WithTop ℝ) ≤ exitTime r R T →
      r (tau (k + 1)) ≤ J k * pre k + b k)
    (htExit : (tau (n + 1) : WithTop ℝ) ≤ exitTime r R T)
    (hzero : r 0 = 0) :
    pre n ≤ (∫ v in 0..tau (n + 1),
      propagator beta (tau (n + 1)) v * jumpWeight tau J n v * f v) +
      ∑ i ∈ Finset.range n, propagator beta (tau (n + 1)) (tau (i + 1)) *
        jumpWeight tau J n (tau (i + 1)) * b i := by
  have htime_prefix : ∀ k < n, tau k < tau (k + 1) :=
    fun k hk => htime k (Nat.lt_succ_of_lt hk)
  have hendExit : ∀ k < n, (tau (k + 1) : WithTop ℝ) ≤ exitTime r R T := by
    intro k hk
    have hkt : tau (k + 1) ≤ tau (n + 1) :=
      time_mono_prefix tau (n + 1) (fun j hj => (htime j hj).le)
        (k + 1) (n + 1) (Nat.succ_le_succ hk.le) (le_refl _)
    have hkt' : (tau (k + 1) : WithTop ℝ) ≤ (tau (n + 1) : WithTop ℝ) := by
      exact_mod_cast hkt
    exact le_trans hkt' htExit
  have hb : IntervalIntegrable beta volume (tau 0) (tau (n + 1)) := by
    simpa only [htau0] using hbeta
  have hforcing : IntervalIntegrable f volume (tau 0) (tau (n + 1)) := by
    simpa only [htau0] using hf
  have hbranch_ineq : ∀ k < n, ∀ᵐ (u : ℝ) ∂volume.restrict (Ioo (tau k) (tau (k + 1))),
      deriv (closedBranch r (tau (k + 1)) (pre k)) u ≤
        -beta u * closedBranch r (tau (k + 1)) (pre k) u + f u := by
    intro k hk
    exact ae_closedBranch_deriv_le_of_before_exit r beta f R T (tau k) (tau (k + 1))
      (pre k) (hendExit k hk) (hineq k (Nat.lt_succ_of_lt hk))
  have hstart : ∀ k < n, closedBranch r (tau (k + 1)) (pre k) (tau k) = r (tau k) := by
    intro k hk
    exact closedBranch_of_ne r (tau (k + 1)) (pre k) (tau k)
      (ne_of_lt (htime_prefix k hk))
  have hjumps : ∀ k < n, r (tau (k + 1)) ≤
      J k * closedBranch r (tau (k + 1)) (pre k) (tau (k + 1)) + b k := by
    intro k hk
    simpa only [closedBranch_terminal] using hjump k hk (hendExit k hk)
  have hlast := htime n (Nat.lt_succ_self n)
  have hfinal_start : closedBranch r (tau (n + 1)) (pre n) (tau n) = r (tau n) :=
    closedBranch_of_ne r (tau (n + 1)) (pre n) (tau n) (ne_of_lt hlast)
  have hr0 : r (tau 0) = 0 := by simpa only [htau0] using hzero
  have hbound := finite_piecewise_gronwall_strict_schedule tau
    (fun k => closedBranch r (tau (k + 1)) (pre k)) (fun k => r (tau k)) J b beta f
    (closedBranch r (tau (n + 1)) (pre n)) n (tau (n + 1))
    htime_prefix (fun k hk => hbranch k (Nat.lt_succ_of_lt hk)) hb hforcing
    hbranch_ineq hstart hJ hjumps hlast.le (hbranch n (Nat.lt_succ_self n))
    (ae_closedBranch_deriv_le_of_before_exit r beta f R T (tau n) (tau (n + 1))
      (pre n) htExit (hineq n (Nat.lt_succ_self n))) hfinal_start hr0
  simpa only [htau0, closedBranch_terminal] using hbound

end PaperFormalization.Manuscript
