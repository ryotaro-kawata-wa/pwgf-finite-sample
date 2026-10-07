import PaperFormalization.Piecewise.Gronwall
import PaperFormalization.Manuscript.FirstExit
import PaperFormalization.Manuscript.BranchTrace

/-! # Piecewise comparison for a single path, up to and including a candidate exit

The path's value at a jump is its post-jump value. Each closed AC branch uses
its separate pre-jump terminal value; BranchTrace proves that value is the
actual left limit. The differential inequalities are required only before
the pathwise exit, and the jump inequalities at or before it. In particular,
a jump at a finite candidate exit is used exactly once.

Coefficient and forcing integrability remain explicit hypotheses. Deriving
these and the branch AC hypotheses for the particle model is separate work.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PaperFormalization.Manuscript

open Continuous Piecewise

/-- A branch ending at or before the exit needs the differential inequality only before the exit. -/
theorem ae_deriv_le_of_before_exit (r beta f : ℝ → ℝ) (R T s t : ℝ)
    (htExit : (t : WithTop ℝ) ≤ exitTime r R T)
    (hineq : ∀ᵐ (u : ℝ) ∂volume.restrict (Ioo s t),
      (u : WithTop ℝ) < exitTime r R T → deriv r u ≤ -beta u * r u + f u) :
    ∀ᵐ (u : ℝ) ∂volume.restrict (Ioo s t), deriv r u ≤ -beta u * r u + f u := by
  rw [ae_restrict_iff' measurableSet_Ioo] at hineq ⊢
  filter_upwards [hineq] with u hu
  intro humem
  have hut : (u : WithTop ℝ) < (t : WithTop ℝ) := by exact_mod_cast humem.2
  exact hu humem (lt_of_lt_of_le hut htExit)

/-- Transfer the original path's pre-exit inequality to its closed pre-jump branch. -/
theorem ae_closedBranch_deriv_le_of_before_exit (r beta f : ℝ → ℝ) (R T s t pre : ℝ)
    (htExit : (t : WithTop ℝ) ≤ exitTime r R T)
    (hineq : ∀ᵐ (u : ℝ) ∂volume.restrict (Ioo s t),
      (u : WithTop ℝ) < exitTime r R T → deriv r u ≤ -beta u * r u + f u) :
    ∀ᵐ (u : ℝ) ∂volume.restrict (Ioo s t),
      deriv (closedBranch r t pre) u ≤ -beta u * closedBranch r t pre u + f u := by
  have h := ae_deriv_le_of_before_exit r beta f R T s t htExit hineq
  rw [ae_restrict_iff' measurableSet_Ioo] at h ⊢
  filter_upwards [h] with u hu
  intro humem
  rw [closedBranch_deriv_eqOn_Iio r t pre humem.2,
    closedBranch_of_ne r t pre u (ne_of_lt humem.2)]
  exact hu humem

/-- The manuscript-shaped stopped comparison, including a finite candidate exit.
The supplied prefix contains exactly the jumps up to the observation time. -/
theorem stopped_piecewise_gronwall (tau pre J b : ℕ → ℝ) (r beta f : ℝ → ℝ)
    (R T t : ℝ) (n : ℕ) (htau0 : tau 0 = 0)
    (htime : ∀ k < n, tau k < tau (k + 1))
    (hbranch : ∀ k < n, AbsolutelyContinuousOnInterval
      (closedBranch r (tau (k + 1)) (pre k)) (tau k) (tau (k + 1)))
    (hbeta : IntervalIntegrable beta volume 0 t)
    (hf : IntervalIntegrable f volume 0 t)
    (hineq : ∀ k < n, ∀ᵐ (u : ℝ) ∂volume.restrict (Ioo (tau k) (tau (k + 1))),
      (u : WithTop ℝ) < exitTime r R T → deriv r u ≤ -beta u * r u + f u)
    (hJ : ∀ k < n, 0 ≤ J k)
    (hjump : ∀ k < n, (tau (k + 1) : WithTop ℝ) ≤ exitTime r R T →
      r (tau (k + 1)) ≤ J k * pre k + b k)
    (ht : tau n ≤ t) (htExit : (t : WithTop ℝ) ≤ exitTime r R T)
    (hfinal : AbsolutelyContinuousOnInterval r (tau n) t)
    (hineq_final : ∀ᵐ (u : ℝ) ∂volume.restrict (Ioo (tau n) t),
      (u : WithTop ℝ) < exitTime r R T → deriv r u ≤ -beta u * r u + f u)
    (hzero : r 0 = 0) :
    r t ≤ (∫ v in 0..t, propagator beta t v * jumpWeight tau J n v * f v) +
      ∑ i ∈ Finset.range n, propagator beta t (tau (i + 1)) *
        jumpWeight tau J n (tau (i + 1)) * b i := by
  have hend : ∀ k < n, tau (k + 1) ≤ t := by
    intro k hk
    exact le_trans (time_mono_prefix tau n (fun j hj => (htime j hj).le)
      (k + 1) n (Nat.succ_le_of_lt hk) (le_refl n)) ht
  have hendExit : ∀ k < n, (tau (k + 1) : WithTop ℝ) ≤ exitTime r R T := by
    intro k hk
    have hkt : (tau (k + 1) : WithTop ℝ) ≤ (t : WithTop ℝ) := by exact_mod_cast hend k hk
    exact le_trans hkt htExit
  have hb : IntervalIntegrable beta volume (tau 0) t := by simpa only [htau0] using hbeta
  have hforcing : IntervalIntegrable f volume (tau 0) t := by simpa only [htau0] using hf
  have hbranch_ineq : ∀ k < n, ∀ᵐ (u : ℝ) ∂volume.restrict (Ioo (tau k) (tau (k + 1))),
      deriv (closedBranch r (tau (k + 1)) (pre k)) u ≤
        -beta u * closedBranch r (tau (k + 1)) (pre k) u + f u := by
    intro k hk
    exact ae_closedBranch_deriv_le_of_before_exit r beta f R T (tau k) (tau (k + 1))
      (pre k) (hendExit k hk) (hineq k hk)
  have hstart : ∀ k < n, closedBranch r (tau (k + 1)) (pre k) (tau k) = r (tau k) := by
    intro k hk
    exact closedBranch_of_ne r (tau (k + 1)) (pre k) (tau k) (ne_of_lt (htime k hk))
  have hjumps : ∀ k < n, r (tau (k + 1)) ≤
      J k * closedBranch r (tau (k + 1)) (pre k) (tau (k + 1)) + b k := by
    intro k hk
    simpa only [closedBranch_terminal] using hjump k hk (hendExit k hk)
  have hr0 : r (tau 0) = 0 := by simpa only [htau0] using hzero
  have hbound := finite_piecewise_gronwall_strict_schedule tau
    (fun k => closedBranch r (tau (k + 1)) (pre k)) (fun k => r (tau k)) J b beta f r n t
    htime hbranch hb hforcing hbranch_ineq hstart hJ hjumps ht hfinal
    (ae_deriv_le_of_before_exit r beta f R T (tau n) t htExit hineq_final) rfl hr0
  simpa only [htau0] using hbound

end PaperFormalization.Manuscript
