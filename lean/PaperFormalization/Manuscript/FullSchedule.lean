import PaperFormalization.Manuscript.StoppedComparison
import PaperFormalization.Manuscript.ObservationBranch

/-! # Stopped comparison over the complete prescribed finite schedule

An arbitrary observation in `[0,T]` selects its own jump prefix. The products
and sum below use the original full schedule and exactly the manuscript's
time filters. Equality at a candidate exit is allowed. Analytic assumptions
are supplied once on the full branches and restricted in the proof.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PaperFormalization.Manuscript

open Continuous Piecewise

/-- Full-schedule, time-filtered comparison for every observation at or before the exit. -/
theorem stopped_full_schedule_gronwall
    (tau pre J b : ℕ → ℝ) (r beta f : ℝ → ℝ) (R T t : ℝ) (L : ℕ)
    (htau0 : tau 0 = 0) (htime : ∀ k < L, tau k < tau (k + 1))
    (hT : tau L ≤ T)
    (hbranch : ∀ k < L, AbsolutelyContinuousOnInterval
      (closedBranch r (tau (k + 1)) (pre k)) (tau k) (tau (k + 1)))
    (hbeta : IntervalIntegrable beta volume 0 T)
    (hf : IntervalIntegrable f volume 0 T)
    (hineq : ∀ k < L, ∀ᵐ (u : ℝ) ∂volume.restrict (Ioo (tau k) (tau (k + 1))),
      (u : WithTop ℝ) < exitTime r R T → deriv r u ≤ -beta u * r u + f u)
    (hJ : ∀ k < L, 0 ≤ J k)
    (hjump : ∀ k < L, (tau (k + 1) : WithTop ℝ) ≤ exitTime r R T →
      r (tau (k + 1)) ≤ J k * pre k + b k)
    (hfinal : AbsolutelyContinuousOnInterval r (tau L) T)
    (hineq_final : ∀ᵐ (u : ℝ) ∂volume.restrict (Ioo (tau L) T),
      (u : WithTop ℝ) < exitTime r R T → deriv r u ≤ -beta u * r u + f u)
    (hzero : r 0 = 0) (ht0 : 0 ≤ t) (htT : t ≤ T)
    (htExit : (t : WithTop ℝ) ≤ exitTime r R T) :
    r t ≤ (∫ v in 0..t, propagator beta t v *
      (∏ k ∈ (Finset.range L).filter
        (fun k => v < tau (k + 1) ∧ tau (k + 1) ≤ t), J k) * f v) +
      ∑ i ∈ (Finset.range L).filter (fun i => tau (i + 1) ≤ t),
        propagator beta t (tau (i + 1)) *
          (∏ k ∈ (Finset.range L).filter
            (fun k => tau (i + 1) < tau (k + 1) ∧ tau (k + 1) ≤ t), J k) * b i := by
  have hmono : ∀ k < L, tau k ≤ tau (k + 1) := fun k hk => (htime k hk).le
  have hnL := jumpCount_le tau L t
  have hkL : ∀ k < jumpCount tau L t, k < L := fun k hk => lt_of_lt_of_le hk hnL
  have htau0t : tau 0 ≤ t := by simpa only [htau0] using ht0
  have h0T : 0 ≤ T := by
    rw [← htau0]
    exact le_trans (time_mono_prefix tau L hmono 0 L (Nat.zero_le L) le_rfl) hT
  have hsub : uIcc 0 t ⊆ uIcc 0 T := by
    rw [uIcc_of_le ht0, uIcc_of_le h0T]
    exact Icc_subset_Icc_right htT
  have hbound := stopped_piecewise_gronwall tau pre J b r beta f R T t
    (jumpCount tau L t) htau0 (fun k hk => htime k (hkL k hk))
    (fun k hk => hbranch k (hkL k hk)) (hbeta.mono_set hsub) (hf.mono_set hsub)
    (fun k hk => hineq k (hkL k hk)) (fun k hk => hJ k (hkL k hk))
    (fun k hk => hjump k (hkL k hk)) (time_jumpCount_le tau L t hmono htau0t) htExit
    (observation_branch_ac tau pre r L T t hmono hbranch hfinal htau0t htT)
    (ae_observation_branch tau L T t
      (fun u => (u : WithTop ℝ) < exitTime r R T → deriv r u ≤ -beta u * r u + f u)
      hmono hineq hineq_final htT) hzero
  simp_rw [jumpWeight_jumpCount_eq_time_filter tau J L t _ hmono] at hbound
  rw [sum_range_jumpCount_eq_time_filter tau L t hmono] at hbound
  exact hbound

end PaperFormalization.Manuscript
