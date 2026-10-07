import PaperFormalization.Piecewise.SchedulePrefix
import PaperFormalization.Manuscript.BranchTrace

/-! # Restriction to the final observed branch of a full schedule

Before the next jump, the closed branch equals the actual path even at the
observation endpoint. After the last jump, restrict the supplied final branch.
Neither case assumes continuity across a jump.
-/

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace PaperFormalization.Continuous

/-- Absolute continuity depends only on values in the closed interval. -/
theorem ac_congr_on (f g : ℝ → ℝ) (a b : ℝ)
    (hf : AbsolutelyContinuousOnInterval f a b) (heq : EqOn f g (uIcc a b)) :
    AbsolutelyContinuousOnInterval g a b := by
  unfold AbsolutelyContinuousOnInterval at hf ⊢
  apply hf.congr'
  rw [Filter.EventuallyEq, eventually_inf_principal]
  filter_upwards with E hE
  apply Finset.sum_congr rfl
  intro i hi
  rw [heq (hE.left i hi).left, heq (hE.left i hi).right]

end PaperFormalization.Continuous

namespace PaperFormalization.Manuscript

open Continuous Piecewise

/-- Strictly before its jump endpoint, a closed AC branch restricts to the original path. -/
theorem ac_closedBranch_restrict (r : ℝ → ℝ) (s e pre t : ℝ)
    (hst : s ≤ t) (hte : t < e)
    (hbranch : AbsolutelyContinuousOnInterval (closedBranch r e pre) s e) :
    AbsolutelyContinuousOnInterval r s t := by
  have hsub : uIcc s t ⊆ uIcc s e := by
    rw [uIcc_of_le hst, uIcc_of_le (le_trans hst hte.le)]
    exact Icc_subset_Icc_right hte.le
  apply ac_congr_on (closedBranch r e pre) r s t (hbranch.mono hsub)
  intro u hu
  rw [uIcc_of_le hst] at hu
  exact closedBranch_of_ne r e pre u (ne_of_lt (lt_of_le_of_lt hu.2 hte))

/-- Full-schedule branch AC supplies the final AC interval at every observation time. -/
theorem observation_branch_ac (tau pre : ℕ → ℝ) (r : ℝ → ℝ) (L : ℕ) (T t : ℝ)
    (htime : ∀ k < L, tau k ≤ tau (k + 1))
    (hbranch : ∀ k < L, AbsolutelyContinuousOnInterval
      (closedBranch r (tau (k + 1)) (pre k)) (tau k) (tau (k + 1)))
    (hfinal : AbsolutelyContinuousOnInterval r (tau L) T)
    (ht0 : tau 0 ≤ t) (htT : t ≤ T) :
    AbsolutelyContinuousOnInterval r (tau (jumpCount tau L t)) t := by
  have hnt := time_jumpCount_le tau L t htime ht0
  by_cases hn : jumpCount tau L t < L
  · exact ac_closedBranch_restrict r _ _ _ t hnt
      (lt_next_jump tau L t htime hn) (hbranch _ hn)
  · have hnL : jumpCount tau L t = L := by
      have := jumpCount_le tau L t
      omega
    rw [hnL] at hnt ⊢
    apply hfinal.mono
    rw [uIcc_of_le hnt, uIcc_of_le (le_trans hnt htT)]
    exact Icc_subset_Icc_right htT

/-- An a.e. predicate on each full branch restricts to the final observed branch. -/
theorem ae_observation_branch (tau : ℕ → ℝ) (L : ℕ) (T t : ℝ) (P : ℝ → Prop)
    (htime : ∀ k < L, tau k ≤ tau (k + 1))
    (hbranch : ∀ k < L, ∀ᵐ u ∂volume.restrict (Ioo (tau k) (tau (k + 1))), P u)
    (hfinal : ∀ᵐ u ∂volume.restrict (Ioo (tau L) T), P u)
    (htT : t ≤ T) :
    ∀ᵐ u ∂volume.restrict (Ioo (tau (jumpCount tau L t)) t), P u := by
  by_cases hn : jumpCount tau L t < L
  · apply ae_restrict_of_ae_restrict_of_subset _ (hbranch _ hn)
    exact Ioo_subset_Ioo_right (lt_next_jump tau L t htime hn).le
  · have hnL : jumpCount tau L t = L := by
      have := jumpCount_le tau L t
      omega
    rw [hnL]
    exact ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right htT) hfinal

end PaperFormalization.Manuscript
