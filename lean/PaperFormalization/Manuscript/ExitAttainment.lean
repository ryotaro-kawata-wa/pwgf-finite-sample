import PaperFormalization.Manuscript.FullSchedule
import Mathlib.Topology.Order.Monotone

/-! # Attainment of a finite pathwise exit and the strict-margin bootstrap

A right-continuous path need not have a closed hitting set. We use only closure
of that set at its infimum and continuity from its right, including the finite
horizon. Closed pre-jump branches imply the required one-sided continuity;
no continuity across jumps or adaptedness is assumed.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace PaperFormalization.Manuscript

open Continuous Piecewise

/-- A finite exit infimum lies in the actual observation interval. -/
theorem finite_exit_mem_interval (r : ℝ → ℝ) (R T t : ℝ)
    (ht : exitTime r R T = (t : WithTop ℝ)) : t ∈ Icc 0 T := by
  have hnonempty : ∃ u ∈ Icc 0 T, R ≤ r u := by
    by_contra! h
    have htop := (exitTime_eq_top_iff r R T).mpr h
    rw [ht] at htop
    exact WithTop.coe_ne_top htop
  obtain ⟨u, hu, hur⟩ := hnonempty
  have ht0 := exitTime_nonneg r R T
  rw [ht] at ht0
  have htu := exitTime_le_of_radius_le r R T u hu hur
  rw [ht] at htu
  exact ⟨by exact_mod_cast ht0, le_trans (by exact_mod_cast htu) hu.2⟩

/-- Continuity from the right up to the horizon attains the radius at a finite exit. -/
theorem radius_le_at_finite_exit (r : ℝ → ℝ) (R T t : ℝ)
    (ht : exitTime r R T = (t : WithTop ℝ))
    (hr : ContinuousWithinAt r (Icc t T) t) : R ≤ r t := by
  classical
  let S : Set ℝ := {u | 0 ≤ u ∧ u ≤ T ∧ R ≤ r u}
  have hS : S.Nonempty := by
    by_contra! h
    have htop : exitTime r R T = ⊤ := by
      apply (exitTime_eq_top_iff r R T).mpr
      intro u hu
      exact lt_of_not_ge (fun hru => Set.notMem_empty u (h ▸ (show u ∈ S from ⟨hu.1, hu.2, hru⟩)))
    rw [ht] at htop
    exact WithTop.coe_ne_top htop
  have hbounded : BddBelow S := ⟨0, fun u hu => hu.1⟩
  have hinf : sInf S = t := by
    have hexists : ∃ u, 0 ≤ u ∧ u ≤ T ∧ R ≤ r u := hS
    change (if ∃ u, 0 ≤ u ∧ u ≤ T ∧ R ≤ r u then
      ((sInf S : ℝ) : WithTop ℝ) else ⊤) = (t : WithTop ℝ) at ht
    rw [if_pos hexists] at ht
    exact WithTop.coe_injective ht
  have hsub : S ⊆ Icc t T := by
    intro u hu
    exact ⟨hinf ▸ csInf_le hbounded hu, hu.2.1⟩
  have hcl : t ∈ closure S := hinf ▸ csInf_mem_closure hS hbounded
  have hthreshold : r t ∈ closure (Ici R) :=
    (hr.mono hsub).mem_closure hcl (fun u hu => hu.2.2)
  simpa only [IsClosed.closure_eq isClosed_Ici, mem_Ici] using hthreshold

/-- A strict bound at every possible candidate exit rules out all exits. -/
theorem exitTime_eq_top_of_strict_candidate_bound (r : ℝ → ℝ) (R T : ℝ)
    (hr : ∀ t ∈ Icc 0 T, ContinuousWithinAt r (Icc t T) t)
    (hbound : ∀ t ∈ Icc 0 T,
      (t : WithTop ℝ) ≤ exitTime r R T → r t < R) : exitTime r R T = ⊤ := by
  by_contra hne
  lift (exitTime r R T) to ℝ using hne with t ht
  have htmem := finite_exit_mem_interval r R T t ht.symm
  have hhit := radius_le_at_finite_exit r R T t ht.symm (hr t htmem)
  exact not_lt_of_ge hhit (hbound t htmem le_rfl)

/-- A closed AC branch implies right continuity before its terminal jump. -/
theorem right_continuous_of_closedBranch_ac (r : ℝ → ℝ) (s e pre t : ℝ)
    (hst : s ≤ t) (hte : t < e)
    (hbranch : AbsolutelyContinuousOnInterval (closedBranch r e pre) s e) :
    ContinuousWithinAt r (Ici t) t := by
  have hse : s ≤ e := le_trans hst hte.le
  have hc : ContinuousWithinAt (closedBranch r e pre) (Icc s e) t := by
    have hm : t ∈ uIcc s e := by
      rw [uIcc_of_le hse]
      exact ⟨hst, hte.le⟩
    simpa only [uIcc_of_le hse] using hbranch.continuousOn.continuousWithinAt hm
  have hmem : Icc s e ∈ 𝓝[≥] t := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hte)]
      with u htu hue
    exact ⟨le_trans hst htu, hue.le⟩
  have hright := hc.mono_of_mem_nhdsWithin hmem
  have heq : r =ᶠ[𝓝[≥] t] closedBranch r e pre := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hte)] with u hue
    exact (closedBranch_of_ne r e pre u (ne_of_lt hue)).symm
  exact hright.congr_of_eventuallyEq heq
    (closedBranch_of_ne r e pre t (ne_of_lt hte)).symm

/-- Full finite branch regularity supplies the one-sided continuity needed for exit attainment. -/
theorem finite_schedule_right_continuous
    (tau pre : ℕ → ℝ) (r : ℝ → ℝ) (L : ℕ) (T t : ℝ)
    (htime : ∀ k < L, tau k ≤ tau (k + 1))
    (hbranch : ∀ k < L, AbsolutelyContinuousOnInterval
      (closedBranch r (tau (k + 1)) (pre k)) (tau k) (tau (k + 1)))
    (hfinal : AbsolutelyContinuousOnInterval r (tau L) T)
    (ht0 : tau 0 ≤ t) (htT : t ≤ T) :
    ContinuousWithinAt r (Icc t T) t := by
  have hnt := time_jumpCount_le tau L t htime ht0
  by_cases hn : jumpCount tau L t < L
  · exact (right_continuous_of_closedBranch_ac r _ _ _ t hnt
      (lt_next_jump tau L t htime hn) (hbranch _ hn)).mono
      (fun _ hu => hu.1)
  · have hnL : jumpCount tau L t = L := by
      have := jumpCount_le tau L t
      omega
    rw [hnL] at hnt
    have hc : ContinuousWithinAt r (Icc (tau L) T) t := by
      have hm : t ∈ uIcc (tau L) T := by
        rw [uIcc_of_le (le_trans hnt htT)]
        exact ⟨hnt, htT⟩
      simpa only [uIcc_of_le (le_trans hnt htT)] using
        hfinal.continuousOn.continuousWithinAt hm
    exact hc.mono (Icc_subset_Icc_left hnt)

/-- A strict stopped estimate on a finite AC schedule is a bound on the whole horizon. -/
theorem lt_radius_on_horizon_of_finite_schedule
    (tau pre : ℕ → ℝ) (r : ℝ → ℝ) (L : ℕ) (R T : ℝ)
    (htau0 : tau 0 = 0) (htime : ∀ k < L, tau k ≤ tau (k + 1))
    (hbranch : ∀ k < L, AbsolutelyContinuousOnInterval
      (closedBranch r (tau (k + 1)) (pre k)) (tau k) (tau (k + 1)))
    (hfinal : AbsolutelyContinuousOnInterval r (tau L) T)
    (hbound : ∀ t ∈ Icc 0 T,
      (t : WithTop ℝ) ≤ exitTime r R T → r t < R) :
    ∀ t ∈ Icc 0 T, r t < R := by
  apply (exitTime_eq_top_iff r R T).mp
  apply exitTime_eq_top_of_strict_candidate_bound r R T _ hbound
  intro t ht
  exact finite_schedule_right_continuous tau pre r L T t htime hbranch hfinal
    (by simpa only [htau0] using ht.1) ht.2

/-- A strict stopped envelope extends its bound to every time in the horizon. -/
theorem bound_on_horizon_of_strict_stopped_envelope (r F : ℝ → ℝ) (R T : ℝ)
    (hr : ∀ t ∈ Icc 0 T, ContinuousWithinAt r (Icc t T) t)
    (hbound : ∀ t ∈ Icc 0 T,
      (t : WithTop ℝ) ≤ exitTime r R T → r t ≤ F t)
    (hsmall : ∀ t ∈ Icc 0 T, F t < R) :
    (exitTime r R T = ⊤) ∧ ∀ t ∈ Icc 0 T, r t ≤ F t := by
  have htop := exitTime_eq_top_of_strict_candidate_bound r R T hr
    (fun t ht hstop => lt_of_le_of_lt (hbound t ht hstop) (hsmall t ht))
  refine ⟨htop, ?_⟩
  intro t ht
  apply hbound t ht
  rw [htop]
  exact le_top

/-- The zero-forcing bootstrap uses a positive auxiliary radius, never a zero exit radius. -/
theorem eq_zero_on_horizon_of_nonpos_stopped_bound (r : ℝ → ℝ) (R T : ℝ)
    (hR : 0 < R)
    (hr : ∀ t ∈ Icc 0 T, ContinuousWithinAt r (Icc t T) t)
    (hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ r t)
    (hbound : ∀ t ∈ Icc 0 T,
      (t : WithTop ℝ) ≤ exitTime r R T → r t ≤ 0) :
    ∀ t ∈ Icc 0 T, r t = 0 := by
  have hglobal := bound_on_horizon_of_strict_stopped_envelope r (fun _ => 0) R T
    hr hbound (fun _ _ => hR)
  intro t ht
  exact le_antisymm (hglobal.2 t ht) (hnonneg t ht)

end PaperFormalization.Manuscript
