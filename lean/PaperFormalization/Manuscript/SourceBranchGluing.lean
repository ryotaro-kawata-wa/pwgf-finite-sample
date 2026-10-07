import PaperFormalization.Piecewise.SchedulePrefix
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Tactic

/-! # Gluing actual closed branches with the prescribed post-jump convention

M13p verified unit (see CODEX_HANDOFF_M13P.md). The finite schedule chooses the RIGHT branch at
an exact jump. Left traces are the previous closed branch's endpoint. They are
not equated. Local identities, regularity and derivatives are consequences of
this definition, not additional model compatibility assumptions.
-/
open Filter Set
open scoped Topology NNReal
namespace PaperFormalization.Manuscript
open Piecewise

noncomputable def sourceGlue {E : Type*} (tau : ℕ -> ℝ) (J : ℕ)
    (branch : ℕ -> ℝ -> E) (t : ℝ) : E := branch (jumpCount tau J t) t

/-- The selected branch at a right/post observation is exactly k. -/
theorem source_jumpCount_on_branch (tau : ℕ -> ℝ) (J k : ℕ)
    (htime : ∀ n < J, tau n < tau (n+1)) (hk : k ≤ J)
    (t : ℝ) (ht : tau k ≤ t) (hn : k < J -> t < tau (k+1)) :
    jumpCount tau J t = k := by
  have hw : ∀ n < J, tau n ≤ tau (n+1) := fun n h => (htime n h).le
  apply Nat.le_antisymm
  · by_contra h
    have hm := (lt_jumpCount_iff tau J t hw k).mp (Nat.lt_of_not_ge h)
    exact (not_le_of_gt (hn hm.1)) hm.2
  · by_contra h
    have hc : jumpCount tau J t < k := Nat.lt_of_not_ge h
    have hct := lt_next_jump tau J t hw (hc.trans_le hk)
    have hmono := time_mono_prefix tau J hw (jumpCount tau J t+1) k
      (Nat.succ_le_of_lt hc) hk
    exact (not_lt_of_ge (hmono.trans ht)) hct

theorem sourceGlue_on_branch {E : Type*} (tau : ℕ -> ℝ) (J : ℕ)
    (branch : ℕ -> ℝ -> E) (htime : ∀ n < J, tau n < tau (n+1))
    (k : ℕ) (hk : k ≤ J) (t : ℝ) (ht : tau k ≤ t)
    (hn : k < J -> t < tau (k+1)) : sourceGlue tau J branch t = branch k t := by
  unfold sourceGlue
  rw [source_jumpCount_on_branch tau J k htime hk t ht hn]

theorem sourceGlue_at_jump {E : Type*} (tau : ℕ -> ℝ) (J : ℕ)
    (branch : ℕ -> ℝ -> E) (htime : ∀ n < J, tau n < tau (n+1))
    (k : ℕ) (hk : k ≤ J) : sourceGlue tau J branch (tau k) = branch k (tau k) := by
  unfold sourceGlue
  rw [jumpCount_at_endpoint tau J k htime hk]

theorem sourceGlue_eventuallyEq {E : Type*} (tau : ℕ -> ℝ) (J : ℕ)
    (branch : ℕ -> ℝ -> E) (htime : ∀ n < J, tau n < tau (n+1))
    (k : ℕ) (hk : k ≤ J) (T t : ℝ)
    (ht : t ∈ Ioo (tau k) (if k < J then tau (k+1) else T)) :
    sourceGlue tau J branch =ᶠ[𝓝 t] branch k := by
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  apply sourceGlue_on_branch tau J branch htime k hk s hs.1.le
  intro hkj
  simpa only [if_pos hkj] using hs.2

/-- The ordinary derivative is transported only at an interior time. -/
theorem sourceGlue_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (tau : ℕ -> ℝ) (J : ℕ) (branch : ℕ -> ℝ -> E)
    (htime : ∀ n < J, tau n < tau (n+1)) (k : ℕ) (hk : k ≤ J)
    (T t : ℝ) (ht : t ∈ Ioo (tau k) (if k < J then tau (k+1) else T))
    (v : E) (hv : HasDerivAt (branch k) v t) :
    HasDerivAt (sourceGlue tau J branch) v t :=
  hv.congr_of_eventuallyEq (sourceGlue_eventuallyEq tau J branch htime k hk T t ht)

/-- Restricting the glued path to the right part of a branch preserves its
Lipschitz constant. The final branch can have length zero. -/
theorem sourceGlue_lipschitzOn {E : Type*} [PseudoMetricSpace E]
    (tau : ℕ -> ℝ) (J : ℕ) (branch : ℕ -> ℝ -> E)
    (htime : ∀ n < J, tau n < tau (n+1)) (k : ℕ) (hk : k ≤ J)
    (s : Set ℝ) (hstart : ∀ t ∈ s, tau k ≤ t)
    (hend : ∀ t ∈ s, k < J -> t < tau (k+1))
    (B : ℝ≥0) (hB : LipschitzOnWith B (branch k) s) :
    LipschitzOnWith B (sourceGlue tau J branch) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  rw [sourceGlue_on_branch tau J branch htime k hk u (hstart u hu) (hend u hu),
    sourceGlue_on_branch tau J branch htime k hk v (hstart v hv) (hend v hv)]
  exact hB.dist_le_mul u hu v hv

/-- Right continuity and the true left trace follow from closed-branch
continuity; the actual value at the jump remains the next branch's start. -/
theorem sourceGlue_traces {E : Type*} [TopologicalSpace E]
    (tau : ℕ -> ℝ) (J : ℕ) (branch : ℕ -> ℝ -> E)
    (htime : ∀ n < J, tau n < tau (n+1)) (k : ℕ) (hk : k < J)
    (hcont : ContinuousOn (branch k) (Icc (tau k) (tau (k+1)))) :
    Tendsto (sourceGlue tau J branch) (𝓝[>] (tau k))
      (𝓝 (sourceGlue tau J branch (tau k))) ∧
    Tendsto (sourceGlue tau J branch) (𝓝[<] (tau (k+1)))
      (𝓝 (branch k (tau (k+1)))) := by
  have hab := htime k hk
  have hright : Tendsto (fun t : ℝ => t) (𝓝[>] (tau k))
      (𝓝[Icc (tau k) (tau (k+1))] (tau k)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨nhdsWithin_le_nhds, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT hab] with t ht
    exact ⟨ht.1.le, ht.2.le⟩
  have hleft : Tendsto (fun t : ℝ => t) (𝓝[<] (tau (k+1)))
      (𝓝[Icc (tau k) (tau (k+1))] (tau (k+1))) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨nhdsWithin_le_nhds, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT hab] with t ht
    exact ⟨ht.1.le, ht.2.le⟩
  constructor
  · rw [sourceGlue_at_jump tau J branch htime k hk.le]
    apply (Filter.Tendsto.comp (hcont (tau k) ⟨le_rfl, hab.le⟩) hright).congr'
    filter_upwards [Ioo_mem_nhdsGT hab] with t ht
    exact (sourceGlue_on_branch tau J branch htime k hk.le t ht.1.le (fun _ => ht.2)).symm
  · apply (Filter.Tendsto.comp (hcont (tau (k+1)) ⟨hab.le, le_rfl⟩) hleft).congr'
    filter_upwards [Ioo_mem_nhdsLT hab] with t ht
    exact (sourceGlue_on_branch tau J branch htime k hk.le t ht.1.le (fun _ => ht.2)).symm

end PaperFormalization.Manuscript
