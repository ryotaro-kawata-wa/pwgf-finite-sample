import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-! # Actual equally spaced closed-branch grids

Each branch keeps its own endpoint labels. Zero-length branches are included;
no equality of the pre-jump and post-jump endpoint values is asserted.
-/
open Set MeasureTheory
open scoped BigOperators NNReal
namespace PaperFormalization.Manuscript

/-- The literal N-subdivision grid on a closed branch, with N+1 labelled nodes. -/
noncomputable def closedBranchGrid (a b : ℝ) (N : ℕ) (i : Fin (N+1)) : ℝ :=
  a + (b-a) * (i : ℝ) / N

/-- Every actual grid node lies on its own closed branch. -/
theorem closedBranchGrid_mem (a b : ℝ) (hab : a ≤ b) {N : ℕ} (hN : 0 < N)
    (i : Fin (N+1)) : closedBranchGrid a b N i ∈ Icc a b := by
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg i.val
  have hiN : (i : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
  have hle : (b-a) * (i : ℝ) / N ≤ b-a := (div_le_iff₀ hN0).mpr
    (mul_le_mul_of_nonneg_left hiN (sub_nonneg.mpr hab))
  have hge : 0 ≤ (b-a) * (i : ℝ) / N := by positivity
  exact ⟨by dsimp [closedBranchGrid]; linarith, by dsimp [closedBranchGrid]; linarith⟩

/-- Every branch time is within one mesh width of an actual labelled node,
including both endpoints and degenerate branches. -/
theorem exists_closedBranchGrid_near (a b : ℝ) (hab : a ≤ b) {N : ℕ} (hN : 0 < N)
    (t : ℝ) (ht : t ∈ Icc a b) :
    ∃ i : Fin (N+1), dist t (closedBranchGrid a b N i) ≤ (b-a)/N := by
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  by_cases heq : a = b
  · subst b
    have ht0 : t = a := le_antisymm ht.2 ht.1
    refine ⟨⟨0, by omega⟩, ?_⟩
    simp [closedBranchGrid, ht0]
  have hab' : 0 < b-a := sub_pos.mpr (lt_of_le_of_ne hab heq)
  let d := (b-a)/(N : ℝ)
  have hd : 0 < d := div_pos hab' hN0
  let z := (t-a)/d
  have hz0 : 0 ≤ z := div_nonneg (sub_nonneg.mpr ht.1) hd.le
  have hNd : (N : ℝ) * d = b-a := by dsimp [d]; field_simp
  have hzN : z ≤ N := (div_le_iff₀ hd).mpr (by nlinarith [ht.2])
  let k : Fin (N+1) := ⟨⌊z⌋₊, Nat.lt_succ_of_le (Nat.floor_le_of_le hzN)⟩
  have hk0 : (k : ℝ) ≤ z := Nat.floor_le hz0
  have hk1 : z < (k : ℝ) + 1 := Nat.lt_floor_add_one z
  have hz : d * z = t-a := by dsimp [z]; field_simp
  have hgrid : closedBranchGrid a b N k = a + d * (k : ℝ) := by dsimp [closedBranchGrid,d]; ring
  have hlo : 0 ≤ t - (a+d*(k : ℝ)) := by nlinarith [mul_le_mul_of_nonneg_left hk0 hd.le]
  have hup : t - (a+d*(k : ℝ)) ≤ d := by nlinarith [mul_lt_mul_of_pos_left hk1 hd]
  refine ⟨k, ?_⟩
  rw [hgrid, Real.dist_eq, abs_of_nonneg hlo]
  exact hup

/-- Actual grid-node bounds extend along a Lipschitz closed branch with the
exact single-mesh error. -/
theorem closedBranchGrid_lipschitz_bound (a b : ℝ) (hab : a ≤ b) {N : ℕ} (hN : 0 < N)
    (f : ℝ → ℝ) (K : ℝ≥0) (hf : LipschitzOnWith K f (Icc a b))
    (r : ℝ) (hgrid : ∀ i, f (closedBranchGrid a b N i) ≤ r)
    (t : ℝ) (ht : t ∈ Icc a b) : f t ≤ r + (K : ℝ) * ((b-a)/N) := by
  obtain ⟨i, hi⟩ := exists_closedBranchGrid_near a b hab hN t ht
  have h := (hf.dist_le_mul t ht (closedBranchGrid a b N i)
    (closedBranchGrid_mem a b hab hN i)).trans (mul_le_mul_of_nonneg_left hi K.coe_nonneg)
  rw [Real.dist_eq] at h
  have hh := (abs_le.mp h).2
  linarith [hgrid i]

/-- A continuum-time branch failure on the specified good paths is contained
in a finite union of actual node failures; no continuum measurability premise
is needed for this outer-measure upper bound. -/
theorem measure_closedBranch_failure_le_grid {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Good : Set Ω) (a b : ℝ) (hab : a ≤ b) {N : ℕ} (hN : 0 < N)
    (F : Ω → ℝ → ℝ) (K : ℝ≥0)
    (hF : ∀ ω ∈ Good, LipschitzOnWith K (F ω) (Icc a b)) (r : ℝ) :
    μ {ω | ω ∈ Good ∧ ∃ t ∈ Icc a b, r + (K : ℝ) * ((b-a)/N) < F ω t} ≤
      ∑ i : Fin (N+1), μ {ω | r < F ω (closedBranchGrid a b N i)} := by
  apply (measure_mono (show {ω | ω ∈ Good ∧ ∃ t ∈ Icc a b,
    r + (K : ℝ) * ((b-a)/N) < F ω t} ⊆
    ⋃ i : Fin (N+1), {ω | r < F ω (closedBranchGrid a b N i)} from ?_)).trans
      (measure_iUnion_fintype_le μ _)
  intro ω hω
  by_contra hn
  have hg : ∀ i, F ω (closedBranchGrid a b N i) ≤ r := by
    intro i
    exact le_of_not_gt (fun hi => hn (mem_iUnion.mpr ⟨i,hi⟩))
  obtain ⟨t, ht, hbad⟩ := hω.2
  exact (not_lt_of_ge (closedBranchGrid_lipschitz_bound a b hab hN (F ω) K
    (hF ω hω.1) r hg t ht)) hbad
end PaperFormalization.Manuscript
