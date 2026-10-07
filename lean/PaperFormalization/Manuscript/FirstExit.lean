import Mathlib.Probability.Process.HittingTime
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # A pathwise first-exit time, with infinity for an empty exit set

No filtration or adaptedness is used. The time coordinate in the target set
restricts exits to [0, T], while mathlib's real-time hittingAfter supplies the
infimum and the WithTop infinity convention. These results concern times
strictly before the infimum and open branches ending at or before it; they
do not claim attainment or identify pre/post-jump traces.
-/

open MeasureTheory Set

namespace PaperFormalization.Manuscript

/-- Infimum of {t in [0, T] | R <= r t}; equal to top when this set is empty. -/
noncomputable def exitTime (r : ℝ → ℝ) (R T : ℝ) : WithTop ℝ :=
  hittingAfter (fun t (_ : Unit) => (t, r t))
    {p : ℝ × ℝ | p.1 ≤ T ∧ R ≤ p.2} 0 ()

/-- The pathwise exit infimum is nonnegative, including the infinite case. -/
theorem exitTime_nonneg (r : ℝ → ℝ) (R T : ℝ) : 0 ≤ exitTime r R T := by
  exact le_hittingAfter ()

/-- Infinity is exactly the absence of a radius exit throughout the finite horizon. -/
theorem exitTime_eq_top_iff (r : ℝ → ℝ) (R T : ℝ) :
    exitTime r R T = ⊤ ↔ ∀ t ∈ Icc 0 T, r t < R := by
  unfold exitTime
  rw [hittingAfter_eq_top_iff]
  constructor
  · intro h t ht
    exact lt_of_not_ge (fun hr => h t ht.1 ⟨ht.2, hr⟩)
  · intro h t ht0 htmem
    exact (not_le_of_gt (h t ⟨ht0, htmem.1⟩)) htmem.2

/-- A time that reaches the radius is at or after the exit infimum. -/
theorem exitTime_le_of_radius_le (r : ℝ → ℝ) (R T t : ℝ)
    (ht : t ∈ Icc 0 T) (hr : R ≤ r t) : exitTime r R T ≤ (t : WithTop ℝ) := by
  exact hittingAfter_le_of_mem ht.1 ⟨ht.2, hr⟩

/-- Every time strictly before the exit infimum lies strictly inside the radius. -/
theorem lt_radius_of_lt_exitTime (r : ℝ → ℝ) (R T t : ℝ)
    (ht : t ∈ Icc 0 T) (hbefore : (t : WithTop ℝ) < exitTime r R T) : r t < R := by
  have hnot := notMem_of_lt_hittingAfter
    (u := fun u (_ : Unit) => (u, r u))
    (s := {p : ℝ × ℝ | p.1 ≤ T ∧ R ≤ p.2}) (n := (0 : ℝ)) (ω := ()) hbefore ht.1
  exact lt_of_not_ge (fun hr => hnot ⟨ht.2, hr⟩)

/-- The radius bound holds throughout an open branch whose endpoint can equal the exit. -/
theorem radius_lt_on_open_before_exit (r : ℝ → ℝ) (R T s t : ℝ)
    (hs : 0 ≤ s) (htT : t ≤ T) (htExit : (t : WithTop ℝ) ≤ exitTime r R T) :
    ∀ u ∈ Ioo s t, r u < R := by
  intro u hu
  have hut : (u : WithTop ℝ) < (t : WithTop ℝ) := by exact_mod_cast hu.2
  exact lt_radius_of_lt_exitTime r R T u
    ⟨le_trans hs hu.1.le, le_trans hu.2.le htT⟩ (lt_of_lt_of_le hut htExit)

/-- The a.e. non-strict radius bound needed by quadratic-drift linearization. -/
theorem ae_radius_le_before_exit (r : ℝ → ℝ) (R T s t : ℝ)
    (hs : 0 ≤ s) (htT : t ≤ T) (htExit : (t : WithTop ℝ) ≤ exitTime r R T) :
    ∀ᵐ u ∂volume.restrict (Ioo s t), r u ≤ R := by
  apply ae_restrict_of_forall_mem measurableSet_Ioo
  intro u hu
  exact (radius_lt_on_open_before_exit r R T s t hs htT htExit u hu).le

end PaperFormalization.Manuscript
