import PaperFormalization.Continuous.Duhamel

/-! # Closed AC branches and their pre-jump traces

A right-continuous path's value at a jump is its post-jump value. Replacing
only that endpoint with a supplied pre-jump value yields the closed branch.
If this branch is AC, the supplied endpoint is proved to be the path's left
limit, and the interior derivatives agree. This precisely expresses the
source's absolute continuity up to a branch endpoint without identifying
pre-jump and post-jump values.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace PaperFormalization.Manuscript

/-- Keep the path everywhere except at the terminal point, where its pre-jump trace is used. -/
noncomputable def closedBranch (r : ℝ → ℝ) (t pre : ℝ) : ℝ → ℝ :=
  Function.update r t pre

@[simp] theorem closedBranch_terminal (r : ℝ → ℝ) (t pre : ℝ) :
    closedBranch r t pre t = pre := by simp [closedBranch]

/-- The branch extension changes no other path value. -/
theorem closedBranch_of_ne (r : ℝ → ℝ) (t pre u : ℝ) (hu : u ≠ t) :
    closedBranch r t pre u = r u := by simp [closedBranch, hu]

/-- In particular, the branch extension agrees with the path strictly before its endpoint. -/
theorem closedBranch_eqOn_Iio (r : ℝ → ℝ) (t pre : ℝ) :
    EqOn (closedBranch r t pre) r (Iio t) := by
  intro u hu
  exact closedBranch_of_ne r t pre u (ne_of_lt hu)

/-- The interior derivative agrees with that of the original path. -/
theorem closedBranch_deriv_eqOn_Iio (r : ℝ → ℝ) (t pre : ℝ) :
    EqOn (deriv (closedBranch r t pre)) (deriv r) (Iio t) :=
  (closedBranch_eqOn_Iio r t pre).deriv isOpen_Iio

/-- An AC closed branch proves that its terminal value is the actual left limit of the path. -/
theorem tendsto_left_of_closedBranch_ac (r : ℝ → ℝ) (s t pre : ℝ) (hst : s < t)
    (hr : AbsolutelyContinuousOnInterval (closedBranch r t pre) s t) :
    Tendsto r (𝓝[<] t) (𝓝 pre) := by
  have hc : ContinuousWithinAt (closedBranch r t pre) (Icc s t) t := by
    simpa only [uIcc_of_le hst.le] using
      hr.continuousOn.continuousWithinAt (right_mem_uIcc : t ∈ uIcc s t)
  have hmem : Icc s t ∈ 𝓝[<] t := by
    have hl : Ioi s ∈ 𝓝[<] t := nhdsWithin_le_nhds (Ioi_mem_nhds hst)
    have hu : Iio t ∈ 𝓝[<] t := self_mem_nhdsWithin
    filter_upwards [hl, hu] with u hsu hut
    exact ⟨hsu.le, hut.le⟩
  have hle : 𝓝[<] t ≤ 𝓝[Icc s t] t :=
    le_inf nhdsWithin_le_nhds (Filter.le_principal_iff.mpr hmem)
  have hq : Tendsto (closedBranch r t pre) (𝓝[<] t) (𝓝 pre) := by
    simpa only [closedBranch_terminal] using (Filter.Tendsto.mono_left hc hle)
  have heq : closedBranch r t pre =ᶠ[𝓝[<] t] r := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact closedBranch_of_ne r t pre u (ne_of_lt hu)
  exact Filter.Tendsto.congr' heq hq

end PaperFormalization.Manuscript
