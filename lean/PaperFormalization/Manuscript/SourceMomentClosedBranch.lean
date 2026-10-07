import PaperFormalization.Manuscript.SourceMomentLeftTrace
import Mathlib.Topology.Order.ExtendFrom
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! # Closed source branches with their actual one-sided endpoint values

The right value at the initial endpoint is retained; only the terminal value
is replaced by its actual left trace. The supplied two one-sided limits and
the interior Lipschitz estimate determine the same estimate on the closed
branch. No complete target or differentiability of an endpoint update is used.
-/

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace PaperFormalization.Manuscript

/-- Interior Lipschitz regularity persists when the terminal value is replaced
by the actual left limit and the initial value is the actual right limit. -/
theorem lipschitzOnWith_update_of_oneSidedTraces
    {E : Type*} [MetricSpace E] (a b : ℝ) (hab : a < b)
    (B : ℝ≥0) (f : ℝ → E) (pre : E)
    (hB : LipschitzOnWith B f (Ioo a b))
    (ha : Tendsto f (𝓝[>] a) (𝓝 (f a)))
    (hb : Tendsto f (𝓝[<] b) (𝓝 pre)) :
    LipschitzOnWith B (Function.update f b pre) (Icc a b) := by
  classical
  have heq : EqOn (Function.update f b pre) (extendFrom (Ioo a b) f) (Icc a b) := by
    intro t ht
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc ht with (rfl | rfl | ht')
    · rw [Function.update_of_ne hab.ne, eq_lim_at_left_extendFrom_Ioo hab ha]
    · rw [Function.update_self, eq_lim_at_right_extendFrom_Ioo hab hb]
    · rw [Function.update_of_ne ht'.2.ne, extendFrom_extends hB.continuousOn t ht']
  have hc : ContinuousOn (Function.update f b pre) (Icc a b) :=
    (continuousOn_Icc_extendFrom_Ioo hB.continuousOn ha hb).congr heq
  have hB' : LipschitzOnWith B (Function.update f b pre) (Ioo a b) := by
    intro s hs t ht
    simpa only [Function.update_of_ne hs.2.ne, Function.update_of_ne ht.2.ne] using hB hs ht
  have hc' : ContinuousOn (Function.update f b pre) (closure (Ioo a b)) := by
    simpa only [closure_Ioo hab.ne] using hc
  simpa only [closure_Ioo hab.ne] using hB'.closure hc'

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
  [NormedAddCommGroup E] [BorelSpace E]

/-- The original value at the initial endpoint obtains measurability and the
same source moment bounds from interior laws and its actual right limit. -/
theorem sourceMomentClass_map_rightValue
    (μ : Measure Ω) [IsProbabilityMeasure μ] (alpha K a b : ℝ) (hab : a < b)
    (Z : ℝ → Ω → E)
    (hZ : ∀ t ∈ Ioo a b, AEStronglyMeasurable (Z t) μ)
    (hclass : ∀ t ∈ Ioo a b, μ.map (Z t) ∈ sourceMomentClass alpha K)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun t => Z t ω) (𝓝[>] a) (𝓝 (Z a ω))) :
    AEStronglyMeasurable (Z a) μ ∧ μ.map (Z a) ∈ sourceMomentClass alpha K := by
  classical
  let Zbranch : ℝ → Ω → E := fun t => if t ∈ Ioo a b then Z t else 0
  have hbranch : ∀ t, AEStronglyMeasurable (Zbranch t) μ := by
    intro t
    by_cases ht : t ∈ Ioo a b
    · simpa only [Zbranch, if_pos ht] using hZ t ht
    · simp only [Zbranch, ht, ↓reduceIte]
      exact aestronglyMeasurable_const
  have hclass' : ∀ᶠ t in 𝓝[>] a,
      μ.map (Zbranch t) ∈ sourceMomentClass alpha K := by
    filter_upwards [Ioo_mem_nhdsGT hab] with t ht
    simpa only [Zbranch, if_pos ht] using hclass t ht
  have hlim' : ∀ᵐ ω ∂μ,
      Tendsto (fun t => Zbranch t ω) (𝓝[>] a) (𝓝 (Z a ω)) := by
    filter_upwards [hlim] with ω hω
    apply hω.congr'
    filter_upwards [Ioo_mem_nhdsGT hab] with t ht
    simp only [Zbranch, if_pos ht]
  exact sourceMomentClass_map_of_ae_tendsto (𝓝[>] a) μ alpha K Zbranch (Z a)
    hbranch hclass' hlim'

/-- Replacing the terminal post-jump value by its supplied actual left trace
produces one closed reference branch with the same AE Lipschitz constant and
unchanged source moment class at every time, including both endpoints. -/
theorem sourceMoment_closedBranch_regularity
    (μ : Measure Ω) [IsProbabilityMeasure μ] (alpha K a b : ℝ) (hab : a < b)
    (B : ℝ≥0) (Z : ℝ → Ω → E) (preZ : Ω → E)
    (hZ : ∀ t ∈ Ioo a b, AEStronglyMeasurable (Z t) μ)
    (hclass : ∀ t ∈ Ioo a b, μ.map (Z t) ∈ sourceMomentClass alpha K)
    (hB : ∀ᵐ ω ∂μ, LipschitzOnWith B (fun t => Z t ω) (Ioo a b))
    (ha : ∀ᵐ ω ∂μ, Tendsto (fun t => Z t ω) (𝓝[>] a) (𝓝 (Z a ω)))
    (hb : ∀ᵐ ω ∂μ, Tendsto (fun t => Z t ω) (𝓝[<] b) (𝓝 (preZ ω))) :
    (∀ᵐ ω ∂μ, LipschitzOnWith B
      (fun t => Function.update Z b preZ t ω) (Icc a b)) ∧
    (∀ t ∈ Icc a b, AEStronglyMeasurable (Function.update Z b preZ t) μ ∧
      μ.map (Function.update Z b preZ t) ∈ sourceMomentClass alpha K) := by
  classical
  have hright := sourceMomentClass_map_rightValue μ alpha K a b hab Z hZ hclass ha
  have hleft := sourceMomentClass_map_leftTrace μ alpha K a b hab Z preZ hZ hclass hb
  constructor
  · filter_upwards [hB, ha, hb] with ω hBω haω hbω
    have heq : (fun t => Function.update Z b preZ t ω) =
        Function.update (fun t => Z t ω) b (preZ ω) := by
      funext t
      by_cases ht : t = b
      · subst t
        simp only [Function.update_self]
      · simp only [Function.update_of_ne ht]
    rw [heq]
    exact lipschitzOnWith_update_of_oneSidedTraces a b hab B (fun t => Z t ω)
      (preZ ω) hBω haω hbω
  · intro t ht
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc ht with (rfl | rfl | ht')
    · simpa only [Function.update_of_ne hab.ne] using hright
    · simpa only [Function.update_self] using hleft
    · simpa only [Function.update_of_ne ht'.2.ne] using ⟨hZ t ht', hclass t ht'⟩

end PaperFormalization.Manuscript
