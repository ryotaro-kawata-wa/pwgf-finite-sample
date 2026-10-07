import PaperFormalization.Manuscript.SourceMomentClassLimit
import Mathlib.Topology.Order.LeftRightNhds

/-! # The original source moment class at an actual left trace

Only times in the open branch `(a,b)` need measurable random variables and
source moment bounds. The supplied pre-jump value is assumed to be the actual
almost sure left limit. Its strong measurability and all-real-order moment
bounds follow under the unchanged probability measure, with the same K.
No assertion of existence of a left limit is made here.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace PaperFormalization.Manuscript

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
  [NormedAddCommGroup E] [BorelSpace E]

/-- Interior source laws pass to the actual pre-jump trace, without assumptions
on the post-jump value or on the path outside this one open branch. -/
theorem sourceMomentClass_map_leftTrace
    (μ : Measure Ω) [IsProbabilityMeasure μ] (alpha K a b : ℝ) (hab : a < b)
    (Z : ℝ → Ω → E) (preZ : Ω → E)
    (hZ : ∀ t ∈ Ioo a b, AEStronglyMeasurable (Z t) μ)
    (hclass : ∀ t ∈ Ioo a b, μ.map (Z t) ∈ sourceMomentClass alpha K)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun t => Z t ω) (𝓝[<] b) (𝓝 (preZ ω))) :
    AEStronglyMeasurable preZ μ ∧ μ.map preZ ∈ sourceMomentClass alpha K := by
  classical
  let Zbranch : ℝ → Ω → E := fun t => if t ∈ Ioo a b then Z t else 0
  have hbranch : ∀ t, AEStronglyMeasurable (Zbranch t) μ := by
    intro t
    by_cases ht : t ∈ Ioo a b
    · simpa only [Zbranch, if_pos ht] using hZ t ht
    · simp only [Zbranch, ht, ↓reduceIte]
      exact aestronglyMeasurable_const
  have hclass' : ∀ᶠ t in 𝓝[<] b,
      μ.map (Zbranch t) ∈ sourceMomentClass alpha K := by
    filter_upwards [Ioo_mem_nhdsLT hab] with t ht
    simpa only [Zbranch, if_pos ht] using hclass t ht
  have hlim' : ∀ᵐ ω ∂μ,
      Tendsto (fun t => Zbranch t ω) (𝓝[<] b) (𝓝 (preZ ω)) := by
    filter_upwards [hlim] with ω hω
    apply hω.congr'
    filter_upwards [Ioo_mem_nhdsLT hab] with t ht
    simp only [Zbranch, if_pos ht]
  exact sourceMomentClass_map_of_ae_tendsto (𝓝[<] b) μ alpha K Zbranch preZ
    hbranch hclass' hlim'

end PaperFormalization.Manuscript
