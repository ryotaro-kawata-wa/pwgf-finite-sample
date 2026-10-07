import PaperFormalization.Manuscript.SourceMomentClass
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! # Exact source moment class under almost sure limits

All random variables use one unchanged probability measure. Fatou's Lq bound
preserves every real q>=1 with the same K, before any real-integral conversion.
Limit strong measurability and identity measurability under each pushforward
are derived from AE strong measurability; the state space need not be separable
or complete. This unit does not infer a trace limit from path assumptions.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace PaperFormalization.Manuscript

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
  [NormedAddCommGroup E] [BorelSpace E]

/-- An AE limit under one unchanged probability law remains in the original
all-real-order class with exactly the same alpha and K. Class membership may
hold eventually along any nontrivial countably generated filter. -/
theorem sourceMomentClass_map_of_ae_tendsto
    {I : Type*} (l : Filter I) [NeBot l] [IsCountablyGenerated l]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (alpha K : ℝ)
    (Z : I → Ω → E) (Zlim : Ω → E)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) μ)
    (hclass : ∀ᶠ i in l, μ.map (Z i) ∈ sourceMomentClass alpha K)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun i => Z i ω) l (𝓝 (Zlim ω))) :
    AEStronglyMeasurable Zlim μ ∧ μ.map Zlim ∈ sourceMomentClass alpha K := by
  have hm : AEStronglyMeasurable Zlim μ := aestronglyMeasurable_of_tendsto_ae l hZ hlim
  refine ⟨hm, Measure.isProbabilityMeasure_map hm.aemeasurable, ?_⟩
  intro q hq
  rw [eLpNorm_map_measure hm.aestronglyMeasurable_id_map hm.aemeasurable]
  change eLpNorm Zlim (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (K * q ^ (1 / alpha))
  apply Lp.eLpNorm_le_of_ae_tendsto (hf := hZ) (h_tendsto := hlim)
  filter_upwards [hclass] with i hi
  have hb := hi.2 q hq
  rw [eLpNorm_map_measure (hZ i).aestronglyMeasurable_id_map (hZ i).aemeasurable] at hb
  exact hb

/-- The sequential form used for prescribed left traces: actual source laws
at every approximating time retain the identical all-real-q bound at the AE
pointwise limit. Limit measurability is a conclusion, not an extra premise. -/
theorem sourceMomentClass_map_of_ae_seq_tendsto
    (μ : Measure Ω) [IsProbabilityMeasure μ] (alpha K : ℝ)
    (Z : ℕ → Ω → E) (Zlim : Ω → E)
    (hZ : ∀ n, AEStronglyMeasurable (Z n) μ)
    (hclass : ∀ n, μ.map (Z n) ∈ sourceMomentClass alpha K)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => Z n ω) atTop (𝓝 (Zlim ω))) :
    AEStronglyMeasurable Zlim μ ∧ μ.map Zlim ∈ sourceMomentClass alpha K :=
  sourceMomentClass_map_of_ae_tendsto atTop μ alpha K Z Zlim hZ
    (Eventually.of_forall hclass) hlim

end PaperFormalization.Manuscript
