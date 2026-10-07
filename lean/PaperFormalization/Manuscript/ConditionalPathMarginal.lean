import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.Prod

/-! # Actual marginals of one conditional population path law

The path kernel stays fixed; only the jointly measurable evaluation map
changes with a selected time or branch. No new conditional law is assumed.
-/
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
namespace PaperFormalization.Manuscript
variable {G Ω E : Type*} [MeasurableSpace G] [MeasurableSpace Ω] [MeasurableSpace E]

/-- The actual history-dependent pushforward of a fixed population kernel. -/
noncomputable def conditionalPathMarginal (μ : Kernel G Ω) (Y : G → Ω → E) : Kernel G E :=
  ((Kernel.id : Kernel G G) ×ₖ μ).map (fun z => Y z.1 z.2)

/-- Jointly measurable evaluation gives a genuine probability kernel whose
value is the exact original conditional path-law pushforward. -/
theorem conditionalPathMarginal_properties (μ : Kernel G Ω) [IsMarkovKernel μ]
    (Y : G → Ω → E) (hY : Measurable (fun z : G × Ω => Y z.1 z.2)) :
    IsMarkovKernel (conditionalPathMarginal μ Y) ∧
      ∀ h, conditionalPathMarginal μ Y h = (μ h).map (Y h) := by
  refine ⟨Kernel.IsMarkovKernel.map _ hY, ?_⟩
  intro h
  have hy : Measurable (Y h) := hY.comp measurable_prodMk_left
  ext s hs
  rw [conditionalPathMarginal, Kernel.map_apply' _ hY _ hs,
    Kernel.id_prod_apply' _ _ (hs.preimage hY), Measure.map_apply hy hs]
  rfl
end PaperFormalization.Manuscript
