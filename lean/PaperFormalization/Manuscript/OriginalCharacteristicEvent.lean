import PaperFormalization.Manuscript.ConditionalCharacteristicProduct
import Mathlib.MeasureTheory.Measure.Real

/-! # Pull the constructed characteristic event back to the original system

The observation-law identity is derived from original independent initial
seeds and the common measurable characteristic map. A common AE model event
on the original system is retained at no additional probability loss.
-/
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
namespace PaperFormalization.Manuscript
variable {G Seed Path Ω ι : Type*} [MeasurableSpace G] [MeasurableSpace Seed]
  [MeasurableSpace Path] [MeasurableSpace Ω] [Fintype ι]

/-- A measurable event for the derived conditional reference-path product
pulls back to an actual measurable original-system event with the same loss.
The joint observation law is proved internally from initial independence. -/
theorem exists_original_characteristic_event
    (ν : Measure Ω) [IsProbabilityMeasure ν] (μ₀ : Measure Seed) [IsProbabilityMeasure μ₀]
    (V : Ω → G) (U : ι → Ω → Seed) (hV : Measurable V) (hU : ∀ i, Measurable (U i))
    (hind : iIndepFun U ν) (henv : IndepFun V (fun ω i => U i ω) ν)
    (hlaw : ∀ i, ν.map (U i) = μ₀)
    (Φ : G → Seed → Path) (hΦ : Measurable (fun z : G × Seed => Φ z.1 z.2))
    (Good : Set (G × (ι → Path))) (hGood : MeasurableSet Good) (p : ℝ)
    (hbudget : ((ν.map V) ⊗ₘ characteristicProductKernel (ι := ι) μ₀ Φ).real Goodᶜ ≤ p)
    (Model : Ω → Prop) (hModel : ∀ᵐ ω ∂ν, Model ω) :
    ∃ OriginalGood : Set Ω, MeasurableSet OriginalGood ∧ ν.real OriginalGoodᶜ ≤ p ∧
      ∀ ω ∈ OriginalGood, Model ω ∧ (V ω, fun i => Φ (V ω) (U i ω)) ∈ Good := by
  let obs := fun ω => (V ω, fun i => Φ (V ω) (U i ω))
  have hobs : Measurable obs := hV.prodMk (measurable_pi_lambda _
    (fun i => hΦ.comp (hV.prodMk (hU i))))
  have hview := independent_characteristic_joint_law ν μ₀ V U hV hU hind henv hlaw Φ hΦ
  have hpull : ν.real ((obs ⁻¹' Good)ᶜ) ≤ p := by
    rw [← preimage_compl, ← map_measureReal_apply hobs hGood.compl]
    exact hview ▸ hbudget
  obtain ⟨Null, hNullSub, hNullMeas, hNullZero⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hModel)
  refine ⟨Nullᶜ ∩ (obs ⁻¹' Good), hNullMeas.compl.inter (hGood.preimage hobs), ?_, ?_⟩
  · rw [compl_inter, compl_compl]
    have hNullReal : ν.real Null = 0 := by simp only [measureReal_def, hNullZero, ENNReal.toReal_zero]
    exact (measureReal_union_le Null ((obs ⁻¹' Good)ᶜ)).trans
      (by simpa only [hNullReal, zero_add] using hpull)
  · intro ω hω
    refine ⟨?_, hω.2⟩
    by_contra hm
    exact hω.1 (hNullSub hm)
end PaperFormalization.Manuscript
