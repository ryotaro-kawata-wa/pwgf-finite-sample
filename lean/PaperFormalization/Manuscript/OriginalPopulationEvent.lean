import PaperFormalization.Manuscript.PopulationKernelLocalization

/-! # Pulling the constructed population event to the original system

The source localization theorem constructs a measurable history event. This
adapter transfers that event through the explicit original environment law,
retains any AE original-system model, and preserves its probability budget.
It does not identify a future population event with a Gaussian prehistory.
-/
open MeasureTheory Set
namespace PaperFormalization.Manuscript

/-- A derived population event has the same budget under its original
measurable environment observation. A common AE original model costs nothing.
Instantiate PopGood with exists_source_population_kernel_localization_event;
its all-time conclusions apply at V omega by the returned membership. -/
theorem exists_original_population_event
    {O S : Type*} [MeasurableSpace O] [MeasurableSpace S]
    (ν : Measure O) [IsProbabilityMeasure ν] (ρ : Measure S)
    (V : O → S) (hV : Measurable V) (hLaw : ν.map V = ρ)
    (PopGood : Set S) (hPopGood : MeasurableSet PopGood)
    (p0 : ℝ) (hbudget : ρ.real PopGoodᶜ ≤ p0)
    (Model : O → Prop) (hModel : ∀ᵐ ω ∂ν, Model ω) :
    ∃ OriginalGood : Set O, MeasurableSet OriginalGood ∧
      ν.real OriginalGoodᶜ ≤ p0 ∧
      ∀ ω ∈ OriginalGood, Model ω ∧ V ω ∈ PopGood := by
  have hpre : MeasurableSet (V ⁻¹' PopGood) := hPopGood.preimage hV
  have hpreBudget : ν.real ((V ⁻¹' PopGood)ᶜ) ≤ p0 := by
    rw [← preimage_compl, ← map_measureReal_apply hV hPopGood.compl, hLaw]
    exact hbudget
  obtain ⟨Null,hNullSub,hNullMeas,hNullZero⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hModel)
  refine ⟨Nullᶜ ∩ (V ⁻¹' PopGood),hNullMeas.compl.inter hpre,?_,?_⟩
  · rw [compl_inter,compl_compl]
    have hz : ν.real Null = 0 := by simp only [measureReal_def,hNullZero,ENNReal.toReal_zero]
    exact (measureReal_union_le Null ((V ⁻¹' PopGood)ᶜ)).trans
      (by simpa only [hz,zero_add] using hpreBudget)
  · intro ω hω
    refine ⟨?_,hω.2⟩
    by_contra hn
    exact hω.1 (hNullSub hn)

end PaperFormalization.Manuscript
