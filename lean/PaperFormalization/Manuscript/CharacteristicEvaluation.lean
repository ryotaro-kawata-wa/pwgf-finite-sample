import PaperFormalization.Manuscript.ConditionalCharacteristicProduct
import PaperFormalization.Manuscript.ConditionalPathMarginal

/-! # Actual iid evaluations of the constructed conditional path product

A common measurable evaluation may depend on the population environment.
Its actual conditional particle laws and full independence follow from the
previously constructed path product, before sample localization. No regular
conditional distribution, topology on paths, or independence conclusion is
assumed.
-/
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
namespace PaperFormalization.Manuscript
variable {G Seed Path E Ω ι : Type*} [MeasurableSpace G] [MeasurableSpace Seed]
  [MeasurableSpace Path] [MeasurableSpace E] [MeasurableSpace Ω] [Fintype ι]

/-- Common actual measurable evaluations of the constructed reference paths
are jointly measurable, conditionally independent, and have the exact
single-path marginal. This holds for every environment, including an empty
particle index set. -/
theorem characteristicProductKernel_evaluation_laws
    (μ : Measure Seed) [IsProbabilityMeasure μ]
    (Φ : G → Seed → Path) (hΦ : Measurable (fun z : G × Seed => Φ z.1 z.2))
    (ev : G → Path → E) (hev : Measurable (fun z : G × Path => ev z.1 z.2)) :
    (∀ i : ι, Measurable (fun z : G × (ι → Path) => ev z.1 (z.2 i))) ∧
    ∀ h, iIndepFun (fun i (v : ι → Path) => ev h (v i))
        (characteristicProductKernel (ι := ι) μ Φ h) ∧
      ∀ i : ι, (characteristicProductKernel (ι := ι) μ Φ h).map
          (fun v => ev h (v i)) = (characteristicKernel μ Φ h).map (ev h) := by
  refine ⟨fun i => hev.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)), ?_⟩
  intro h
  have hphi : Measurable (Φ h) := hΦ.comp measurable_prodMk_left
  have he : Measurable (ev h) := hev.comp measurable_prodMk_left
  letI : IsProbabilityMeasure (μ.map (Φ h)) := Measure.isProbabilityMeasure_map hphi.aemeasurable
  rw [(characteristicProductKernel_properties μ Φ hΦ).2 h,
    (characteristicKernel_properties μ Φ hΦ).2 h]
  refine ⟨iIndepFun_pi (fun _ => he.aemeasurable), ?_⟩
  intro i
  calc
    _ = ((Measure.pi (fun _ : ι => μ.map (Φ h))).map (Function.eval i)).map (ev h) := by
      rw [Measure.map_map he (measurable_pi_apply i)]
      rfl
    _ = _ := by rw [(measurePreserving_eval (fun _ : ι => μ.map (Φ h)) i).map_eq]

/-- The actual evaluated reference cloud on an arbitrary original system
has the derived environment/product joint law. Initial full iid and
independence of the entire seed array from population innovations are the
inputs; finite comparison-coupling seeds are outside that environment. -/
theorem independent_characteristic_evaluation_joint_law
    (ν : Measure Ω) [IsProbabilityMeasure ν] (μ : Measure Seed) [IsProbabilityMeasure μ]
    (V : Ω → G) (U : ι → Ω → Seed) (hV : Measurable V) (hU : ∀ i, Measurable (U i))
    (hind : iIndepFun U ν) (henv : IndepFun V (fun ω i => U i ω) ν)
    (hlaw : ∀ i, ν.map (U i) = μ)
    (Φ : G → Seed → Path) (hΦ : Measurable (fun z : G × Seed => Φ z.1 z.2))
    (ev : G → Path → E) (hev : Measurable (fun z : G × Path => ev z.1 z.2)) :
    ν.map (fun ω => (V ω, fun i => ev (V ω) (Φ (V ω) (U i ω)))) =
      (ν.map V) ⊗ₘ characteristicProductKernel (ι := ι) μ (fun h u => ev h (Φ h u)) := by
  exact independent_characteristic_joint_law ν μ V U hV hU hind henv hlaw
    (fun h u => ev h (Φ h u)) (hev.comp (measurable_fst.prodMk hΦ))
end PaperFormalization.Manuscript
