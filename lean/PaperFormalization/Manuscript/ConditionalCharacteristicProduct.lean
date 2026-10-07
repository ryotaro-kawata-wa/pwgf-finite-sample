import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Independence.Basic

/-! # Conditional reference paths from original independent initial seeds

The environment represents the population innovations only. A jointly
measurable common characteristic map sends each independent initial seed to
its whole reference path. The actual kernel and its finite product identity
are constructed; no regular conditional law or stochastic flow is assumed
as a conclusion. Constructing the characteristic map from the dynamics is
outside this measure-theoretic unit.
-/
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory ENNReal
namespace PaperFormalization.Manuscript
variable {Env Seed Path Ω ι : Type*}
  [MeasurableSpace Env] [MeasurableSpace Seed] [MeasurableSpace Path]
  [MeasurableSpace Ω] [Fintype ι]

/-- Push the original seed law through the actual common characteristic map. -/
noncomputable def characteristicKernel (μ : Measure Seed) (Φ : Env → Seed → Path) :
    Kernel Env Path :=
  ((Kernel.id : Kernel Env Env) ×ₖ Kernel.const Env μ).map (fun z => Φ z.1 z.2)

/-- The constructed kernel is Markov and has the unchanged seed pushforward
at every environment. Joint measurability, rather than a conditional-law
premise, ensures that this is an actual measurable kernel. -/
theorem characteristicKernel_properties (μ : Measure Seed) [IsProbabilityMeasure μ]
    (Φ : Env → Seed → Path) (hΦ : Measurable (fun z : Env × Seed => Φ z.1 z.2)) :
    IsMarkovKernel (characteristicKernel μ Φ) ∧
      ∀ e, characteristicKernel μ Φ e = μ.map (Φ e) := by
  refine ⟨Kernel.IsMarkovKernel.map _ hΦ, ?_⟩
  intro e
  have he : Measurable (Φ e) := hΦ.comp measurable_prodMk_left
  ext s hs
  rw [characteristicKernel, Kernel.map_apply' _ hΦ _ hs,
    Kernel.id_prod_apply' _ _ (hs.preimage hΦ), Kernel.const_apply,
    Measure.map_apply he hs]
  rfl

/-- The full reference path-array kernel, formed from actual independent seeds. -/
noncomputable def characteristicProductKernel (μ : Measure Seed) (Φ : Env → Seed → Path) :
    Kernel Env (ι → Path) :=
  characteristicKernel (Measure.pi (fun _ : ι => μ)) (fun e u i => Φ e (u i))

/-- Given an environment, the constructed path-array law is exactly the
product of the single-path laws. This includes an empty particle index set. -/
theorem characteristicProductKernel_properties (μ : Measure Seed) [IsProbabilityMeasure μ]
    (Φ : Env → Seed → Path) (hΦ : Measurable (fun z : Env × Seed => Φ z.1 z.2)) :
    IsMarkovKernel (characteristicProductKernel (ι := ι) μ Φ) ∧
      ∀ e, characteristicProductKernel (ι := ι) μ Φ e =
        Measure.pi (fun _ : ι => μ.map (Φ e)) := by
  have harray : Measurable (fun z : Env × (ι → Seed) => fun i => Φ z.1 (z.2 i)) := by
    exact measurable_pi_lambda _ (fun i => hΦ.comp (measurable_fst.prodMk
      ((measurable_pi_apply i).comp measurable_snd)))
  have hp := characteristicKernel_properties (Measure.pi (fun _ : ι => μ))
    (fun e u i => Φ e (u i)) harray
  refine ⟨hp.1, fun e => (hp.2 e).trans ?_⟩
  exact Measure.pi_map_pi (fun _ => (hΦ.comp measurable_prodMk_left).aemeasurable)

/-- The actual environment/path-array joint law is the original environment
law composed with the derived product kernel. In particular no localization
or change of the population law occurs. -/
theorem characteristicProduct_joint_law (ρ : Measure Env) [IsProbabilityMeasure ρ]
    (μ : Measure Seed) [IsProbabilityMeasure μ]
    (Φ : Env → Seed → Path) (hΦ : Measurable (fun z : Env × Seed => Φ z.1 z.2)) :
    (ρ.prod (Measure.pi (fun _ : ι => μ))).map
      (fun z => (z.1, fun i => Φ z.1 (z.2 i))) =
        ρ ⊗ₘ characteristicProductKernel (ι := ι) μ Φ := by
  have harray : Measurable (fun z : Env × (ι → Seed) => fun i => Φ z.1 (z.2 i)) := by
    exact measurable_pi_lambda _ (fun i => hΦ.comp (measurable_fst.prodMk
      ((measurable_pi_apply i).comp measurable_snd)))
  have hf := measurable_fst.prodMk harray
  have hk := characteristicKernel_properties (Measure.pi (fun _ : ι => μ))
    (fun e u i => Φ e (u i)) harray
  letI : IsMarkovKernel (characteristicProductKernel (ι := ι) μ Φ) := hk.1
  ext s hs
  rw [Measure.map_apply hf hs, Measure.prod_apply (hs.preimage hf), Measure.compProd_apply hs]
  apply lintegral_congr
  intro e
  have he : Measurable (fun u : ι → Seed => fun i => Φ e (u i)) :=
    harray.comp measurable_prodMk_left
  rw [show characteristicProductKernel (ι := ι) μ Φ e =
      (Measure.pi (fun _ : ι => μ)).map (fun u i => Φ e (u i)) from hk.2 e,
    Measure.map_apply he (hs.preimage measurable_prodMk_left)]
  rfl

/-- On an arbitrary original probability space, genuine iid initial seeds
independent of the population environment give the same explicit joint path
law. The environment variable must exclude later finite coupling seeds; no
independence of paths after conditioning on sample localization is asserted. -/
theorem independent_characteristic_joint_law
    (ν : Measure Ω) [IsProbabilityMeasure ν] (μ : Measure Seed) [IsProbabilityMeasure μ]
    (V : Ω → Env) (U : ι → Ω → Seed) (hV : Measurable V) (hU : ∀ i, Measurable (U i))
    (hind : iIndepFun U ν) (henv : IndepFun V (fun ω i => U i ω) ν)
    (hlaw : ∀ i, ν.map (U i) = μ)
    (Φ : Env → Seed → Path) (hΦ : Measurable (fun z : Env × Seed => Φ z.1 z.2)) :
    ν.map (fun ω => (V ω, fun i => Φ (V ω) (U i ω))) =
      (ν.map V) ⊗ₘ characteristicProductKernel (ι := ι) μ Φ := by
  letI : IsProbabilityMeasure (ν.map V) := Measure.isProbabilityMeasure_map hV.aemeasurable
  have hu : Measurable (fun ω i => U i ω) := measurable_pi_lambda _ hU
  have hseeds : ν.map (fun ω i => U i ω) = Measure.pi (fun _ : ι => μ) := by
    rw [hind.map_fun_eq_pi_map (fun i => (hU i).aemeasurable)]
    simp_rw [hlaw]
  have hinput := henv.map_prod_eq_prod_map_map hV.aemeasurable hu.aemeasurable
  rw [hseeds] at hinput
  have harray : Measurable (fun z : Env × (ι → Seed) => fun i => Φ z.1 (z.2 i)) := by
    exact measurable_pi_lambda _ (fun i => hΦ.comp (measurable_fst.prodMk
      ((measurable_pi_apply i).comp measurable_snd)))
  calc
    _ = (ν.map (fun ω => (V ω, fun i => U i ω))).map
        (fun z => (z.1, fun i => Φ z.1 (z.2 i))) := by
      rw [Measure.map_map (measurable_fst.prodMk harray) (hV.prodMk hu)]
      rfl
    _ = ((ν.map V).prod (Measure.pi (fun _ : ι => μ))).map
        (fun z => (z.1, fun i => Φ z.1 (z.2 i))) := by rw [hinput]
    _ = _ := characteristicProduct_joint_law (ν.map V) μ Φ hΦ
end PaperFormalization.Manuscript
