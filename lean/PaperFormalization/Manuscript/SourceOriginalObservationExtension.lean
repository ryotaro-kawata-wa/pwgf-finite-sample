import PaperFormalization.Manuscript.SourceObservedCovarianceSchedule
import PaperFormalization.Manuscript.ConditionalAlignedSeedAE
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.Prod

/-! # A real auxiliary extension of the ORIGINAL experiment

M13p verified unit (see CODEX_HANDOFF_M13P.md). The original measure is extended by a product
with one fresh auxiliary law. The observation law of (history, raw population
vector, auxiliary) is then derived from disintegration, not assumed. Forgetting
the auxiliary preserves every original event and random variable.
-/
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
namespace PaperFormalization.Manuscript

variable {O S V A : Type*} [MeasurableSpace O] [MeasurableSpace S]
  [MeasurableSpace V] [MeasurableSpace A]

/-- Associating an independent auxiliary with a kernel is the same joint law. -/
theorem source_compProd_auxiliary_associate
    (ρ : Measure S) [IsProbabilityMeasure ρ]
    (k : Kernel S V) [IsMarkovKernel k]
    (lambda : Measure A) [IsProbabilityMeasure lambda] :
    ((ρ ⊗ₘ k).prod lambda).map (fun z : (S × V) × A => (z.1.1, (z.1.2, z.2))) =
      ρ ⊗ₘ k.prod (Kernel.const S lambda) := by
  have hk : k.compProd (Kernel.const (S × V) lambda) = k.prod (Kernel.const S lambda) := by
    ext h s hs
    rw [Kernel.compProd_apply hs, Kernel.prod_apply' _ _ _ hs]
    rfl
  have ha := Measure.compProd_assoc (μ := ρ) (κ := k)
    (η := Kernel.const (S × V) lambda)
  rw [hk, Measure.compProd_const] at ha
  calc
    _ = ((ρ ⊗ₘ k.prod (Kernel.const S lambda)).map
        MeasurableEquiv.prodAssoc.symm).map MeasurableEquiv.prodAssoc := by rw [ha]; rfl
    _ = _ := by
      rw [Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]
      simp only [Function.comp_def, MeasurableEquiv.apply_symm_apply]
      exact Measure.map_id

/-- Exact observation law on the unchanged original experiment plus a fresh
auxiliary. The original space O need NOT be standard Borel. Only the finite
population observation V must admit a regular conditional law. -/
theorem source_original_auxiliary_observation_law
    [StandardBorelSpace V] [Nonempty V]
    (nu : Measure O) [IsProbabilityMeasure nu]
    (history : O -> S) (population : O -> V)
    (hhistory : Measurable history) (hpopulation : Measurable population)
    (lambda : Measure A) [IsProbabilityMeasure lambda] :
    (nu.prod lambda).map (fun z => (history z.1, (population z.1, z.2))) =
      (nu.map history) ⊗ₘ (condDistrib population history nu).prod (Kernel.const S lambda) := by
  letI : IsProbabilityMeasure (nu.map history) :=
    Measure.isProbabilityMeasure_map hhistory.aemeasurable
  let observation := fun w => (history w, population w)
  have hobs : Measurable observation := hhistory.prodMk hpopulation
  have hprod : (nu.map observation).prod lambda =
      (nu.prod lambda).map (Prod.map observation id) := by
    simpa only [Measure.map_id] using Measure.map_prod_map nu lambda hobs measurable_id
  have hjoint : nu.map observation = (nu.map history) ⊗ₘ condDistrib population history nu :=
    (compProd_map_condDistrib hpopulation.aemeasurable).symm
  calc
    _ = ((nu.prod lambda).map (Prod.map observation id)).map
        (fun z : (S × V) × A => (z.1.1, (z.1.2, z.2))) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = ((nu.map observation).prod lambda).map
        (fun z : (S × V) × A => (z.1.1, (z.1.2, z.2))) := by rw [hprod]
    _ = _ := by
      rw [hjoint]
      exact source_compProd_auxiliary_associate (nu.map history) _ lambda

/-- Forgetting fresh auxiliary randomness preserves the complete original law. -/
theorem source_original_auxiliary_preserves
    (nu : Measure O) [IsProbabilityMeasure nu]
    (lambda : Measure A) [IsProbabilityMeasure lambda] :
    (nu.prod lambda).map (Prod.fst : O × A -> O) = nu :=
  measurePreserving_fst.map_eq

/-- Any existing covariance view lifts to the auxiliary extension with the same
law, sample, population kernel, and eligibility. No new conditional iid premise. -/
noncomputable def sourceCovarianceView_lift_auxiliary
    {N d : ℕ} {alpha K : ℝ} {E W : Type*}
    [MeasurableSpace E] [MeasurableSpace W]
    (nu : Measure O) [IsProbabilityMeasure nu]
    (lambda : Measure A) [IsProbabilityMeasure lambda]
    (view : SourceObservedCovarianceView N d alpha K nu E W) :
    SourceObservedCovarianceView N d alpha K (nu.prod lambda) E W := {
  ρ := view.ρ
  probability := view.probability
  k := view.k
  markov := view.markov
  κ := view.κ
  population_markov := view.population_markov
  PopGood := view.PopGood
  measurable_popGood := view.measurable_popGood
  X := view.X
  measurable_X := view.measurable_X
  source_model := view.source_model
  observation := fun z => view.observation z.1
  measurable_observation := view.measurable_observation.comp measurable_fst
  observation_law := by
    change (nu.prod lambda).map (view.observation ∘ Prod.fst) = _
    rw [<- Measure.map_map view.measurable_observation measurable_fst,
      source_original_auxiliary_preserves nu lambda]
    exact view.observation_law }

end PaperFormalization.Manuscript
