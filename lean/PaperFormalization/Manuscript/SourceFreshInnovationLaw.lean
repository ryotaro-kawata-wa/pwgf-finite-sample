import PaperFormalization.Manuscript.SourceReferencePathLaw
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! # Fresh innovations and enlarged histories on the unchanged original law

M13q verified unit (see CODEX_HANDOFF_M13Q.md). Independence is imposed on the primitive fresh
innovation and the entire past, as in the original model, not on a whitened
coordinate. Adding independent past auxiliaries is proved safe. No good-event
restriction and no future population observation is introduced.
-/
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
namespace PaperFormalization.Manuscript
variable {O S W A E : Type*} [MeasurableSpace O] [MeasurableSpace S]
  [MeasurableSpace W] [MeasurableSpace A] [MeasurableSpace E]

/-- The fresh-innovation conditional evaluation law follows from the ORIGINAL
independence, rather than being an assumed law of the evaluated vector. -/
theorem source_condDistrib_fresh_evaluation
    [StandardBorelSpace E] [Nonempty E]
    (nu : Measure O) [IsProbabilityMeasure nu]
    (lambda : Measure W) [IsProbabilityMeasure lambda]
    (history : O -> S) (innovation : O -> W)
    (hH : Measurable history) (hW : Measurable innovation)
    (hind : IndepFun history innovation nu) (hlaw : nu.map innovation = lambda)
    (evaluate : S -> W -> E)
    (hevaluate : Measurable (fun z : S × W => evaluate z.1 z.2)) :
    condDistrib (fun o => evaluate (history o) (innovation o)) history nu
      =ᵐ[nu.map history] characteristicKernel lambda evaluate := by
  letI : IsMarkovKernel (characteristicKernel lambda evaluate) :=
    (characteristicKernel_properties lambda evaluate hevaluate).1
  exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hH
    (hevaluate.comp (hH.prodMk hW))
    (independent_single_characteristic_joint_law nu lambda history innovation hH hW
      hind hlaw evaluate hevaluate)

/-- Joint factorization after revealing an independent auxiliary PAST.
The fresh innovation stays outside the revealed history. -/
theorem source_fresh_joint_after_auxiliary
    (nu : Measure O) [IsProbabilityMeasure nu]
    (lambda : Measure A) [IsProbabilityMeasure lambda]
    (history : O -> S) (innovation : O -> W)
    (hH : Measurable history) (hW : Measurable innovation)
    (hind : IndepFun history innovation nu) :
    (nu.prod lambda).map (fun z => ((history z.1, z.2), innovation z.1)) =
      ((nu.map history).prod lambda).prod (nu.map innovation) := by
  have hm : Measurable (fun z : O × A => ((history z.1,z.2),innovation z.1)) :=
    ((hH.comp measurable_fst).prodMk measurable_snd).prodMk (hW.comp measurable_fst)
  apply Measure.ext_prod₃'
  intro s t u hs ht hu
  rw [Measure.map_apply hm ((hs.prod ht).prod hu)]
  have hpre : (fun z : O × A => ((history z.1,z.2),innovation z.1)) ⁻¹'
      ((s ×ˢ t) ×ˢ u) = (history ⁻¹' s ∩ innovation ⁻¹' u) ×ˢ t := by
    ext z
    simp only [mem_preimage, mem_prod, mem_inter_iff]
    tauto
  rw [hpre]
  rw [Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
  have hjoint := hind.map_prod_eq_prod_map_map hH.aemeasurable hW.aemeasurable
  have hr := congrArg (fun m : Measure (S × W) => m (s ×ˢ u)) hjoint
  rw [Measure.map_apply (hH.prodMk hW) (hs.prod hu), Measure.prod_prod] at hr
  change nu (history ⁻¹' s ∩ innovation ⁻¹' u) = _ at hr
  rw [hr]
  ac_rfl

/-- The enlarged history itself has the original-history times auxiliary law. -/
theorem source_auxiliary_history_marginal
    (nu : Measure O) [IsProbabilityMeasure nu]
    (lambda : Measure A) [IsProbabilityMeasure lambda]
    (history : O -> S) (hH : Measurable history) :
    (nu.prod lambda).map (fun z => (history z.1,z.2)) = (nu.map history).prod lambda := by
  simpa only [Measure.map_id, Prod.map_def, id_eq] using
    (Measure.map_prod_map nu lambda hH measurable_id).symm

/-- State-dependent field evaluations may depend on ALL past auxiliaries.
The innovation law is unchanged, not conditioned on a population good event. -/
theorem source_condDistrib_fresh_evaluation_after_auxiliary
    [StandardBorelSpace E] [Nonempty E]
    (nu : Measure O) [IsProbabilityMeasure nu]
    (lambdaW : Measure W) [IsProbabilityMeasure lambdaW]
    (lambdaA : Measure A) [IsProbabilityMeasure lambdaA]
    (history : O -> S) (innovation : O -> W)
    (hH : Measurable history) (hW : Measurable innovation)
    (hind : IndepFun history innovation nu) (hlaw : nu.map innovation = lambdaW)
    (evaluate : (S × A) -> W -> E)
    (hevaluate : Measurable (fun z : (S × A) × W => evaluate z.1 z.2)) :
    condDistrib (fun z : O × A => evaluate (history z.1,z.2) (innovation z.1))
      (fun z => (history z.1,z.2)) (nu.prod lambdaA)
      =ᵐ[(nu.map history).prod lambdaA] characteristicKernel lambdaW evaluate := by
  let H := fun z : O × A => (history z.1,z.2)
  let I := fun z : O × A => innovation z.1
  have hHm : Measurable H := (hH.comp measurable_fst).prodMk measurable_snd
  have hIm : Measurable I := hW.comp measurable_fst
  letI : IsProbabilityMeasure (nu.map history) := Measure.isProbabilityMeasure_map hH.aemeasurable
  letI : IsMarkovKernel (characteristicKernel lambdaW evaluate) :=
    (characteristicKernel_properties lambdaW evaluate hevaluate).1
  have hHI := source_fresh_joint_after_auxiliary nu lambdaA history innovation hH hW hind
  rw [hlaw] at hHI
  have hHmarg := source_auxiliary_history_marginal nu lambdaA history hH
  have hjoint : (nu.prod lambdaA).map (fun z => (H z,evaluate (H z) (I z))) =
      ((nu.prod lambdaA).map H) ⊗ₘ characteristicKernel lambdaW evaluate := by
    calc
      _ = ((nu.prod lambdaA).map (fun z => (H z,I z))).map
          (fun z => (z.1,evaluate z.1 z.2)) := by
        rw [Measure.map_map (measurable_fst.prodMk hevaluate) (hHm.prodMk hIm)]
        rfl
      _ = (((nu.map history).prod lambdaA).prod lambdaW).map
          (fun z => (z.1,evaluate z.1 z.2)) := by rw [hHI]
      _ = ((nu.map history).prod lambdaA) ⊗ₘ characteristicKernel lambdaW evaluate :=
        single_characteristic_product_joint_law _ lambdaW evaluate hevaluate
      _ = _ := by rw [hHmarg]
  have hcd := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hHm
    (hevaluate.comp (hHm.prodMk hIm)) hjoint
  simpa only [H, I, Function.comp_def, hHmarg] using hcd

/-- A finite Gaussian field model under its primitive innovation law gives the
raw evaluation's conditional Gaussian law. The covariance may be singular. -/
theorem source_fresh_evaluation_gaussian
    {I : Type*} [Fintype I] [DecidableEq I]
    (nu : Measure O) [IsProbabilityMeasure nu]
    (lambda : Measure W) [IsProbabilityMeasure lambda]
    (history : O -> S) (innovation : O -> W)
    (hH : Measurable history) (hW : Measurable innovation)
    (hind : IndepFun history innovation nu) (hlaw : nu.map innovation = lambda)
    (evaluate : S -> W -> EuclideanSpace Real I)
    (hevaluate : Measurable (fun z : S × W => evaluate z.1 z.2))
    (Cov : S -> Matrix I I Real)
    (hfield : ∀ᵐ h ∂ nu.map history,
      lambda.map (evaluate h) = multivariateGaussian 0 (Cov h)) :
    ∀ᵐ h ∂ nu.map history,
      condDistrib (fun o => evaluate (history o) (innovation o)) history nu h =
        multivariateGaussian 0 (Cov h) := by
  filter_upwards [source_condDistrib_fresh_evaluation nu lambda history innovation hH hW
    hind hlaw evaluate hevaluate, hfield] with h hc hf
  exact (hc.trans ((characteristicKernel_properties lambda evaluate hevaluate).2 h)).trans hf

/-- An independent auxiliary extension leaves every original observable's law
unchanged, before taking any conditional distribution. -/
theorem source_original_map_after_auxiliary
    (nu : Measure O) [IsProbabilityMeasure nu]
    (lambda : Measure A) [IsProbabilityMeasure lambda]
    (f : O -> E) (hf : Measurable f) :
    (nu.prod lambda).map (fun z => f z.1) = nu.map f := by
  have hfst : MeasurePreserving (Prod.fst : O × A -> O) (nu.prod lambda) nu :=
    measurePreserving_fst
  change (nu.prod lambda).map (f ∘ Prod.fst) = _
  rw [← Measure.map_map hf measurable_fst, hfst.map_eq]

/-- Primitive fresh independence survives revealing arbitrary independent past
auxiliaries. This does not add future original observations to history. -/
theorem source_fresh_independent_after_auxiliary
    (nu : Measure O) [IsProbabilityMeasure nu]
    (lambda : Measure A) [IsProbabilityMeasure lambda]
    (history : O -> S) (innovation : O -> W)
    (hH : Measurable history) (hW : Measurable innovation)
    (hind : IndepFun history innovation nu) :
    IndepFun (fun z : O × A => (history z.1,z.2))
      (fun z => innovation z.1) (nu.prod lambda) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    ((hH.comp measurable_fst).prodMk measurable_snd).aemeasurable
    (hW.comp measurable_fst).aemeasurable).mpr
  simp only [Function.comp_def]
  rw [source_fresh_joint_after_auxiliary nu lambda history innovation hH hW hind,
    source_auxiliary_history_marginal nu lambda history hH,
    source_original_map_after_auxiliary nu lambda innovation hW]

/-- Pullback along a measure-preserving original-coordinate projection preserves
original independence, without conditioning on any event. -/
theorem source_independence_pullback
    {O' : Type*} [MeasurableSpace O']
    (nu : Measure O) [IsProbabilityMeasure nu]
    (nu' : Measure O') [IsProbabilityMeasure nu']
    (project : O' -> O) (hproject : MeasurePreserving project nu' nu)
    (f : O -> S) (g : O -> W) (hf : Measurable f) (hg : Measurable g)
    (hind : IndepFun f g nu) : IndepFun (f ∘ project) (g ∘ project) nu' := by
  apply (indepFun_iff_map_prod_eq_prod_map_map (hf.comp hproject.measurable).aemeasurable
    (hg.comp hproject.measurable).aemeasurable).mpr
  change nu'.map ((fun o => (f o,g o)) ∘ project) = _
  rw [← Measure.map_map (hf.prodMk hg) hproject.measurable,
    ← Measure.map_map hf hproject.measurable,
    ← Measure.map_map hg hproject.measurable, hproject.map_eq]
  exact hind.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable
end PaperFormalization.Manuscript
