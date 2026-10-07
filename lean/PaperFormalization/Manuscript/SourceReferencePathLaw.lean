import PaperFormalization.Manuscript.OriginalConditionalPathLaw
import PaperFormalization.Manuscript.ConditionalCharacteristicProduct

/-! # Identify the original reference-path marginal from independent seeds

M13p verified unit (see CODEX_HANDOFF_M13P.md). The common conditional path law from M13o is
identified with the actual characteristic pushforward, instead of assuming a
pre-law identity. The argument is at PATH-measure level. All labelled time and
pre-jump marginals therefore agree outside one environment-null set, even for
an uncountable family of evaluations. The conditioning environment is unchanged.
-/
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
namespace PaperFormalization.Manuscript

variable {O Env Seed Ref Pair : Type*}
  [MeasurableSpace O] [MeasurableSpace Env] [MeasurableSpace Seed]
  [MeasurableSpace Ref] [MeasurableSpace Pair]

/-- The original product law pushes forward to the constructed single-path kernel. -/
theorem single_characteristic_product_joint_law
    (ρ : Measure Env) [IsProbabilityMeasure ρ]
    (mu0 : Measure Seed) [IsProbabilityMeasure mu0]
    (Phi : Env -> Seed -> Ref)
    (hPhi : Measurable (fun z : Env × Seed => Phi z.1 z.2)) :
    (ρ.prod mu0).map (fun z => (z.1, Phi z.1 z.2)) =
      ρ ⊗ₘ characteristicKernel mu0 Phi := by
  letI : IsMarkovKernel (characteristicKernel mu0 Phi) :=
    (characteristicKernel_properties mu0 Phi hPhi).1
  have hf := measurable_fst.prodMk hPhi
  ext s hs
  rw [Measure.map_apply hf hs, Measure.prod_apply (hs.preimage hf), Measure.compProd_apply hs]
  apply lintegral_congr
  intro e
  have hPhi_e : Measurable (Phi e) := hPhi.comp measurable_prodMk_left
  rw [(characteristicKernel_properties mu0 Phi hPhi).2 e,
    Measure.map_apply hPhi_e (hs.preimage (measurable_prodMk_left (x := e)))]
  rfl

/-- The single-path observation law follows from the ORIGINAL independence,
with no conditional moment or conditional-law equality premise. -/
theorem independent_single_characteristic_joint_law
    (nu : Measure O) [IsProbabilityMeasure nu]
    (mu0 : Measure Seed) [IsProbabilityMeasure mu0]
    (environment : O -> Env) (initial : O -> Seed)
    (henv : Measurable environment) (hinit : Measurable initial)
    (hind : IndepFun environment initial nu) (hlaw : nu.map initial = mu0)
    (Phi : Env -> Seed -> Ref)
    (hPhi : Measurable (fun z : Env × Seed => Phi z.1 z.2)) :
    nu.map (fun w => (environment w, Phi (environment w) (initial w))) =
      (nu.map environment) ⊗ₘ characteristicKernel mu0 Phi := by
  letI : IsProbabilityMeasure (nu.map environment) :=
    Measure.isProbabilityMeasure_map henv.aemeasurable
  have hin := hind.map_prod_eq_prod_map_map henv.aemeasurable hinit.aemeasurable
  rw [hlaw] at hin
  calc
    _ = (nu.map (fun w => (environment w, initial w))).map
        (fun z => (z.1, Phi z.1 z.2)) := by
      rw [Measure.map_map (measurable_fst.prodMk hPhi) (henv.prodMk hinit)]
      rfl
    _ = ((nu.map environment).prod mu0).map (fun z => (z.1, Phi z.1 z.2)) := by rw [hin]
    _ = _ := single_characteristic_product_joint_law (nu.map environment) mu0 Phi hPhi

/-- Marginalize the initial-array independence before taking any conditional
law. This is not independence after localization. -/
theorem original_environment_independent_initial_coordinate
    {I : Type*} (nu : Measure O)
    (environment : O -> Env) (initial : I -> O -> Seed)
    (hind : IndepFun environment (fun w i => initial i w) nu) (i : I) :
    IndepFun environment (initial i) nu := by
  simpa only [Function.comp_def, id_eq] using hind.comp measurable_id (measurable_pi_apply i)

/-- Identify the reference component of the common pair-path conditional law.
`hreference` is an AE equality of random PATHS, not a desired equality of laws. -/
theorem original_reference_path_law_identified
    [StandardBorelSpace Ref] [Nonempty Ref]
    [StandardBorelSpace Pair] [Nonempty Pair]
    (nu : Measure O) [IsProbabilityMeasure nu]
    (mu0 : Measure Seed) [IsProbabilityMeasure mu0]
    (environment : O -> Env) (initial : O -> Seed)
    (henv : Measurable environment) (hinit : Measurable initial)
    (hind : IndepFun environment initial nu) (hlaw : nu.map initial = mu0)
    (paths : O -> Pair) (hpaths : Measurable paths)
    (reference : Pair -> Ref) (href : Measurable reference)
    (Phi : Env -> Seed -> Ref)
    (hPhi : Measurable (fun z : Env × Seed => Phi z.1 z.2))
    (hreference : (fun w => reference (paths w)) =ᵐ[nu]
      (fun w => Phi (environment w) (initial w))) :
    (originalConditionalPathLaw nu environment paths).map reference
      =ᵐ[nu.map environment] characteristicKernel mu0 Phi := by
  letI : IsMarkovKernel (characteristicKernel mu0 Phi) :=
    (characteristicKernel_properties mu0 Phi hPhi).1
  have hjoint := independent_single_characteristic_joint_law nu mu0 environment initial
    henv hinit hind hlaw Phi hPhi
  have hchar := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable henv
    (hPhi.comp (henv.prodMk hinit)) hjoint
  have hproj := condDistrib_comp (μ := nu) (mβ := inferInstance) environment hpaths.aemeasurable href
  have heq := condDistrib_congr_left (X := environment) (mβ := inferInstance) hreference
  change (condDistrib paths environment nu).map reference
    =ᵐ[nu.map environment] characteristicKernel mu0 Phi
  filter_upwards [hproj, hchar] with e hpe hce
  exact hpe.symm.trans ((congrArg (fun K => K e) heq).trans hce)

/-- One PATH-law equality yields all evaluation laws on one AE environment set.
The target may depend on the environment; no union of timewise null sets occurs. -/
theorem original_reference_all_evaluation_laws
    {I E : Type*} [MeasurableSpace E]
    [StandardBorelSpace Ref] [Nonempty Ref]
    [StandardBorelSpace Pair] [Nonempty Pair]
    (nu : Measure O) [IsProbabilityMeasure nu]
    (mu0 : Measure Seed) [IsProbabilityMeasure mu0]
    (environment : O -> Env) (initial : O -> Seed)
    (henv : Measurable environment) (hinit : Measurable initial)
    (hind : IndepFun environment initial nu) (hlaw : nu.map initial = mu0)
    (paths : O -> Pair) (hpaths : Measurable paths)
    (reference : Pair -> Ref) (href : Measurable reference)
    (Phi : Env -> Seed -> Ref)
    (hPhi : Measurable (fun z : Env × Seed => Phi z.1 z.2))
    (hreference : (fun w => reference (paths w)) =ᵐ[nu]
      (fun w => Phi (environment w) (initial w)))
    (eval : I -> Env -> Ref -> E) (heval : ∀ i e, Measurable (eval i e)) :
    ∀ᵐ e ∂nu.map environment, ∀ i,
      (originalConditionalPathLaw nu environment paths e).map (fun p => eval i e (reference p)) =
        mu0.map (fun u => eval i e (Phi e u)) := by
  have hid := original_reference_path_law_identified nu mu0 environment initial henv hinit
    hind hlaw paths hpaths reference href Phi hPhi hreference
  filter_upwards [hid] with e he
  have hm : ((originalConditionalPathLaw nu environment paths).map reference) e =
      (originalConditionalPathLaw nu environment paths e).map reference := by
    ext s hs
    rw [Kernel.map_apply' _ href _ hs, Measure.map_apply href hs]
  rw [hm, (characteristicKernel_properties mu0 Phi hPhi).2 e] at he
  intro i
  calc
    _ = ((originalConditionalPathLaw nu environment paths e).map reference).map (eval i e) := by
      rw [Measure.map_map (heval i e) href]
      rfl
    _ = (mu0.map (Phi e)).map (eval i e) := by rw [he]
    _ = _ := by
      have hPhi_e : Measurable (Phi e) := hPhi.comp measurable_prodMk_left
      rw [Measure.map_map (heval i e) hPhi_e]
      rfl

end PaperFormalization.Manuscript
