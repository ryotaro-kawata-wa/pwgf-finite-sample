import PaperFormalization.Manuscript.SourceConstructedPopulationEvent
import PaperFormalization.Manuscript.SourceReferencePathIdentification
import PaperFormalization.Manuscript.SourceOriginalReferenceGamma

/-! # The constructed population event supplies the original Gamma inputs

M13q verified unit (see CODEX_HANDOFF_M13Q.md). Common-path identification and source regularity
supply the conditional support and moments. Every time and both closed endpoint
labels use the SAME path-measure equality. No iid-after-localization argument or
uncountable intersection of exceptional sets is used.
-/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ProbabilityTheory
namespace PaperFormalization.Manuscript
variable {O Env Seed : Type*} [MeasurableSpace O] [MeasurableSpace Env] [MeasurableSpace Seed]

/-- Source AE Lipschitz regularity of an original reference path is transported
to its actual characteristic kernel through the original independent-seed law. -/
theorem source_reference_kernel_support_of_original
    (J d : Nat) (a b : Fin (J+1) -> Real) (B : NNReal)
    (nu : Measure O) [IsProbabilityMeasure nu]
    (mu0 : Measure Seed) [IsProbabilityMeasure mu0]
    (env : O -> Env) (initial : O -> Seed)
    (henv : Measurable env) (hinit : Measurable initial)
    (hind : IndepFun env initial nu) (hlaw : nu.map initial = mu0)
    (Phi : Env -> Seed -> SourceReferencePathSpace J d a b)
    (hPhi : Measurable (fun z : Env × Seed => Phi z.1 z.2))
    (hLip : ∀ᵐ o ∂ nu, ∀ j,
      LipschitzOnWith B (fun t => sourceReferencePathEval (Phi (env o) (initial o)) j t)
        (Icc (a j) (b j))) :
    ∀ᵐ h ∂ nu.map env, ∀ᵐ path ∂ characteristicKernel mu0 Phi h,
      path ∈ sourceReferencePathLipschitz B := by
  letI : IsProbabilityMeasure (nu.map env) := Measure.isProbabilityMeasure_map henv.aemeasurable
  letI : IsMarkovKernel (characteristicKernel mu0 Phi) :=
    (characteristicKernel_properties mu0 Phi hPhi).1
  have hjoint := independent_single_characteristic_joint_law nu mu0 env initial
    henv hinit hind hlaw Phi hPhi
  have hobs : Measurable (fun o => (env o, Phi (env o) (initial o))) :=
    henv.prodMk (hPhi.comp (henv.prodMk hinit))
  have hs : MeasurableSet (sourceReferencePathLipschitz (J := J) (d := d) (a := a) (b := b) B) :=
    (sourceReferencePathLipschitz_isClosed B).measurableSet
  have hjointSupport : ∀ᵐ z ∂ (nu.map env) ⊗ₘ characteristicKernel mu0 Phi,
      z.2 ∈ sourceReferencePathLipschitz B := by
    rw [← hjoint]
    apply (ae_map_iff hobs.aemeasurable (hs.preimage measurable_snd)).mpr
    exact hLip.mono (fun o ho => (sourceReferencePathLipschitz_iff B _).mpr ho)
  exact Measure.ae_ae_of_ae_compProd hjointSupport

/-- One path-measure identity transfers the constructed population exponential
bounds to the reference kernel with the exact unnormalized source constants.
The identity and bounds are provided by the existing original-path constructors,
not separately assumed conditional Gaussian/independence properties. -/
theorem source_pair_population_gamma_inputs
    (J d : Nat) (a btime : Fin (J+1) -> Real) (B : NNReal)
    (rho : Measure Env)
    (law : Kernel Env (SourcePopulationPathSpace J d a btime)) [IsMarkovKernel law]
    (mu0 : Measure Seed) [IsProbabilityMeasure mu0]
    (Phi : Env -> Seed -> SourceReferencePathSpace J d a btime)
    (hPhi : Measurable (fun z : Env × Seed => Phi z.1 z.2))
    (hIdent : law.map (fun p => p 1) =ᵐ[rho] characteristicKernel mu0 Phi)
    (hSupport : ∀ᵐ h ∂ rho, ∀ᵐ path ∂ characteristicKernel mu0 Phi h,
      path ∈ sourceReferencePathLipschitz B)
    (PopGood : Set Env) (alpha b A0 Kpop : Real) (hb : 0 < b)
    (hMom : ∀ h, h ∈ PopGood -> ∀ j t, t ∈ Icc (a j) (btime j) ->
      Integrable (fun path => Real.exp (norm (sourcePopulationPathEval path 1 j t) ^ alpha /
        (sourcePopulationFlowFactor alpha * b ^ alpha))) (law h) ∧
      (∫ path, Real.exp (norm (sourcePopulationPathEval path 1 j t) ^ alpha /
        (sourcePopulationFlowFactor alpha * b ^ alpha)) ∂ law h) ≤ A0 * Real.exp (b ^ (-alpha)) ∧
      (law h).map (fun path => sourcePopulationPathEval path 1 j t) ∈ sourceMomentClass alpha Kpop) :
    ∀ᵐ h ∂ rho, h ∈ PopGood ->
      (∀ᵐ path ∂ characteristicKernel mu0 Phi h, path ∈ sourceReferencePathLipschitz B) ∧
      ∀ j t, t ∈ Icc (a j) (btime j) ->
        (characteristicKernel mu0 Phi h).map (fun path => sourceReferencePathEval path j t) ∈
          sourceMomentClass alpha Kpop ∧
        Integrable (fun x : EuclideanSpace Real (Fin d) =>
          Real.exp ((sourcePopulationFlowFactor alpha)⁻¹ * (norm x / b)^alpha))
          ((characteristicKernel mu0 Phi h).map (fun path => sourceReferencePathEval path j t)) ∧
        (∫ x, Real.exp ((sourcePopulationFlowFactor alpha)⁻¹ * (norm x / b)^alpha)
          ∂ (characteristicKernel mu0 Phi h).map (fun path => sourceReferencePathEval path j t)) ≤
          A0 * Real.exp (b ^ (-alpha)) := by
  have hf : Measurable (fun x : EuclideanSpace Real (Fin d) =>
      Real.exp (norm x ^ alpha / (sourcePopulationFlowFactor alpha * b ^ alpha))) :=
    ((measurable_norm.pow_const alpha).div_const _).exp
  have hscalar (x : EuclideanSpace Real (Fin d)) :
      (sourcePopulationFlowFactor alpha)⁻¹ * (norm x / b)^alpha =
        norm x ^ alpha / (sourcePopulationFlowFactor alpha * b ^ alpha) := by
    rw [Real.div_rpow (norm_nonneg _) hb.le]
    ring
  filter_upwards [hIdent,hSupport] with h hid hs
  intro hh
  refine ⟨hs, ?_⟩
  intro j t ht
  have hmapKernel : (law.map (fun p => p 1)) h = (law h).map (fun p => p 1) := by
    ext s hs
    rw [Kernel.map_apply' _ (measurable_pi_apply 1) _ hs,
      Measure.map_apply (measurable_pi_apply 1) hs]
  have hEvalLaw : (characteristicKernel mu0 Phi h).map (fun path => sourceReferencePathEval path j t) =
      (law h).map (fun path => sourcePopulationPathEval path 1 j t) := by
    have hreference : Measurable (fun path : SourcePopulationPathSpace J d a btime => path 1) :=
      measurable_pi_apply 1
    rw [← hid, hmapKernel, Measure.map_map (sourceReferencePathEval_measurable j t) hreference]
    rfl
  have hv := hMom h hh j t ht
  have hi := (integrable_map_measure hf.aestronglyMeasurable
    (sourcePopulationPathEval_measurable 1 j t).aemeasurable).mpr hv.1
  have hbound : (∫ x, Real.exp (norm x ^ alpha / (sourcePopulationFlowFactor alpha * b ^ alpha))
      ∂ (law h).map (fun path => sourcePopulationPathEval path 1 j t)) ≤
      A0 * Real.exp (b ^ (-alpha)) := by
    rw [integral_map (sourcePopulationPathEval_measurable 1 j t).aemeasurable hf.aestronglyMeasurable]
    exact hv.2.1
  rw [hEvalLaw]
  exact ⟨hv.2.2, by simpa only [hscalar] using hi, by simpa only [hscalar] using hbound⟩
end PaperFormalization.Manuscript
