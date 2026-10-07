import PaperFormalization.Manuscript.SourceFreshInnovationLaw
import PaperFormalization.Manuscript.SourceAuxiliaryTower

/-! # Fresh innovations at the actual finite auxiliary histories

M13q verified unit (see CODEX_HANDOFF_M13Q.md). The history at level n contains the selected
original prehistory and exactly the first n independent auxiliary coordinates.
This is constructed on the existing universe-correct auxiliary tower. Neither
current/future population innovations nor the current whitening auxiliary are
added to that history. Its fresh-independence proof is an induction, not a new
conditional-law field in a model record.
-/
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
namespace PaperFormalization.Manuscript
variable {O S W A : Type*} [MeasurableSpace O] [MeasurableSpace S]
  [MeasurableSpace W] [MeasurableSpace A]

/-- Lift an original prehistory together with precisely the past auxiliaries. -/
def sourceAuxiliaryHistory (history : O -> S) :
    (n : Nat) -> SourceAuxiliarySpace O A n -> SourceAuxiliarySpace S A n
  | 0, z => ULift.up (history z.down)
  | n+1, z => (sourceAuxiliaryHistory history n z.1,z.2)

theorem sourceAuxiliaryHistory_measurable
    (history : O -> S) (hH : Measurable history) (n : Nat) :
    Measurable (sourceAuxiliaryHistory (A := A) history n) := by
  induction n with
  | zero => exact measurable_up.comp (hH.comp measurable_down)
  | succ n ih => exact (ih.comp measurable_fst).prodMk measurable_snd

/-- Reading the population prefix from the enlarged history never reveals a
new original outcome. The identity is pointwise, not only almost surely. -/
theorem sourceAuxiliaryHistory_original
    (history : O -> S) (n : Nat) (z : SourceAuxiliarySpace O A n) :
    sourceAuxiliaryOriginal n (sourceAuxiliaryHistory history n z) =
      history (sourceAuxiliaryOriginal n z) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih z.1

set_option backward.isDefEq.respectTransparency false in
/-- Inductively preserve fresh-innovation independence at every auxiliary
stage. Each induction step adds an independent PAST auxiliary only. -/
theorem source_auxiliary_history_fresh_independent
    (nu : Measure O) [IsProbabilityMeasure nu]
    (lambdaA : Measure A) [IsProbabilityMeasure lambdaA]
    (history : O -> S) (innovation : O -> W)
    (hH : Measurable history) (hW : Measurable innovation)
    (hind : IndepFun history innovation nu) (n : Nat) :
    IndepFun (sourceAuxiliaryHistory (A := A) history n)
      (innovation ∘ sourceAuxiliaryOriginal n) (sourceAuxiliaryMeasure nu lambdaA n) := by
  induction n with
  | zero =>
    have hbase := source_independence_pullback nu (sourceAuxiliaryMeasure nu lambdaA 0)
      (sourceAuxiliaryOriginal (A := A) 0) (sourceAuxiliaryOriginal_preserving nu lambdaA 0)
      history innovation hH hW hind
    simpa only [sourceAuxiliaryHistory,sourceAuxiliaryOriginal,Function.comp_def,id_eq] using
      hbase.comp measurable_up measurable_id
  | succ n ih =>
    have hn := source_fresh_independent_after_auxiliary (sourceAuxiliaryMeasure nu lambdaA n)
      lambdaA (sourceAuxiliaryHistory (A := A) history n)
      (innovation ∘ sourceAuxiliaryOriginal n)
      (sourceAuxiliaryHistory_measurable history hH n)
      (hW.comp (sourceAuxiliaryOriginal_preserving nu lambdaA n).measurable) ih
    change IndepFun
      (fun z : SourceAuxiliarySpace O A n × A => (sourceAuxiliaryHistory history n z.1,z.2))
      (fun z => innovation (sourceAuxiliaryOriginal n z.1))
      ((sourceAuxiliaryMeasure nu lambdaA n).prod lambdaA)
    simpa only [Function.comp_def] using hn

/-- The innovation marginal is exactly the ORIGINAL one at every stage. -/
theorem source_auxiliary_innovation_marginal
    (nu : Measure O) [IsProbabilityMeasure nu]
    (lambdaA : Measure A) [IsProbabilityMeasure lambdaA]
    (innovation : O -> W) (hW : Measurable innovation) (n : Nat) :
    (sourceAuxiliaryMeasure nu lambdaA n).map (innovation ∘ sourceAuxiliaryOriginal n) =
      nu.map innovation := by
  rw [← Measure.map_map hW (sourceAuxiliaryOriginal_preserving nu lambdaA n).measurable,
    (sourceAuxiliaryOriginal_preserving nu lambdaA n).map_eq]

/-- The original GP finite-evaluation law now applies at the explicit enlarged
history, by the proven fresh independence and unchanged innovation marginal.
This supplies the raw Gaussian premise of the one-step source construction. -/
theorem source_auxiliary_history_fresh_gaussian
    {I : Type*} [Fintype I] [DecidableEq I]
    (nu : Measure O) [IsProbabilityMeasure nu]
    (lambdaA : Measure A) [IsProbabilityMeasure lambdaA]
    (lambdaW : Measure W) [IsProbabilityMeasure lambdaW]
    (history : O -> S) (innovation : O -> W)
    (hH : Measurable history) (hW : Measurable innovation)
    (hind : IndepFun history innovation nu) (hlaw : nu.map innovation = lambdaW)
    (n : Nat)
    (evaluate : SourceAuxiliarySpace S A n -> W -> EuclideanSpace Real I)
    (hEval : Measurable (fun z : SourceAuxiliarySpace S A n × W => evaluate z.1 z.2))
    (Cov : SourceAuxiliarySpace S A n -> Matrix I I Real)
    (hField : ∀ᵐ h ∂ (sourceAuxiliaryMeasure nu lambdaA n).map (sourceAuxiliaryHistory history n),
      lambdaW.map (evaluate h) = multivariateGaussian 0 (Cov h)) :
    ∀ᵐ h ∂ (sourceAuxiliaryMeasure nu lambdaA n).map (sourceAuxiliaryHistory history n),
      condDistrib (fun z => evaluate (sourceAuxiliaryHistory history n z)
        (innovation (sourceAuxiliaryOriginal n z))) (sourceAuxiliaryHistory history n)
        (sourceAuxiliaryMeasure nu lambdaA n) h = multivariateGaussian 0 (Cov h) := by
  apply source_fresh_evaluation_gaussian (sourceAuxiliaryMeasure nu lambdaA n) lambdaW
    (sourceAuxiliaryHistory (A := A) history n) (innovation ∘ sourceAuxiliaryOriginal n)
    (sourceAuxiliaryHistory_measurable history hH n)
    (hW.comp (sourceAuxiliaryOriginal_preserving nu lambdaA n).measurable)
    (source_auxiliary_history_fresh_independent nu lambdaA history innovation hH hW hind n)
    ((source_auxiliary_innovation_marginal nu lambdaA innovation hW n).trans hlaw)
    evaluate hEval Cov hField
end PaperFormalization.Manuscript
