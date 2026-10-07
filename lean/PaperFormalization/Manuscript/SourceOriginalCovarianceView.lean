import PaperFormalization.Manuscript.CharacteristicEvaluation
import PaperFormalization.Manuscript.SourceObservedCovarianceSchedule
import PaperFormalization.Manuscript.PrehistoryPopulationEligibility
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-! # The covariance view is constructed from the original independent seeds

M13p verified unit (see CODEX_HANDOFF_M13P.md). The only probabilistic inputs are the original
initial iid law and independence of the entire initial array from the population
environment. The view's joint observation law, identical conditional marginals,
and conditional independence are proved internally. Eligibility is the genuine
extended exponential-moment event, not a sample-localization conditioning.
-/
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
namespace PaperFormalization.Manuscript

variable {O Env Seed : Type*} [MeasurableSpace O] [MeasurableSpace Env]
  [MeasurableSpace Seed] {N d : ℕ}

/-- A concrete covariance observation under the unchanged original measure.
`Phi` is the actual pre-jump characteristic map, not a conditional law input. -/
noncomputable def sourceOriginalCovarianceView
    (nu : Measure O) [IsProbabilityMeasure nu]
    (mu0 : Measure Seed) [IsProbabilityMeasure mu0]
    (environment : O -> Env) (initial : Fin N -> O -> Seed)
    (henv : Measurable environment) (hinit : ∀ i, Measurable (initial i))
    (hiid : iIndepFun initial nu)
    (hind : IndepFun environment (fun w i => initial i w) nu)
    (hlaw : ∀ i, nu.map (initial i) = mu0)
    (Phi : Env -> Seed -> EuclideanSpace ℝ (Fin d))
    (hPhi : Measurable (fun z : Env × Seed => Phi z.1 z.2))
    (alpha scale : ℝ) (halpha : 0 < alpha) (hscale : 0 < scale) :
    SourceObservedCovarianceView N d alpha
      (sourceExponentialMomentCoefficient alpha * scale) nu Env
      (Fin N -> EuclideanSpace ℝ (Fin d)) := by
  let single := characteristicKernel mu0 Phi
  let array := characteristicProductKernel (ι := Fin N) mu0 Phi
  have hs := characteristicKernel_properties mu0 Phi hPhi
  have ha := characteristicProductKernel_properties (ι := Fin N) mu0 Phi hPhi
  letI : IsMarkovKernel single := hs.1
  letI : IsMarkovKernel array := ha.1
  have hev := characteristicProductKernel_evaluation_laws (ι := Fin N) mu0 Phi hPhi
    (fun _ x => x) (measurable_snd : Measurable (fun z : Env × EuclideanSpace ℝ (Fin d) => z.2))
  refine {
    ρ := nu.map environment
    probability := Measure.isProbabilityMeasure_map henv.aemeasurable
    k := array
    markov := ha.1
    κ := single
    population_markov := hs.1
    PopGood := populationExponentialEligibility single alpha scale
    measurable_popGood := measurableSet_populationExponentialEligibility single alpha scale
    X := fun z => z.2
    measurable_X := fun i => (measurable_pi_apply i).comp measurable_snd
    source_model := ?_
    observation := fun w => (environment w, fun i => Phi (environment w) (initial i w))
    measurable_observation := henv.prodMk
      (measurable_pi_lambda _ (fun i => hPhi.comp (henv.prodMk (hinit i))))
    observation_law := independent_characteristic_joint_law nu mu0 environment initial
      henv hinit hiid hind hlaw Phi hPhi }
  filter_upwards with e
  intro he
  refine ⟨sourceMomentClass_of_populationExponentialEligibility single alpha scale
    halpha hscale e he, ?_, ?_⟩
  · intro i
    simpa only [Measure.map_id'] using (hev.2 e).2 i
  · exact (hev.2 e).1

/-- The actual observed reference cloud is the coordinatewise characteristic
image of the ORIGINAL initial array, pointwise, not just in distribution. -/
theorem sourceOriginalCovarianceView_sample
    (nu : Measure O) [IsProbabilityMeasure nu]
    (mu0 : Measure Seed) [IsProbabilityMeasure mu0]
    (environment : O -> Env) (initial : Fin N -> O -> Seed)
    (henv : Measurable environment) (hinit : ∀ i, Measurable (initial i))
    (hiid : iIndepFun initial nu)
    (hind : IndepFun environment (fun w i => initial i w) nu)
    (hlaw : ∀ i, nu.map (initial i) = mu0)
    (Phi : Env -> Seed -> EuclideanSpace ℝ (Fin d))
    (hPhi : Measurable (fun z : Env × Seed => Phi z.1 z.2))
    (alpha scale : ℝ) (halpha : 0 < alpha) (hscale : 0 < scale) (w : O) :
    let view := sourceOriginalCovarianceView nu mu0 environment initial henv hinit
      hiid hind hlaw Phi hPhi alpha scale halpha hscale
    view.X (view.observation w) = fun i => Phi (environment w) (initial i w) := rfl

/-- The pre-law is literally the seed pushforward; it is not an assumption
about two independently chosen conditional versions. -/
theorem sourceOriginalCovarianceView_preLaw
    (nu : Measure O) [IsProbabilityMeasure nu]
    (mu0 : Measure Seed) [IsProbabilityMeasure mu0]
    (environment : O -> Env) (initial : Fin N -> O -> Seed)
    (henv : Measurable environment) (hinit : ∀ i, Measurable (initial i))
    (hiid : iIndepFun initial nu)
    (hind : IndepFun environment (fun w i => initial i w) nu)
    (hlaw : ∀ i, nu.map (initial i) = mu0)
    (Phi : Env -> Seed -> EuclideanSpace ℝ (Fin d))
    (hPhi : Measurable (fun z : Env × Seed => Phi z.1 z.2))
    (alpha scale : ℝ) (halpha : 0 < alpha) (hscale : 0 < scale) (w : O) :
    let view := sourceOriginalCovarianceView nu mu0 environment initial henv hinit
      hiid hind hlaw Phi hPhi alpha scale halpha hscale
    view.κ (view.observation w).1 = mu0.map (Phi (environment w)) :=
  (characteristicKernel_properties mu0 Phi hPhi).2 (environment w)

end PaperFormalization.Manuscript
