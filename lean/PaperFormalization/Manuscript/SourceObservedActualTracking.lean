import PaperFormalization.Manuscript.SourceActualTracking
import PaperFormalization.Manuscript.SourceObservedTrackingSchedule

/-! # Actual tracking on the joint original-law observed event

M13o declarations checked with the pinned toolchain; see verification/latest.json.
Covariance residual inputs are obtained from observed iid covariance views,
not assumed separately. The covariance and Gaussian histories remain distinct.
The exact prescribed covariance scale is substituted into the literal radius.
The event theorem below gives a conditional deterministic implication on a
measurable original-law event. Its budget does NOT pay for Gamma labels,
population eligibility, anti-spikiness, curvature/smallness, or law identification.
-/
open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal Topology ProbabilityTheory Matrix.Norms.Frobenius
set_option maxSynthPendingDepth 8
namespace PaperFormalization.Manuscript
open Continuous Piecewise

variable {Ω : Type*} [MeasurableSpace Ω] {N d : ℕ}
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

variable (c C g p q K D alpha C3 : ℝ) (φ : ∀ n, EuclideanSpace ℝ (Fin d) → H n)
  (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (hD : 1 ≤ D)
  (halpha : 0 < alpha) (hφ : ∀ n, ContDiff ℝ 2 (φ n))
  (hgrowth : ∀ n z k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) z‖ ≤
    featureGrowth C g q n*(1+‖z‖^(n+1-k)))
  (hthirdφ : ∀ n z, DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ (φ n))) z)
  (hgrowth₃ : ∀ n z, ‖iteratedFDeriv ℝ 3 (φ n) z‖ ≤ featureGrowth C g q n*(1+‖z‖^(n+1-3)))
  (G : lp H 2 → ℝ) (U : Set (lp H 2)) (hU : IsOpen U)
  (hSU : measureMomentRegion (sourceWeightedFeatureMap c p φ) (sourceMomentClass alpha K) D ⊆ U)
  (hG : ContDiffOn ℝ 3 G U)
  (hthirdG : ∀ theta ∈ measureMomentRegion (sourceWeightedFeatureMap c p φ)
    (sourceMomentClass alpha K) D, ‖iteratedFDeriv ℝ 3 G theta‖ ≤ C3)
  (L : ℝ≥0) (hL : (L : ℝ) = sourceComparisonEnvelope c C g p q K D alpha C3 φ G)

include hc hC hp hq hK hD halpha hφ hgrowth hthirdφ hgrowth₃ hthirdG hL

set_option maxHeartbeats 2400000 in
/-- Instantiate the actual-path tracking theorem using the two literal observed
event outputs and explicit covariance sample/pre-law identifications. -/
theorem actual_source_tracking_of_observed_events
    (μ : Measure Ω) [IsProbabilityMeasure μ] (J : ℕ) (tau eta : ℕ → ℝ) (T A_sp : ℝ)
    (B : ℝ≥0) (hN : 0 < N) (htau0 : tau 0 = 0)
    (htime : ∀ k < J, tau k < tau (k+1)) (hT : tau J ≤ T)
    (P : SourceTrackingPaths (N := N) μ J tau T B c p K D alpha A_sp φ G)
    (delta pTotal : ℝ)
    (hGammaLabels : ∀ k ≤ J, ∀ t ∈ Icc (tau k) (if k < J then tau (k+1) else T),
      weightedSampleResidual (featureResidualWeight c p L) φ
        (fun n => ∫ ω, φ n (P.Zbranch k ω t) ∂μ) (fun i => P.Ybranch k t i) ≤ delta)
    {O : Type*} [MeasurableSpace O] (ν : Measure O)
    (SC VC SJ VJ : Fin J → Type*)
    [∀ j, MeasurableSpace (SC j)] [∀ j, MeasurableSpace (VC j)]
    [∀ j, MeasurableSpace (SJ j)] [∀ j, MeasurableSpace (VJ j)]
    (covView : ∀ j, SourceObservedCovarianceView N d alpha K ν (SC j) (VC j))
    (jumpView : ∀ j, SourceObservedJumpView c p K D alpha φ G U hU hSU
      (hG.of_le (by norm_num)) hN ν (SJ j) (VJ j)) (ω : O)
    (hCovEvent : let F := sourceWeightedFeatureMap c p φ
      ∀ j, let z := (covView j).observation ω
        z.1 ∈ (covView j).PopGood →
        matrixNuclearValue (populationCovarianceResidual ((covView j).κ z.1) ((covView j).X z)
          (fun x => stackedKernelMatrix (fun i =>
            actualMomentKernelMatrix F G (∫ y, F y ∂(covView j).κ z.1) ((covView j).X z i) x))) / N ≤
          sourcePrescribedCovarianceEnvelope J N d c C g p q alpha K L pTotal)
    (hJumpGood : ∀ j, (jumpView j).observation ω ∉ actualSourceJumpFailure c C g p q D φ G L
      (jumpView j).PopGood (fun h => (jumpView j).κ h) (jumpView j).X (jumpView j).Y
      (jumpView j).Xpost (jumpView j).Ypost (jumpView j).eta (pTotal/(8*((J : ℝ)+1))))
    (hCovPopGood : ∀ j, ((covView j).observation ω).1 ∈ (covView j).PopGood)
    (hCovSample : ∀ j, (covView j).X ((covView j).observation ω) = (fun i => P.preY j i))
    (hCovPreLaw : ∀ j, (covView j).κ ((covView j).observation ω).1 =
      μ.map (fun x => P.Zbranch j x (tau (j+1))))
    (hPopGood : ∀ j, ((jumpView j).observation ω).1 ∈ (jumpView j).PopGood)
    (hPreX : ∀ j, (jumpView j).X ((jumpView j).observation ω).1 = P.preX j)
    (hPreY : ∀ j, (jumpView j).Y ((jumpView j).observation ω).1 = P.preY j)
    (hPostX : ∀ j, (jumpView j).Xpost ((jumpView j).observation ω).1 ((jumpView j).observation ω).2 = P.X (tau (j+1)))
    (hPostY : ∀ j, (jumpView j).Ypost ((jumpView j).observation ω).1 ((jumpView j).observation ω).2 = P.Y (tau (j+1)))
    (hPreLaw : ∀ j, (jumpView j).κ ((jumpView j).observation ω).1 =
      μ.map (fun ω => P.Zbranch j ω (tau (j+1))))
    (hEta : ∀ j, (jumpView j).eta = eta j)
    (hAsp : 1 ≤ A_sp) :
    let deltaTilde := sourcePrescribedCovarianceEnvelope J N d c C g p q alpha K L pTotal
    let F := sourceWeightedFeatureMap c p φ
    let r := fun t => ‖P.X t-P.Y t‖/Real.sqrt N
    let kappa := fun t => rayleighInf (sampledMomentHessian F G
      (∫ z, F z ∂(μ.map (fun ω => P.Z ω t))) (P.Y t))
    let cD := featureDisplacementLambda c C g p q D L+(2+A_sp)*(L : ℝ)
    let A := sourceJumpCoefficient d (featureDisplacementLambda c C g p q D L) L *
      sourceGaussianDeviation (pTotal/(8*((J : ℝ)+1)))
    T * (delta + cD * (2 * jumpAmplification (sourceJumpError A eta) J *
      sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A J T)) ≤ 1 / 4 →
    (∀ t ∈ Icc 0 T, r t ≤
      Real.exp (1 / 4) * jumpAmplification (sourceJumpError A eta) J *
        sourceCurvatureEnvelope kappa tau eta delta deltaTilde A J t) ∧
    (sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A J T = 0 →
      ∀ t ∈ Icc 0 T, P.X t = P.Y t) ∧
    (∀ k < J, norm (P.preX k-P.preY k) / Real.sqrt N ≤
      Real.exp (1/4) * jumpAmplification (sourceJumpError A eta) J *
        sourceCurvatureEnvelope kappa tau eta delta deltaTilde A k (tau (k+1))) ∧
    (sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A J T = 0 →
      ∀ k < J, P.preX k = P.preY k) := by
  have hCovPre : ∀ k < J,
      let F := sourceWeightedFeatureMap c p φ
      let muPre := μ.map (fun ω => P.Zbranch k ω (tau (k+1)))
      matrixNuclearValue (populationCovarianceResidual muPre (fun i => P.preY k i)
        (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix F G
          (∫ z, F z ∂muPre) (P.preY k i) z))) / N ≤
        sourcePrescribedCovarianceEnvelope J N d c C g p q alpha K L pTotal := by
    intro k hk
    let j : Fin J := ⟨k,hk⟩
    have hv := hCovEvent j (hCovPopGood j)
    rw [hCovPreLaw j, hCovSample j] at hv
    exact hv
  exact actual_source_tracking_bound
    c C g p q K D alpha C3 φ hc hC hp hq hK hD halpha
    hφ hgrowth hthirdφ hgrowth₃ G U hU hSU hG hthirdG L hL
    μ J tau eta T A_sp B hN htau0 htime hT P delta
    (sourcePrescribedCovarianceEnvelope J N d c C g p q alpha K L pTotal) pTotal
    hGammaLabels hCovPre ν SJ VJ jumpView ω hJumpGood hPopGood
    hPreX hPreY hPostX hPostY hPreLaw hEta hAsp

set_option maxHeartbeats 2600000 in
/-- One original-law event with the exact combined budget. For EVERY primitive
actual-path realization compatible with its observations, the source hypotheses
imply both right/post and left/pre tracking and both zero-envelope identities.
The universally quantified hypotheses are NOT declared probabilistic events. -/
theorem exists_source_actual_tracking_on_observed_event
    {O : Type*} [MeasurableSpace O] (J : ℕ) (hN : 0 < N)
    (ν : Measure O) [IsProbabilityMeasure ν]
    (SC VC SJ VJ : Fin J → Type*)
    [∀ j, MeasurableSpace (SC j)] [∀ j, MeasurableSpace (VC j)]
    [∀ j, MeasurableSpace (SJ j)] [∀ j, MeasurableSpace (VJ j)]
    (covView : ∀ j, SourceObservedCovarianceView N d alpha K ν (SC j) (VC j))
    (jumpView : ∀ j, SourceObservedJumpView c p K D alpha φ G U hU hSU
      (hG.of_le (by norm_num)) hN ν (SJ j) (VJ j))
    (delta pTotal : ℝ) (hpTotal : 0 < pTotal) (hpTotal1 : pTotal < 1)
    (Model : O → Prop) (hModel : ∀ᵐ ω ∂ν, Model ω) :
    ∃ Good : Set O, MeasurableSet Good ∧
      ν.real Goodᶜ ≤ ((J : ℝ) / ((J : ℝ) + 1)) * (5 * pTotal / 32) ∧
      ν.real Goodᶜ < pTotal / 4 ∧
      ∀ ω ∈ Good, Model ω ∧
        ∀ (μ : Measure Ω) [IsProbabilityMeasure μ] (tau eta : ℕ → ℝ) (T A_sp : ℝ)
          (B : ℝ≥0) (htau0 : tau 0 = 0)
          (htime : ∀ k < J, tau k < tau (k+1)) (hT : tau J ≤ T)
          (P : SourceTrackingPaths (N := N) μ J tau T B c p K D alpha A_sp φ G)
          (hGammaLabels : ∀ k ≤ J, ∀ t ∈ Icc (tau k) (if k < J then tau (k+1) else T),
            weightedSampleResidual (featureResidualWeight c p L) φ
              (fun n => ∫ ω, φ n (P.Zbranch k ω t) ∂μ) (fun i => P.Ybranch k t i) ≤ delta)
          (hCovPopGood : ∀ j, ((covView j).observation ω).1 ∈ (covView j).PopGood)
          (hCovSample : ∀ j, (covView j).X ((covView j).observation ω) = (fun i => P.preY j i))
          (hCovPreLaw : ∀ j, (covView j).κ ((covView j).observation ω).1 =
            μ.map (fun x => P.Zbranch j x (tau (j+1))))
          (hPopGood : ∀ j, ((jumpView j).observation ω).1 ∈ (jumpView j).PopGood)
          (hPreX : ∀ j, (jumpView j).X ((jumpView j).observation ω).1 = P.preX j)
          (hPreY : ∀ j, (jumpView j).Y ((jumpView j).observation ω).1 = P.preY j)
          (hPostX : ∀ j, (jumpView j).Xpost ((jumpView j).observation ω).1 ((jumpView j).observation ω).2 = P.X (tau (j+1)))
          (hPostY : ∀ j, (jumpView j).Ypost ((jumpView j).observation ω).1 ((jumpView j).observation ω).2 = P.Y (tau (j+1)))
          (hPreLaw : ∀ j, (jumpView j).κ ((jumpView j).observation ω).1 =
            μ.map (fun ω => P.Zbranch j ω (tau (j+1))))
          (hEta : ∀ j, (jumpView j).eta = eta j)
          (hAsp : 1 ≤ A_sp),
          let deltaTilde := sourcePrescribedCovarianceEnvelope J N d c C g p q alpha K L pTotal
          let F := sourceWeightedFeatureMap c p φ
          let r := fun t => ‖P.X t-P.Y t‖/Real.sqrt N
          let kappa := fun t => rayleighInf (sampledMomentHessian F G
            (∫ z, F z ∂(μ.map (fun ω => P.Z ω t))) (P.Y t))
          let cD := featureDisplacementLambda c C g p q D L+(2+A_sp)*(L : ℝ)
          let A := sourceJumpCoefficient d (featureDisplacementLambda c C g p q D L) L *
            sourceGaussianDeviation (pTotal/(8*((J : ℝ)+1)))
          T * (delta + cD * (2 * jumpAmplification (sourceJumpError A eta) J *
            sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A J T)) ≤ 1 / 4 →
          (∀ t ∈ Icc 0 T, r t ≤
            Real.exp (1 / 4) * jumpAmplification (sourceJumpError A eta) J *
              sourceCurvatureEnvelope kappa tau eta delta deltaTilde A J t) ∧
          (sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A J T = 0 →
            ∀ t ∈ Icc 0 T, P.X t = P.Y t) ∧
          (∀ k < J, norm (P.preX k-P.preY k) / Real.sqrt N ≤
            Real.exp (1/4) * jumpAmplification (sourceJumpError A eta) J *
              sourceCurvatureEnvelope kappa tau eta delta deltaTilde A k (tau (k+1))) ∧
          (sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A J T = 0 →
            ∀ k < J, P.preX k = P.preY k) := by
  obtain ⟨Good, hGood, hbudget, hstrict, hvalid⟩ :=
    exists_source_observed_tracking_schedule_event
      J c C g p q K D alpha C3 φ hc hC hp hq halpha hK hD hφ hgrowth
      G U hU hSU hG hthirdG L hL hN ν SC VC SJ VJ covView jumpView
      pTotal hpTotal hpTotal1 Model hModel
  refine ⟨Good, hGood, hbudget, hstrict, ?_⟩
  intro ω hω
  refine ⟨(hvalid ω hω).1, ?_⟩
  intro μ hμ tau eta T A_sp B htau0 htime hT P hGammaLabels
    hCovPopGood hCovSample hCovPreLaw hPopGood hPreX hPreY hPostX hPostY hPreLaw hEta hAsp
  letI := hμ
  exact actual_source_tracking_of_observed_events
    c C g p q K D alpha C3 φ hc hC hp hq hK hD halpha
    hφ hgrowth hthirdφ hgrowth₃ G U hU hSU hG hthirdG L hL
    μ J tau eta T A_sp B hN htau0 htime hT P delta pTotal hGammaLabels
    ν SC VC SJ VJ covView jumpView ω (hvalid ω hω).2.1 (hvalid ω hω).2.2
    hCovPopGood hCovSample hCovPreLaw hPopGood hPreX hPreY hPostX hPostY hPreLaw hEta hAsp
end PaperFormalization.Manuscript
