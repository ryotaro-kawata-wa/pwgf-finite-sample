import PaperFormalization.Manuscript.SourceActualTrackingInputs
import PaperFormalization.Manuscript.SourceTrackingAllCasesWithPre

/-! # Actual normalized particle tracking from primitive paths

M13o declarations checked with the pinned toolchain. The current build and
axiom audit are recorded in verification/latest.json.

Compose the actual-path adapter with the all-cases scalar comparison theorem.
No scalar AC, integrability, drift, jump, or tracking estimate is a hypothesis.
The only additions to the adapter's assumptions are the manuscript condition
A_sp >= 1 and its literal nonlinear smallness condition. Coefficient and
residual-envelope nonnegativity are derived, not added as assumptions.

The residual-event bounds and observed-view/pre-law identities remain explicit.
This theorem does not construct the original stochastic model and does not
claim a high-probability result. Zero envelope, no jumps, and a zero-length
final branch are not excluded. The conclusions include actual right/post values and left/pre traces,
with only strictly earlier jumps in the pretrace forcing envelope.
-/
open Matrix MeasureTheory Set Filter
open scoped BigOperators NNReal Topology Matrix.Norms.Frobenius
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

set_option maxHeartbeats 2000000 in
/-- Under the primitive actual-path and event/view hypotheses, the literal
source smallness condition yields normalized particle tracking. A zero actual
envelope supremum forces equality of the actual configurations at every time.
The extra anti-spikiness parameter condition is the manuscript's A_sp >= 1. -/
theorem actual_source_tracking_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ] (J : ℕ) (tau eta : ℕ → ℝ) (T A_sp : ℝ)
    (B : ℝ≥0) (hN : 0 < N) (htau0 : tau 0 = 0)
    (htime : ∀ k < J, tau k < tau (k+1)) (hT : tau J ≤ T)
    (P : SourceTrackingPaths (N := N) μ J tau T B c p K D alpha A_sp φ G)
    (delta deltaTilde pTotal : ℝ)
    (hGammaLabels : ∀ k ≤ J, ∀ t ∈ Icc (tau k) (if k < J then tau (k+1) else T),
      weightedSampleResidual (featureResidualWeight c p L) φ
        (fun n => ∫ ω, φ n (P.Zbranch k ω t) ∂μ) (fun i => P.Ybranch k t i) ≤ delta)
    (hCovPre : ∀ k < J,
      let F := sourceWeightedFeatureMap c p φ
      let muPre := μ.map (fun ω => P.Zbranch k ω (tau (k+1)))
      matrixNuclearValue (populationCovarianceResidual muPre (fun i => P.preY k i)
        (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix F G
          (∫ z, F z ∂muPre) (P.preY k i) z))) / N ≤ deltaTilde)
    {O : Type*} [MeasurableSpace O] (ν : Measure O)
    (S V : Fin J → Type*) [∀ j, MeasurableSpace (S j)] [∀ j, MeasurableSpace (V j)]
    (view : ∀ j, SourceObservedJumpView c p K D alpha φ G U hU hSU
      (hG.of_le (by norm_num)) hN ν (S j) (V j)) (ω : O)
    (hJumpGood : ∀ j, (view j).observation ω ∉ actualSourceJumpFailure c C g p q D φ G L
      (view j).PopGood (fun h => (view j).κ h) (view j).X (view j).Y
      (view j).Xpost (view j).Ypost (view j).eta (pTotal/(8*((J : ℝ)+1))))
    (hPopGood : ∀ j, ((view j).observation ω).1 ∈ (view j).PopGood)
    (hPreX : ∀ j, (view j).X ((view j).observation ω).1 = P.preX j)
    (hPreY : ∀ j, (view j).Y ((view j).observation ω).1 = P.preY j)
    (hPostX : ∀ j, (view j).Xpost ((view j).observation ω).1 ((view j).observation ω).2 = P.X (tau (j+1)))
    (hPostY : ∀ j, (view j).Ypost ((view j).observation ω).1 ((view j).observation ω).2 = P.Y (tau (j+1)))
    (hPreLaw : ∀ j, (view j).κ ((view j).observation ω).1 =
      μ.map (fun ω => P.Zbranch j ω (tau (j+1))))
    (hEta : ∀ j, (view j).eta = eta j)
    (hAsp : 1 ≤ A_sp) :
    let F := sourceWeightedFeatureMap c p φ
    let r := fun t => ‖P.X t-P.Y t‖/Real.sqrt N
    let kappa := fun t => rayleighInf (sampledMomentHessian F G
      (∫ z, F z ∂(μ.map (fun ω => P.Z ω t))) (P.Y t))
    let cD := featureDisplacementLambda c C g p q D L+(2+A_sp)*(L : ℝ)
    let A := sourceJumpCoefficient d (featureDisplacementLambda c C g p q D L) L *
      sourceGaussianDeviation (pTotal/(8*((J : ℝ)+1)))
    T * (delta + cD * (2 * jumpAmplification (sourceJumpError A eta) J *
      sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A J T)) ≤ 1 / 4 ->
    (∀ t ∈ Icc 0 T, r t ≤
      Real.exp (1 / 4) * jumpAmplification (sourceJumpError A eta) J *
        sourceCurvatureEnvelope kappa tau eta delta deltaTilde A J t) ∧
    (sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A J T = 0 ->
      ∀ t ∈ Icc 0 T, P.X t = P.Y t) ∧
    (∀ k < J, norm (P.preX k-P.preY k) / Real.sqrt N ≤
      Real.exp (1/4) * jumpAmplification (sourceJumpError A eta) J *
        sourceCurvatureEnvelope kappa tau eta delta deltaTilde A k (tau (k+1))) ∧
    (sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A J T = 0 →
      ∀ k < J, P.preX k = P.preY k) := by
  let F := sourceWeightedFeatureMap c p φ
  let r := fun t => ‖P.X t-P.Y t‖/Real.sqrt N
  let pre := fun k => ‖P.preX k-P.preY k‖/Real.sqrt N
  let kappa := fun t => rayleighInf (sampledMomentHessian F G
    (∫ z, F z ∂(μ.map (fun ω => P.Z ω t))) (P.Y t))
  let Gamma := momentResidual (featureResidualWeight c p L)
    (fun n t => finiteFeatureMean (fun i => φ n (P.Y t i)))
    (fun n t => ∫ z, φ n z ∂(μ.map (fun ω => P.Z ω t)))
  let muPre := fun k => μ.map (fun ω => P.Zbranch k ω (tau (k+1)))
  let GammaPre := fun k => momentResidual (featureResidualWeight c p L)
    (fun n _ => finiteFeatureMean (fun i => φ n (P.preY k i))) (fun n _ => ∫ z, φ n z ∂muPre k) 0
  let GammaTildePre := fun k => matrixNuclearValue (populationCovarianceResidual (muPre k) (fun i => P.preY k i)
    (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix F G (∫ z, F z ∂muPre k) (P.preY k i) z))) / N
  let cD := featureDisplacementLambda c C g p q D L+(2+A_sp)*(L : ℝ)
  let A := sourceJumpCoefficient d (featureDisplacementLambda c C g p q D L) L *
    sourceGaussianDeviation (pTotal/(8*((J : ℝ)+1)))
  change
    T * (delta + cD * (2 * jumpAmplification (sourceJumpError A eta) J *
      sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A J T)) ≤ 1 / 4 ->
    (∀ t ∈ Icc 0 T, r t ≤
      Real.exp (1 / 4) * jumpAmplification (sourceJumpError A eta) J *
        sourceCurvatureEnvelope kappa tau eta delta deltaTilde A J t) ∧
    (sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A J T = 0 ->
      ∀ t ∈ Icc 0 T, P.X t = P.Y t) ∧
    (∀ k < J, norm (P.preX k-P.preY k) / Real.sqrt N ≤
      Real.exp (1/4) * jumpAmplification (sourceJumpError A eta) J *
        sourceCurvatureEnvelope kappa tau eta delta deltaTilde A k (tau (k+1))) ∧
    (sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A J T = 0 →
      ∀ k < J, P.preX k = P.preY k)
  intro hsmall

  -- These nine analytic inputs are conclusions of the actual model adapter.
  have hinputs := actual_source_tracking_inputs
    c C g p q K D alpha C3 φ hc hC hp hq hK hD halpha
    hφ hgrowth hthirdφ hgrowth₃ G U hU hSU hG hthirdG L hL
    μ J tau eta T A_sp B hN htau0 htime hT P
    delta deltaTilde pTotal hGammaLabels hCovPre ν S V view ω
    hJumpGood hPopGood hPreX hPreY hPostX hPostY hPreLaw hEta
  rcases hinputs with
    ⟨hbranch, hfinal, hkappa, hGamma, hGammaBounds, hpre,
      hdrift, hjump, hzero⟩

  -- The schedule includes 0 even when J = 0 or T = 0.
  have htauJ : 0 ≤ tau J := by
    rw [← htau0]
    exact time_mono_prefix tau J (fun k hk => (htime k hk).le)
      0 J (Nat.zero_le J) le_rfl
  have hT0 : 0 ≤ T := htauJ.trans hT
  have hGamma0 := hGammaBounds 0 (⟨le_rfl, hT0⟩ : 0 ∈ Icc 0 T)
  have hdelta : 0 ≤ delta := hGamma0.1.trans hGamma0.2

  -- Literal coefficients; no independent sign or coefficient-bound premise.
  have hLambda : 0 ≤ featureDisplacementLambda c C g p q D L :=
    featureDisplacementLambda_nonneg c C g p q D L hC (by linarith)
  have hcD : 0 ≤ cD := by
    dsimp only [cD]
    exact add_nonneg hLambda (mul_nonneg (by linarith) L.coe_nonneg)
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      ((by norm_num : (0 : ℝ) ≤ 1).trans
        (sourceJumpCoefficient_domination d
          (featureDisplacementLambda c C g p q D L) L hLambda L.coe_nonneg).1)
      ((by norm_num : (0 : ℝ) ≤ 1).trans
        (one_le_sourceGaussianDeviation (pTotal / (8 * ((J : ℝ) + 1)))))
  have hr : ∀ t ∈ Icc 0 T, 0 ≤ r t := by
    intro t _
    exact div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

  -- Split the all-branch drift without replacing the final closed branch by
  -- a positive-length interval. The same proof covers tau J = T.
  have hdriftBranches : ∀ k < J,
      ∀ᵐ t ∂volume.restrict (Ioo (tau k) (tau (k + 1))),
        deriv r t ≤ -kappa t * r t + cD * (r t)^2 + Gamma t * r t + Gamma t := by
    intro k hk
    simpa only [if_pos hk] using (hdrift k hk.le)
  have hdriftFinal : ∀ᵐ t ∂volume.restrict (Ioo (tau J) T),
      deriv r t ≤ -kappa t * r t + cD * (r t)^2 + Gamma t * r t + Gamma t := by
    simpa only [if_neg (Nat.lt_irrefl J)] using (hdrift J le_rfl)

  have htracking := source_tracking_all_cases_with_pre
    tau pre eta GammaPre GammaTildePre r kappa Gamma
    cD delta deltaTilde A T J htau0 htime hT hcD hdelta hA hsmall
    hbranch hkappa hGamma hr hGammaBounds hdriftBranches
    (fun k hk => (hpre k hk).2.2)
    (fun k hk => (hpre k hk).1)
    (fun k hk => (hpre k hk).2.1)
    hjump hfinal hdriftFinal hzero
  have hsqrtN : Real.sqrt (N : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (Nat.cast_pos.2 hN))
  have hconfig : ∀ x y : PiLp 2 (fun _ : Fin N => EuclideanSpace ℝ (Fin d)),
      norm (x-y) / Real.sqrt (N : ℝ) = 0 → x = y := by
    intro x y hxy
    have hn : norm (x-y) = 0 :=
      (div_eq_zero_iff.mp hxy).resolve_right hsqrtN
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  refine ⟨htracking.1.1, ?_, htracking.2.1, ?_⟩
  · intro hB t ht
    exact hconfig (P.X t) (P.Y t) (htracking.1.2 hB t ht)
  · intro hB k hk
    exact hconfig (P.preX k) (P.preY k) (htracking.2.2 hB k hk)

end PaperFormalization.Manuscript
