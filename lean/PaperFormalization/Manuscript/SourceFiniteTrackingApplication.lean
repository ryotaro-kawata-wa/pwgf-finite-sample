import PaperFormalization.Manuscript.SourceFinalTrackingStatement
import PaperFormalization.Manuscript.SourceActualTracking

/-! # Invoke actual_source_tracking_bound on the constructed horizon paths
M13s verified unit; see CODEX_HANDOFF_M13S.md. This is the deterministic final invocation, not another
record assuming scalar AC/drift/jump or the desired comparison conclusion.
The stochastic assembly in SourceScheduledTrackingClosure supplies the event
certificates and views consumed here.
-/
open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal Topology ProbabilityTheory Matrix.Norms.Frobenius
namespace PaperFormalization.Manuscript
open Continuous Piecewise
variable {W O : Type*} [MeasurableSpace W] [MeasurableSpace O] {N d : Nat}
variable {H : Nat -> Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace Real (H n)] [∀ n, CompleteSpace (H n)]
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 12 in
set_option maxHeartbeats 10000000 in
/-- The actual finite history, not a free path record, satisfies all four
tracking conclusions on the original anti-spikiness and smallness restrictions. -/
theorem source_finite_horizon_tracking
    (c C g p q alpha K D scale C3 : Real)
    (phi : ∀ m, EuclideanSpace Real (Fin d) -> H m)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (halpha : 0 < alpha) (hK : 0 < K) (hD : 1 ≤ D)
    (hphi : ∀ m, ContDiff Real 2 (phi m))
    (hgrowth : ∀ m x k, k ≤ 2 -> norm (iteratedFDeriv Real k (phi m) x) ≤
      featureGrowth C g q m * (1 + norm x ^ (m+1-k)))
    (hthirdphi : ∀ m x, DifferentiableAt Real (fderiv Real (fderiv Real (phi m))) x)
    (hgrowth3 : ∀ m x, norm (iteratedFDeriv Real 3 (phi m) x) ≤
      featureGrowth C g q m * (1 + norm x ^ (m+1-3)))
    (G : lp H 2 -> Real) (U : Set (lp H 2)) (hU : IsOpen U)
    (hDomains : SourceAllMomentDomains (sourceWeightedFeatureMap c p phi) alpha U)
    (hG : ContDiffOn Real 3 G U)
    (hthirdG : ∀ theta, theta ∈ measureMomentRegion (sourceWeightedFeatureMap c p phi)
      (sourceMomentClass alpha K) D -> norm (iteratedFDeriv Real 3 G theta) ≤ C3)
    (L : NNReal) (hL : (L : Real) = sourceComparisonEnvelope c C g p q K D alpha C3 phi G)
    (mu0 : Measure (EuclideanSpace Real (Fin d))) [IsProbabilityMeasure mu0]
    (hN : 0 < N) (tau eta : Nat -> Real) (flowX flowY field)
    (J : Nat) (T : Real) (B : NNReal)
    (htau0 : tau 0 = 0) (htime : ∀ k, k < J -> tau k < tau (k+1)) (hT : tau J ≤ T)
    (h : Fin J -> W × SourceStepNormal N d) (u : SourceFiniteConfiguration N d)
    (hXstart : ∀ k x, flowX k (tau k) x = x)
    (hYstart : ∀ k past x, flowY k past (tau k) x = x)
    (delta deltaTilde pTotal : Real) (nu : Measure O)
    (S V : Fin J -> Type*) [∀ n, MeasurableSpace (S n)] [∀ n, MeasurableSpace (V n)]
    (view : ∀ n, SourceObservedJumpView c p K D alpha phi G U hU
      (hDomains K hK D hD) (hG.of_le (by norm_num)) hN nu (S n) (V n)) (omega : O) :
    let post := sourceActualFinitePost mu0 c p alpha phi G U hU hDomains (hG.of_le (by norm_num)) hN tau eta flowX flowY field
    let branches := sourceFiniteHorizonBranch post flowX flowY J h u
    let paths := sourceFiniteHorizonPath post flowX flowY tau J h u
    let Z := sourceFiniteReferenceBranch tau eta flowY field J h
    let F := sourceWeightedFeatureMap c p phi
    let kappa := fun t => rayleighInf (sampledMomentHessian F G
      (∫ x, F x ∂ mu0.map (fun u => sourceGlue tau J (fun k => Z k u) t)) ((paths t).2))
    let A := sourceJumpCoefficient d (featureDisplacementLambda c C g p q D L) L *
      sourceGaussianDeviation (pTotal/(8*((J : Real)+1)))
    SourceReferenceControl mu0 (fun j => Z j.val) (sourceScheduleLeft tau J) (sourceScheduleRight tau J T)
      B alpha K scale ->
    (∀ k, k ≤ J -> ∀ i, LipschitzOnWith B (fun t => (branches k t).1 i)
      (Icc (tau k) (if k < J then tau (k+1) else T))) ->
    (∀ k, k ≤ J -> ∀ i, LipschitzOnWith B (fun t => (branches k t).2 i)
      (Icc (tau k) (if k < J then tau (k+1) else T))) ->
    (∀ k, k ≤ J -> ∀ t, t ∈ Icc (tau k) (if k < J then tau (k+1) else T) ->
      ∀ i, norm ((branches k t).1 i) ≤ D ∧ norm ((branches k t).2 i) ≤ D) ->
    (∀ k, k ≤ J -> ∀ i,
      ∀ᵐ t ∂ volume.restrict (Ioo (tau k) (if k < J then tau (k+1) else T)),
        HasDerivAt (fun s => (branches k s).1 i) ((sourceExactEmpiricalDrift c p phi G (branches k t).1) i) t) ->
    (∀ k, k ≤ J -> ∀ i,
      ∀ᵐ t ∂ volume.restrict (Ioo (tau k) (if k < J then tau (k+1) else T)),
        HasDerivAt (fun s => (branches k s).2 i)
          ((frozenMomentConfigurationField
            (momentGradientField (fderiv Real F) (gradient G))
            (∫ x, F x ∂ mu0.map (fun u => Z k u t)) (branches k t).2) i) t) ->
    (∀ k, k ≤ J -> ∀ t, t ∈ Icc (tau k) (if k < J then tau (k+1) else T) ->
      weightedSampleResidual (featureResidualWeight c p L) phi
        (fun m => ∫ u, phi m (Z k u t) ∂ mu0) (fun i => (branches k t).2 i) ≤ delta) ->
    (∀ k, k < J ->
      let muPre := mu0.map (fun u => Z k u (tau (k+1)))
      matrixNuclearValue (populationCovarianceResidual muPre (fun i => (branches k (tau (k+1))).2 i)
        (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix F G
          (∫ x, F x ∂ muPre) ((branches k (tau (k+1))).2 i) z))) / N ≤ deltaTilde) ->
    (∀ n, (view n).observation omega ∉ actualSourceJumpFailure c C g p q D phi G L
      (view n).PopGood (fun hist => (view n).κ hist) (view n).X (view n).Y
      (view n).Xpost (view n).Ypost (view n).eta (pTotal/(8*((J : Real)+1)))) ->
    (∀ n, ((view n).observation omega).1 ∈ (view n).PopGood) ->
    (∀ n, (view n).X ((view n).observation omega).1 = (branches n (tau (n.val+1))).1) ->
    (∀ n, (view n).Y ((view n).observation omega).1 = (branches n (tau (n.val+1))).2) ->
    (∀ n, (view n).Xpost ((view n).observation omega).1 ((view n).observation omega).2 = (paths (tau (n.val+1))).1) ->
    (∀ n, (view n).Ypost ((view n).observation omega).1 ((view n).observation omega).2 = (paths (tau (n.val+1))).2) ->
    (∀ n, (view n).κ ((view n).observation omega).1 = mu0.map (fun u => Z n u (tau (n.val+1)))) ->
    (∀ n, (view n).eta = eta n) ->
    ∀ A_sp, 1 ≤ A_sp ->
      SourceRightAntiSpikiness (fun t => (paths t).1) (fun t => (paths t).2) T A_sp ->
      SourceTrackingSmallness kappa tau eta J T delta deltaTilde A
        (featureDisplacementLambda c C g p q D L+(2+A_sp)*(L : Real)) ->
      SourceTrackingConclusion (fun t => (paths t).1) (fun t => (paths t).2)
        (fun k => (branches k (tau (k+1))).1) (fun k => (branches k (tau (k+1))).2)
        kappa tau eta J T delta deltaTilde A := by
  dsimp only
  intro hControl hXlip hYlip hLocal hXode hYode hGamma hCov hJump hEligible
    hPreX hPreY hPostX hPostY hPreLaw hEta A_sp hAsp hsp hsmall
  let post := sourceActualFinitePost mu0 c p alpha phi G U hU hDomains (hG.of_le (by norm_num)) hN tau eta flowX flowY field
  let branches := sourceFiniteHorizonBranch post flowX flowY J h u
  let paths := sourceFiniteHorizonPath post flowX flowY tau J h u
  let Z := sourceFiniteReferenceBranch tau eta flowY field J h
  have hOrder (k : Nat) (hk : k ≤ J) : tau k ≤ if k < J then tau (k+1) else T :=
    sourceSchedule_ordered tau J T htime hT ⟨k,Nat.lt_succ_of_le hk⟩
  have hClass : ∀ k, k ≤ J -> ∀ t, t ∈ uIcc (tau k) (if k < J then tau (k+1) else T) ->
      mu0.map (fun u => Z k u t) ∈ sourceMomentClass alpha K := by
    intro k hk t ht
    exact (hControl.2 ⟨k,Nat.lt_succ_of_le hk⟩ t (by simpa only [uIcc_of_le (hOrder k hk),sourceScheduleLeft,sourceScheduleRight] using ht)).1
  have hZlip : ∀ k, k ≤ J -> ∀ᵐ u ∂ mu0,
      LipschitzOnWith B (Z k u) (uIcc (tau k) (if k < J then tau (k+1) else T)) := by
    intro k hk
    simpa only [uIcc_of_le (hOrder k hk),sourceScheduleLeft,sourceScheduleRight,Z] using hControl.1 ⟨k,Nat.lt_succ_of_le hk⟩
  have hx : ∀ k, k ≤ J -> ∀ i, LipschitzOnWith B (fun t => (branches k t).1 i)
      (uIcc (tau k) (if k < J then tau (k+1) else T)) := by
    intro k hk i
    simpa only [uIcc_of_le (hOrder k hk)] using hXlip k hk i
  have hy : ∀ k, k ≤ J -> ∀ i, LipschitzOnWith B (fun t => (branches k t).2 i)
      (uIcc (tau k) (if k < J then tau (k+1) else T)) := by
    intro k hk i
    simpa only [uIcc_of_le (hOrder k hk)] using hYlip k hk i
  have hl : ∀ k, k ≤ J -> ∀ t, t ∈ uIcc (tau k) (if k < J then tau (k+1) else T) ->
      ∀ i, norm ((branches k t).1 i) ≤ D ∧ norm ((branches k t).2 i) ≤ D := by
    intro k hk t ht
    exact hLocal k hk t (by simpa only [uIcc_of_le (hOrder k hk),sourceScheduleLeft,sourceScheduleRight] using ht)
  have hspBranch := sourceRightAntiSpikiness_branches tau J T A_sp htau0 htime hT
    (fun k t => (branches k t).1) (fun k t => (branches k t).2) hsp
  let P := sourceFiniteTrackingPaths mu0 c p alpha K D A_sp phi G U hU hDomains (hG.of_le (by norm_num))
    hN tau eta flowX flowY field J T B htau0 htime hT h u hXstart hYstart
    hClass hZlip hx hy hl hspBranch hXode hYode
  have result := actual_source_tracking_bound c C g p q K D alpha C3 phi hc hC hp hq hK hD halpha
    hphi hgrowth hthirdphi hgrowth3 G U hU (hDomains K hK D hD) hG hthirdG L hL
    mu0 J tau eta T A_sp B hN htau0 htime hT P delta deltaTilde pTotal
    hGamma hCov nu S V view omega hJump hEligible hPreX hPreY hPostX hPostY hPreLaw hEta hAsp
  exact result hsmall
end PaperFormalization.Manuscript
