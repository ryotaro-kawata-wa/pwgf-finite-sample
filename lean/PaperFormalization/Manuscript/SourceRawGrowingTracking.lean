import PaperFormalization.Manuscript.SourceRawObjectiveTracking
import PaperFormalization.Manuscript.SourceMainRateStatement
import PaperFormalization.Manuscript.SourceRawCharacteristicVersion

/-! # Original-solution main growing-horizon rate on ONE epsilon-independent event

M13t verified implementation. This is a direct source-facing application,
not a theorem assuming residual rates, a compatible view family or smallness.
The selected radius coefficient depends only on alpha,K0. For each epsilon the
constant and cutoff are the uniform sourceUniformRateData, whose arguments
exclude N,T,p, schedule, curvature, probability space and random outcome.
Only the original anti-spikiness and controlled RESPONSE path restrictions
remain. The raw fixed-schedule theorem supplies the exact common event.
No arbitrary-initial-state global ODE existence or adaptive schedule is claimed.
-/
open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology ProbabilityTheory Matrix.Norms.Frobenius
namespace PaperFormalization.Manuscript
open Continuous Piecewise
attribute [local instance] sourceGramMeasurableMatrix sourceGramBorelMatrix
variable {O W : Type*} [MeasurableSpace O] [MeasurableSpace W] {N d : Nat}
variable {H : Nat -> Type*} [∀ m, NormedAddCommGroup (H m)]
  [∀ m, InnerProductSpace Real (H m)] [∀ m, CompleteSpace (H m)]
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 14 in
set_option maxHeartbeats 15000000 in
/-- A single fixed-radius event supports every positive exponent. Controlled
responses give eventual smallness through the previously proved uniform cutoff.
The output includes the main max(distance, objective) rate for the raw solution,
both trace labels and the exact four finite-schedule conclusions. -/
theorem exists_source_raw_growing_tracking_event
    (c C g p q alpha K0 C3 A_sp L0 Cp upsilon zeta C0 : Real)
    (phi : ∀ m, EuclideanSpace Real (Fin d) -> H m)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (halpha : 0 < alpha) (hK0 : 0 < K0)
    (hAsp : 1 ≤ A_sp) (hL0 : 0 ≤ L0) (hCp : 0 < Cp)
    (hupsilon : 0 ≤ upsilon) (hzeta : 0 < zeta) (horizonGap : upsilon+zeta < 1/4)
    (hC0 : 0 ≤ C0)
    (hphi : ∀ m, ContDiff Real 2 (phi m))
    (hgrowth : ∀ m x k, k ≤ 2 -> norm (iteratedFDeriv Real k (phi m) x) ≤
      featureGrowth C g q m * (1 + norm x ^ (m+1-k)))
    (hthirdphi : ∀ m x, DifferentiableAt Real (fderiv Real (fderiv Real (phi m))) x)
    (hgrowth3 : ∀ m x, norm (iteratedFDeriv Real 3 (phi m) x) ≤
      featureGrowth C g q m * (1 + norm x ^ (m+1-3)))
    (G : lp H 2 -> Real) (U : Set (lp H 2)) (hU : IsOpen U)
    (hDomains : SourceAllMomentDomains (sourceWeightedFeatureMap c p phi) alpha U)
    (hG : ContDiffOn Real 3 G U)
    (hthirdG : ∀ theta, theta ∈ U -> norm (iteratedFDeriv Real 3 G theta) ≤ C3)
    (hN : 0 < N) (tau eta : Nat -> Real) (J : Nat) (T : Real) (B : NNReal)
    (htau0 : tau 0 = 0) (htime : ∀ k, k < J -> tau k < tau (k+1)) (hT : tau J ≤ T)
    (pTotal : Real) (hpTotal : 0 < pTotal) (hpTotal1 : pTotal < 1)
    (hJbound : (J : Real) ≤ L0)
    (hHorizon : T ≤ (N : Real)^(1/4-upsilon-zeta))
    (hConfidence : (N : Real)^(-Cp) ≤ pTotal)
    (L : NNReal) (hL : (L : Real) = sourceComparisonEnvelope c C g p q
      (sourceFinalMomentScale J T alpha K0 pTotal B)
      (sourceRateRadius N J T pTotal alpha (sourceRateRadiusCoefficient alpha K0 halpha) B) alpha C3 phi G)
    (nu : Measure O) [IsProbabilityMeasure nu]
    (mu0 : Measure (EuclideanSpace Real (Fin d))) [IsProbabilityMeasure mu0]
    (flowY : (n : Nat) -> (Fin n -> W) -> Real -> EuclideanSpace Real (Fin d) -> EuclideanSpace Real (Fin d))
    (field : (n : Nat) -> (Fin n -> W) -> W -> EuclideanSpace Real (Fin d) -> EuclideanSpace Real (Fin d))
    (hFY : ∀ n t, Measurable (fun z : (Fin n -> W) × EuclideanSpace Real (Fin d) => flowY n z.1 t z.2))
    (hfield : ∀ n, Measurable (fun z : ((Fin n -> W) × W) × EuclideanSpace Real (Fin d) => field n z.1.1 z.1.2 z.2))
    (hYstart : ∀ n past x, flowY n past (tau n) x = x)
    (initial : O -> SourceFiniteConfiguration N d) (innovation : Nat -> O -> W)
    (hinit : Measurable initial) (hInnovation : ∀ n, Measurable (innovation n))
    (hiid : iIndepFun (fun i o => initial o i) nu)
    (hPopIndependent : IndepFun (fun o n => innovation n o) (fun o i => initial o i) nu)
    (hInitialLaw : ∀ i, nu.map (fun o => initial o i) = mu0)
    (lambda : Fin J -> Measure W) [∀ n, IsProbabilityMeasure (lambda n)]
    (heta : ∀ n : Fin J, 0 ≤ eta n) (hEtaBound : ∀ n : Fin J, eta n ≤ C0)
    (hFresh : ∀ n : Fin J, IndepFun (sourceOriginalPrehistory initial innovation n) (innovation n) nu)
    (hInnovationLaw : ∀ n : Fin J, nu.map (innovation n) = lambda n)
    (Phi : (Nat -> W) -> EuclideanSpace Real (Fin d) ->
      SourceReferencePathSpace J d (sourceScheduleLeft tau J) (sourceScheduleRight tau J T))
    (hPhi : Measurable (fun z : (Nat -> W) × EuclideanSpace Real (Fin d) => Phi z.1 z.2))
    (hVersion : ∀ᵐ z ∂ (nu.map (fun o n => innovation n o)).prod mu0,
      ∀ j t, t ∈ Icc (sourceScheduleLeft tau J j) (sourceScheduleRight tau J T j) ->
        sourceReferencePathEval (Phi z.1 z.2) j t = sourceOriginalCharacteristic tau eta flowY field j.val z.1 z.2 t)
    (XB : SourceAuxiliarySpace O (SourceStepNormal N d) J -> Nat -> Real -> SourceFiniteConfiguration N d) :
    let D := sourceRateRadius N J T pTotal alpha (sourceRateRadiusCoefficient alpha K0 halpha) B
    let flowX := sourceCanonicalEmpiricalFlow (N := N) c p phi G tau J T htime hT
    let post := sourceActualFinitePost mu0 c p alpha phi G U hU hDomains (hG.of_le (by norm_num)) hN tau eta flowX flowY field
    let normal := stdGaussian (SourceStepNormal N d)
    let finalLaw := sourceAuxiliaryMeasure nu normal J
    let branches := sourceFinalBranch post flowX flowY initial innovation J
    let paths := sourceFinalRight post flowX flowY tau initial innovation J
    let F := sourceWeightedFeatureMap c p phi
    let Kpop := sourceFinalMomentScale J T alpha K0 pTotal B
    let delta := sourceFinalGammaThreshold J N T alpha K0 D pTotal c C g p q B L
    let deltaTilde := sourcePrescribedCovarianceEnvelope J N d c C g p q alpha Kpop L pTotal
    let A := sourceFinalJumpCoefficient J d c C g p q D pTotal L
    let Z := fun z : SourceAuxiliarySpace O (SourceStepNormal N d) J => sourceFiniteReferenceBranch tau eta flowY field J (sourceTowerPacked innovation J z)
    let kappa := fun z t => rayleighInf (sampledMomentHessian F G
      (∫ x, F x ∂ mu0.map (fun u => sourceGlue tau J (fun k => Z z k u) t)) ((paths z t).2))
    (∀ cloud, ∀ t, t ∈ Icc 0 T ->
      finalLaw.map (fun z => sourcePairCloud cloud (sourceGlue tau J (XB z) t,(paths z t).2) ⟨0,hN⟩) ∈ sourceMomentClass alpha K0) ->
    (∀ᵐ z ∂ finalLaw, ∀ cloud i j,
      LipschitzOnWith B (fun t => sourcePairCloud cloud (XB z j.val t,(branches z j.val t).2) i)
        (Icc (sourceScheduleLeft tau J j) (sourceScheduleRight tau J T j))) ->
    (∀ᵐ z ∂ finalLaw, SourceRawEmpiricalSchedule mu0 c p alpha phi G U hU hDomains
      (hG.of_le (by norm_num)) hN tau eta flowY field J T (sourceTowerPacked innovation J z)
      (initial (sourceAuxiliaryOriginal J z)) (XB z)) ->
    (∀ᵐ z ∂ (nu.map (fun o n => innovation n o)).prod mu0, ∀ k, k ≤ J ->
      ∀ᵐ t ∂ volume.restrict (Ioo (tau k) (if k < J then tau (k+1) else T)),
        HasDerivAt (sourceOriginalCharacteristic tau eta flowY field k z.1 z.2)
          (momentGradientField (fderiv Real F) (gradient G)
            (∫ x, F x ∂ mu0.map (fun u => sourceOriginalCharacteristic tau eta flowY field k z.1 u t),
             sourceOriginalCharacteristic tau eta flowY field k z.1 z.2 t)) t) ->
    (∀ n : Fin J,
      let hist := sourceAuxiliaryHistory (A := SourceStepNormal N d) (sourceOriginalPrehistory initial innovation n) n
      let Y := fun h : SourceRecurrentHistory W N d n => (sourceHistoryBranch post flowX flowY n h (tau (n.val+1))).2
      let popLaw := characteristicKernel mu0 (fun (h : SourceRecurrentHistory W N d n) u =>
        sourceReferencePre tau flowY (sourcePopulationFieldJump eta field) n (sourceHistoryPopulation n h) u)
      ∀ᵐ h ∂ (sourceAuxiliaryMeasure nu normal n).map hist,
        (lambda n).map (sourceRawFieldVector field n (sourceHistoryPopulation n h) (Y h)) =
          multivariateGaussian 0 (populationGramCovariance (popLaw h)
            (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix F G
              (∫ x, F x ∂ popLaw h) (Y h i) z)))) ->
    let data := fun epsilon (he : 0 < epsilon) => sourceUniformRateData
      c C g p q alpha K0 C3 A_sp L0 Cp upsilon zeta C0 phi G B
      hc hC hp hq halpha (by linarith : 0 ≤ A_sp) hL0 hCp hupsilon hzeta hC0 epsilon he
    ∃ Good : Set (SourceAuxiliarySpace O (SourceStepNormal N d) J),
      MeasurableSet Good ∧ finalLaw.real Good.compl ≤ 17*pTotal/32 ∧ finalLaw.real Good.compl < pTotal ∧
      ∀ z, z ∈ Good ->
        SourceObjectiveControl F G
          (fun t => mu0.map (fun u => sourceGlue tau J (fun k => Z z k u) t))
          (fun k => mu0.map (fun u => Z z k u (tau (k+1))))
          (sourceGlue tau J (XB z)) (fun t => (paths z t).2)
          (fun k => XB z k (tau (k+1))) (fun k => (branches z k (tau (k+1))).2)
          J T (featureDisplacementLambda c C g p q D L) delta ∧
        ∀ epsilon (he : 0 < epsilon), (data epsilon he).val.2 ≤ N ->
          SourceRightAntiSpikiness (sourceGlue tau J (XB z)) (fun t => (paths z t).2) T A_sp ->
          SourceControlledResponse N J T upsilon C0 (kappa z) tau eta ->
          SourceTrackingConclusion (sourceGlue tau J (XB z)) (fun t => (paths z t).2)
            (fun k => XB z k (tau (k+1))) (fun k => (branches z k (tau (k+1))).2)
            (kappa z) tau eta J T delta deltaTilde A ∧
          SourceObjectiveTrackingConclusion F G
            (fun t => mu0.map (fun u => sourceGlue tau J (fun k => Z z k u) t))
            (fun k => mu0.map (fun u => Z z k u (tau (k+1))))
            (sourceGlue tau J (XB z)) (fun k => XB z k (tau (k+1)))
            (kappa z) tau eta J T (featureDisplacementLambda c C g p q D L) delta deltaTilde A ∧
          SourceJointRateConclusion F G
            (fun t => mu0.map (fun u => sourceGlue tau J (fun k => Z z k u) t))
            (fun k => mu0.map (fun u => Z z k u (tau (k+1))))
            (sourceGlue tau J (XB z)) (fun t => (paths z t).2)
            (fun k => XB z k (tau (k+1))) (fun k => (branches z k (tau (k+1))).2)
            (kappa z) tau eta J T pTotal epsilon (data epsilon he).val.1 := by
  dsimp only
  intro hFirstRaw hLipRaw hRaw hPopODE hField
  let CD := sourceRateRadiusCoefficient alpha K0 halpha
  let D := sourceRateRadius N J T pTotal alpha CD B
  have hCD := sourceRateRadiusCoefficient_admissible alpha K0 halpha
  have hT0 : 0 ≤ T := by
    have hh := Piecewise.time_mono_prefix tau J (fun k hk => (htime k hk).le) 0 J (Nat.zero_le J) le_rfl
    rw [htau0] at hh
    exact hh.trans hT
  have hD : 1 ≤ D := sourceRateRadius_one_le N J T pTotal alpha CD B
    hN hT0 hpTotal hpTotal1.le halpha hCD.1
  have hRadius := sourceRateRadius_admissible N J T pTotal alpha K0 CD B
    hN hT0 hpTotal hpTotal1.le halpha hK0 hCD.2.1
  obtain ⟨Good,hGood,hBudget,hStrict,hValid⟩ := exists_source_objective_tracking_for_raw_solution_branches
    c C g p q alpha K0 D C3 phi hc hC hp hq halpha hK0 hD hphi hgrowth hthirdphi hgrowth3
    G U hU hDomains hG hthirdG hN tau eta J T B htau0 htime hT pTotal hpTotal hpTotal1 hRadius L hL
    nu mu0 flowY field hFY hfield hYstart initial innovation hinit hInnovation hiid hPopIndependent hInitialLaw
    lambda heta hFresh hInnovationLaw Phi hPhi hVersion XB hFirstRaw hLipRaw hRaw hPopODE hField
  refine ⟨Good,hGood,hBudget,hStrict,?_⟩
  intro z hz
  have hObj := (hValid z hz).1
  refine ⟨hObj,?_⟩
  intro epsilon he hCutoff hsp hResponse
  let rates := sourceUniformRateData c C g p q alpha K0 C3 A_sp L0 Cp upsilon zeta C0 phi G B
    hc hC hp hq halpha (by linarith : 0 ≤ A_sp) hL0 hCp hupsilon hzeta hC0 epsilon he
  have hEta : ∀ i < J, 0 ≤ eta i ∧ eta i ≤ C0 := fun i hi => ⟨heta ⟨i,hi⟩,hEtaBound ⟨i,hi⟩⟩
  have hRate := rates.property.2.2 N J hCutoff T pTotal hJbound hT0 hpTotal hpTotal1
    hHorizon hConfidence L hL _ tau eta hEta hResponse
  have hTrack := (hValid z hz).2 A_sp hAsp hsp hRate.1
  have hLambda : 0 ≤ featureDisplacementLambda c C g p q D L :=
    featureDisplacementLambda_nonneg c C g p q D L hC (by linarith)
  refine ⟨hTrack,source_objective_conclusion_of_tracking _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hLambda hObj hTrack,?_⟩
  constructor
  · intro t ht
    refine ⟨(hObj.1 t ht).1,?_⟩
    exact hRate.2 J le_rfl t ht _ _ (hTrack.1 t ht) (hObj.1 t ht).2
  · intro k hk
    have htimeK : tau (k+1) ∈ Icc 0 T := source_closed_time_in_horizon tau J T
      htau0 htime hT k hk.le (tau (k+1))
      (by simp only [if_pos hk]; exact ⟨(htime k hk).le,le_rfl⟩)
    refine ⟨(hObj.2 k hk).1,?_⟩
    exact hRate.2 k hk.le (tau (k+1)) htimeK _ _ (hTrack.2.2.1 k hk) (hObj.2 k hk).2
end PaperFormalization.Manuscript
