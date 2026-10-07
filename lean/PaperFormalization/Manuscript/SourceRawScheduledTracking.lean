import PaperFormalization.Manuscript.SourceRawScheduleCorrespondence

/-! # Final high-probability tracking for the supplied original solution branches
M13s verified unit; see CODEX_HANDOFF_M13S.md. Unlike a theorem whose lifetime membership is merely supplied,
this source-facing wrapper takes the raw vector ODE, start and prescribed jump
relations. It proves the canonical/source agreement, transfers the ORIGINAL
first-particle moments and Lipschitz condition, invokes the full scheduled
tracking theorem, and returns tracking of the RAW source path itself.
The measurable source characteristic is an existing manuscript realization
premise. No probability is assigned to anti-spikiness or smallness.
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
/-- The original raw empirical solution, not a surrogate off-domain process,
is tracked with all right/pre and zero-envelope conclusions. -/
theorem exists_source_tracking_for_raw_solution_branches
    (c C g p q alpha K0 D C3 : Real)
    (phi : ∀ m, EuclideanSpace Real (Fin d) -> H m)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (halpha : 0 < alpha) (hK0 : 0 < K0) (hD : 1 ≤ D)
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
    (hRadiusChoice : 2 * Real.exp 1 * K0 *
      (1 + Real.log (2 * N * (2*((J : Real)+1)+(B : Real)*T/(Real.exp 1*K0))/(pTotal/8)))^(1/alpha) ≤ D)
    (L : NNReal) (hL : (L : Real) = sourceComparisonEnvelope c C g p q
      (sourceFinalMomentScale J T alpha K0 pTotal B) D alpha C3 phi G)
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
    (heta : ∀ n : Fin J, 0 ≤ eta n)
    (hFresh : ∀ n : Fin J, IndepFun (sourceOriginalPrehistory initial innovation n) (innovation n) nu)
    (hInnovationLaw : ∀ n : Fin J, nu.map (innovation n) = lambda n)
    (Phi : (Nat -> W) -> EuclideanSpace Real (Fin d) ->
      SourceReferencePathSpace J d (sourceScheduleLeft tau J) (sourceScheduleRight tau J T))
    (hPhi : Measurable (fun z : (Nat -> W) × EuclideanSpace Real (Fin d) => Phi z.1 z.2))
    (hVersion : ∀ᵐ z ∂ (nu.map (fun o n => innovation n o)).prod mu0,
      ∀ j t, t ∈ Icc (sourceScheduleLeft tau J j) (sourceScheduleRight tau J T j) ->
        sourceReferencePathEval (Phi z.1 z.2) j t = sourceOriginalCharacteristic tau eta flowY field j.val z.1 z.2 t)
    (XB : SourceAuxiliarySpace O (SourceStepNormal N d) J -> Nat -> Real -> SourceFiniteConfiguration N d) :
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
    let Z := fun z => sourceFiniteReferenceBranch tau eta flowY field J (sourceTowerPacked innovation J z)
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
    ∃ Good : Set (SourceAuxiliarySpace O (SourceStepNormal N d) J),
      MeasurableSet Good ∧ finalLaw.real Good.compl ≤ 17*pTotal/32 ∧ finalLaw.real Good.compl < pTotal ∧
      ∀ z, z ∈ Good -> ∀ A_sp, 1 ≤ A_sp ->
        SourceRightAntiSpikiness (sourceGlue tau J (XB z)) (fun t => (paths z t).2) T A_sp ->
        SourceTrackingSmallness (kappa z) tau eta J T delta deltaTilde A
          (featureDisplacementLambda c C g p q D L+(2+A_sp)*(L : Real)) ->
        SourceTrackingConclusion (sourceGlue tau J (XB z)) (fun t => (paths z t).2)
          (fun k => XB z k (tau (k+1))) (fun k => (branches z k (tau (k+1))).2)
          (kappa z) tau eta J T delta deltaTilde A := by
  dsimp only
  intro hFirstRaw hLipRaw hRaw hPopODE hField
  classical
  let flowX := sourceCanonicalEmpiricalFlow (N := N) c p phi G tau J T htime hT
  let post := sourceActualFinitePost mu0 c p alpha phi G U hU hDomains (hG.of_le (by norm_num)) hN tau eta flowX flowY field
  let normal := stdGaussian (SourceStepNormal N d)
  let finalLaw := sourceAuxiliaryMeasure nu normal J
  let branches := sourceFinalBranch post flowX flowY initial innovation J
  let paths := sourceFinalRight post flowX flowY tau initial innovation J
  have hf := source_empirical_drift_contDiff_all_domains c C g p q alpha phi hc hC hp hq hphi hgrowth
    G U hU hDomains hG hN
  let Agreement := fun z : SourceAuxiliarySpace O (SourceStepNormal N d) J =>
    SourceVisitedEmpiricalSolutions (sourceExactEmpiricalDrift c p phi G) post tau J T
      (sourceTowerPacked innovation J z) (initial (sourceAuxiliaryOriginal J z)) ∧
    ∀ k, k ≤ J -> EqOn (fun t => (branches z k t).1) (XB z k)
      (Icc (tau k) (if k < J then tau (k+1) else T))
  have hAgreement : ∀ᵐ z ∂ finalLaw, Agreement z := by
    filter_upwards [hRaw] with z hz
    exact source_canonical_schedule_agrees_with_source mu0 c p alpha phi G U hU hDomains
      (hG.of_le (by norm_num)) hN tau eta flowY field hf J T htime hT
      (sourceTowerPacked innovation J z) (initial (sourceAuxiliaryOriginal J z)) (XB z) hz
  have hRightEq (z) (hz : Agreement z) :
      EqOn (fun t => (paths z t).1) (sourceGlue tau J (XB z)) (Icc 0 T) :=
    source_glued_paths_eq_of_closed_agreement tau J T htau0 htime
      (fun k t => (branches z k t).1) (XB z) hz.2
  have hFirst : ∀ cloud t, t ∈ Icc 0 T ->
      finalLaw.map (fun z => sourcePairCloud cloud (paths z t) ⟨0,hN⟩) ∈ sourceMomentClass alpha K0 := by
    intro cloud t ht
    have hm : finalLaw.map (fun z => sourcePairCloud cloud (paths z t) ⟨0,hN⟩) =
        finalLaw.map (fun z => sourcePairCloud cloud (sourceGlue tau J (XB z) t,(paths z t).2) ⟨0,hN⟩) := by
      apply Measure.map_congr
      filter_upwards [hAgreement] with z hz
      exact congrArg (fun pair => sourcePairCloud cloud pair ⟨0,hN⟩) (Prod.ext (hRightEq z hz ht) rfl)
    rw [hm]
    exact hFirstRaw cloud t ht
  have hLip : ∀ᵐ z ∂ finalLaw, ∀ cloud i j,
      LipschitzOnWith B (fun t => sourcePairCloud cloud (branches z j.val t) i)
        (Icc (sourceScheduleLeft tau J j) (sourceScheduleRight tau J T j)) := by
    filter_upwards [hAgreement,hLipRaw] with z hz hl
    intro cloud i j
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    have heS : branches z j.val s = (XB z j.val s,(branches z j.val s).2) :=
      Prod.ext (hz.2 j.val (Nat.le_of_lt_succ j.isLt) hs) rfl
    have heT : branches z j.val t = (XB z j.val t,(branches z j.val t).2) :=
      Prod.ext (hz.2 j.val (Nat.le_of_lt_succ j.isLt) ht) rfl
    rw [heS,heT]
    exact (hl cloud i j).dist_le_mul s hs t ht
  obtain ⟨Core,hCore,hBudget,hStrict,hValid⟩ := exists_source_scheduled_tracking_event
    c C g p q alpha K0 D C3 phi hc hC hp hq halpha hK0 hD hphi hgrowth hthirdphi hgrowth3
    G U hU hDomains hG hthirdG hN tau eta J T B htau0 htime hT pTotal hpTotal hpTotal1 hRadiusChoice L hL
    nu mu0 flowY field hFY hfield hYstart initial innovation hinit hInnovation hiid hPopIndependent hInitialLaw
    lambda heta hFresh hInnovationLaw Phi hPhi hVersion hFirst hLip (hAgreement.mono (fun _ h => h.1)) hPopODE hField
  obtain ⟨Good,hGood,hGoodBudget,hGoodValid⟩ := exists_original_population_event finalLaw finalLaw id
    measurable_id (by simp) Core hCore (17*pTotal/32) hBudget Agreement hAgreement
  have hslack : 17*pTotal/32 < pTotal := by linarith
  refine ⟨Good,hGood,hGoodBudget,hGoodBudget.trans_lt hslack,?_⟩
  intro z hz A_sp hAsp hsp hsmall
  have hAgree := (hGoodValid z hz).1
  have hInCore := (hGoodValid z hz).2
  have hspCanonical : SourceRightAntiSpikiness (fun t => (paths z t).1) (fun t => (paths z t).2) T A_sp := by
    intro t ht
    rw [hRightEq z hAgree ht]
    exact hsp t ht
  have ht := hValid z hInCore A_sp hAsp hspCanonical hsmall
  refine ⟨?_,?_,?_,?_⟩
  . intro t ht0
    have he := hRightEq z hAgree ht0
    dsimp only [paths,post,flowX] at he
    simpa only [he] using ht.1 t ht0
  . intro hzero t ht0
    exact (hRightEq z hAgree ht0).symm.trans (ht.2.1 hzero t ht0)
  . intro k hk
    have hpre := hAgree.2 k hk.le (by simp only [if_pos hk]; exact ⟨(htime k hk).le,le_rfl⟩)
    dsimp only [branches,post,flowX] at hpre
    simpa only [hpre] using ht.2.2.1 k hk
  . intro hzero k hk
    have hpre := hAgree.2 k hk.le (by simp only [if_pos hk]; exact ⟨(htime k hk).le,le_rfl⟩)
    exact hpre.symm.trans (ht.2.2.2 hzero k hk)
end PaperFormalization.Manuscript
