import PaperFormalization.Manuscript.SourceFinalTrajectoryRealization
import PaperFormalization.Manuscript.SourceRecurrentObservationEvent

/-! # Original scheduled tracking: a complete event-to-tracking invocation
M13s verified unit; see CODEX_HANDOFF_M13S.md. This theorem takes primitive source realization data, ONE
particle's right-path moment assumption, the original piecewise regularity and
primitive innovation/field laws. It constructs the empirical solution selector,
derives its permutation equivariance, the actual finite recurrence's exchangeable
law, all-particle/left-label moments, both event families, and the exact original
tracking invocation. Population/Gamma/radius and observation losses are combined
on the SAME final auxiliary measure.

The existence witness below concerns only visited source branches. It is not
arbitrary-initial-state global existence. The measurable population characteristic
and its source ODE are original model premises; their conditional laws are NOT.
No view, hGamma, covariance concentration, target scalar AC/drift/jump, empirical
exchangeability, or all-particle moment bound is an input hypothesis.
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
/-- On a measurable original-law event of loss at most 17 pTotal/32, the actual
recurrent paths satisfy all four source tracking conclusions whenever the original
anti-spikiness and nonlinear smallness path conditions hold. No probability is
claimed after conditioning on those possibly rare path restrictions. -/
theorem exists_source_scheduled_tracking_event
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
        sourceReferencePathEval (Phi z.1 z.2) j t = sourceOriginalCharacteristic tau eta flowY field j.val z.1 z.2 t) :
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
      finalLaw.map (fun z => sourcePairCloud cloud (paths z t) ⟨0,hN⟩) ∈ sourceMomentClass alpha K0) ->
    (∀ᵐ z ∂ finalLaw, ∀ cloud i j,
      LipschitzOnWith B (fun t => sourcePairCloud cloud (branches z j.val t) i)
        (Icc (sourceScheduleLeft tau J j) (sourceScheduleRight tau J T j))) ->
    (∀ᵐ z ∂ finalLaw, SourceVisitedEmpiricalSolutions (sourceExactEmpiricalDrift c p phi G)
      post tau J T (sourceTowerPacked innovation J z) (initial (sourceAuxiliaryOriginal J z))) ->
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
        SourceRightAntiSpikiness (fun t => (paths z t).1) (fun t => (paths z t).2) T A_sp ->
        SourceTrackingSmallness (kappa z) tau eta J T delta deltaTilde A
          (featureDisplacementLambda c C g p q D L+(2+A_sp)*(L : Real)) ->
        SourceTrackingConclusion (fun t => (paths z t).1) (fun t => (paths z t).2)
          (fun k => (branches z k (tau (k+1))).1) (fun k => (branches z k (tau (k+1))).2)
          (kappa z) tau eta J T delta deltaTilde A := by
  dsimp only
  intro hFirst hLip hSolutions hPopODE hField
  classical
  let flowX := sourceCanonicalEmpiricalFlow (N := N) c p phi G tau J T htime hT
  let post := sourceActualFinitePost mu0 c p alpha phi G U hU hDomains (hG.of_le (by norm_num)) hN tau eta flowX flowY field
  let normal := stdGaussian (SourceStepNormal N d)
  let finalLaw := sourceAuxiliaryMeasure nu normal J
  let branches := sourceFinalBranch post flowX flowY initial innovation J
  let paths := sourceFinalRight post flowX flowY tau initial innovation J
  let F := sourceWeightedFeatureMap c p phi
  let scale := sourceFinalPopulationScale J T alpha K0 pTotal B
  let Kpop := sourceFinalMomentScale J T alpha K0 pTotal B
  let a := sourceScheduleLeft tau J
  let btime := sourceScheduleRight tau J T
  let env := fun o n => innovation n o
  let finalEnv := fun z : SourceAuxiliarySpace O (SourceStepNormal N d) J => env (sourceAuxiliaryOriginal J z)
  let finalInit := fun (i : Fin N) (z : SourceAuxiliarySpace O (SourceStepNormal N d) J) => initial (sourceAuxiliaryOriginal J z) i
  let Z := fun z : SourceAuxiliarySpace O (SourceStepNormal N d) J => sourceFiniteReferenceBranch tau eta flowY field J (sourceTowerPacked innovation J z)
  let i0 : Fin N := ⟨0,hN⟩
  have hScales := sourceFinalScales_positive J T alpha K0 pTotal B halpha hpTotal hpTotal1
  have hscale : 0 < scale := hScales.1
  have hKpop : 0 < Kpop := hScales.2
  have hKscale : Kpop = sourceExponentialMomentCoefficient alpha * scale := rfl
  have hab : ∀ j, a j ≤ btime j := sourceSchedule_ordered tau J T htime hT
  have hlen : (∑ j, (btime j-a j)) ≤ T := (sourceSchedule_total_length tau J T htau0).le
  have hT0 : 0 ≤ T := by
    have hh := Piecewise.time_mono_prefix tau J (fun k hk => (htime k hk).le) 0 J (Nat.zero_le J) le_rfl
    rw [htau0] at hh
    exact hh.trans hT
  have hRadius := sourceOriginalRadiusLoss_eighth_budget J N T alpha K0 D pTotal B
    hN hT0 halpha hK0 hpTotal hpTotal1 hRadiusChoice
  have hfx := sourceCanonicalEmpiricalFlow_properties c C g p q alpha phi hc hC hp hq hphi hgrowth
    G U hU hDomains hG hN tau J T htime hT
  have hFX : ∀ k t, Measurable (flowX k t) := hfx.1
  have hXstart : ∀ k x, flowX k (tau k) x = x := hfx.2.1
  have hXPerm : ∀ s k t x, flowX k t (sourceParticlePermute s x) = sourceParticlePermute s (flowX k t x) := hfx.2.2.2
  have hpost : ∀ k, Measurable (fun z : (Fin k -> W × SourceStepNormal N d) × SourceFiniteConfiguration N d => post k z.1 z.2) :=
    sourceActualFinitePost_measurable mu0 c C g p q alpha phi hc hC hp hq hphi hgrowth
      G U hU hDomains (hG.of_le (by norm_num)) hN tau eta flowX flowY field hFX hFY hfield
  have hpostPerm : ∀ s k h u, post k (sourcePackedPermute s h) (sourceParticlePermute s u) = sourcePairPermute s (post k h u) :=
    fun s => sourceActualFinitePost_permute mu0 c p alpha phi G U hU hDomains (hG.of_le (by norm_num)) hN
      tau eta flowX flowY field hFY hfield s (hXPerm s)
  have hmBranches k t := sourceFinalBranch_measurable post flowX flowY hpost hFX hFY initial innovation hinit hInnovation J k t
  have hAllMoment := sourceFinalBranch_all_closed_moments post flowX flowY hpost hFX hFY hpostPerm hXPerm
    nu mu0 initial innovation hinit hInnovation hiid hPopIndependent hInitialLaw tau J T alpha K0
    htau0 htime hT i0 (by
      intro cloud k hk
      filter_upwards [hLip] with z hz
      exact (hz cloud i0 ⟨k,Nat.lt_succ_of_le hk⟩).continuousOn) hFirst
  have henv : Measurable env := measurable_pi_lambda _ hInnovation
  have hInitCoord i : Measurable (fun o => initial o i) :=
    ((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 _)).comp hinit
  have projectOriginal := sourceAuxiliaryOriginal_preserving nu normal J
  have hFinalEnv : Measurable finalEnv := henv.comp projectOriginal.measurable
  have hFinalInit i : Measurable (finalInit i) := (hInitCoord i).comp projectOriginal.measurable
  have hFinalIID : iIndepFun finalInit finalLaw :=
    source_iIndepFun_pullback nu finalLaw (sourceAuxiliaryOriginal J) projectOriginal
      (fun i o => initial o i) hInitCoord hiid
  have hFinalInd : IndepFun finalEnv (fun z i => finalInit i z) finalLaw :=
    source_independence_pullback nu finalLaw (sourceAuxiliaryOriginal J) projectOriginal
      env (fun o i => initial o i) henv (measurable_pi_lambda _ hInitCoord) hPopIndependent
  have hFinalLaw i : finalLaw.map (finalInit i) = mu0 :=
    (source_final_original_marginal nu normal (fun o => initial o i) (hInitCoord i) J).trans (hInitialLaw i)
  have hFinalEnvLaw : finalLaw.map finalEnv = nu.map env :=
    source_final_original_marginal nu normal env henv J
  have hVersionSample := source_independent_seed_path_agreement nu mu0 env (fun i o => initial o i)
    henv hInitCoord hPopIndependent hInitialLaw
    (fun e u => ∀ j t, t ∈ Icc (a j) (btime j) ->
      sourceReferencePathEval (Phi e u) j t = sourceOriginalCharacteristic tau eta flowY field j.val e u t) hVersion
  have hVersionSampleFinal := projectOriginal.quasiMeasurePreserving.ae hVersionSample
  let Clouds := fun (cloud : Fin 2) (i : Fin N) (j : Fin (J+1))
    (z : SourceAuxiliarySpace O (SourceStepNormal N d) J) t => sourcePairCloud cloud (branches z j.val t) i
  have hClouds cloud i j t : Measurable (fun z => Clouds cloud i j z t) :=
    ((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 _)).comp
      ((sourcePairCloud_measurable cloud).comp (hmBranches j.val t))
  have hCloudRef : ∀ᵐ z ∂ finalLaw, ∀ i j t, t ∈ Icc (a j) (btime j) ->
      Clouds 1 i j z t = sourceReferencePathEval (Phi (finalEnv z) (finalInit i z)) j t := by
    filter_upwards [hVersionSampleFinal] with z hz
    intro i j t ht
    have he := sourceFinalBranch_reference_original mu0 c p alpha phi G U hU hDomains (hG.of_le (by norm_num)) hN
      tau eta flowX flowY field initial innovation J j.val (Nat.le_of_lt_succ j.isLt) z t i
    exact he.trans (hz i j t ht).symm
  have hvalue m x : norm (phi m x) ≤ featureGrowth C g q m * (1+norm x^(m+1)) := by
    simpa only [norm_iteratedFDeriv_zero,Nat.sub_zero] using hgrowth m x 0 (by norm_num)
  have hderiv m x : norm (fderiv Real (phi m) x) ≤ featureGrowth C g q m * (1+norm x^m) := by
    simpa only [norm_iteratedFDeriv_one,Nat.add_sub_cancel] using hgrowth m x 1 (by norm_num)
  obtain ⟨PG,hPG,hPGBudget,hPGValid⟩ := exists_source_retained_population_gamma_radius_event
    J N d hN T a btime B hab hlen alpha K0 (pTotal/8) (pTotal/8) D halpha hK0
    (by positivity) (by linarith) (by positivity) (by linarith) hD hRadius.1
    finalLaw mu0 finalEnv finalInit hFinalEnv hFinalInit hFinalIID hFinalInd hFinalLaw
    Phi hPhi Clouds hClouds hLip (fun cloud i j t ht => hAllMoment cloud i j.val (Nat.le_of_lt_succ j.isLt) t ht)
    hCloudRef (fun _ => True) (by simp) c C g p q L hc hp hq hC phi
    (fun m => (hphi m).of_le (by norm_num)) hvalue hderiv
  have hPopPrefix (n : Fin J) : IndepFun (fun o (i : Fin n.val) => innovation i o) (fun o (i : Fin N) => initial o i) nu := by
    simpa only [Function.comp_def,id_eq] using hPopIndependent.comp
      (measurable_pi_lambda _ (fun i : Fin n.val => measurable_pi_apply i.val)) measurable_id
  have hPreMoment (n : Fin J) : nu.map (fun o => sourceReferencePre tau flowY (sourcePopulationFieldJump eta field)
      n (fun i => innovation i o) (initial o i0)) ∈ sourceMomentClass alpha K0 := by
    have hc := hAllMoment (1 : Fin 2) i0 n.val n.isLt.le (tau (n.val+1))
      (by simp only [if_pos n.isLt]; exact ⟨(htime n n.isLt).le,le_rfl⟩)
    change finalLaw.map (fun z => (branches z n.val (tau (n.val+1))).2 i0) ∈ sourceMomentClass alpha K0 at hc
    rw [sourceFinalBranch_reference_map mu0 c p alpha phi G U hU hDomains (hG.of_le (by norm_num)) hN
      tau eta flowX flowY field nu initial innovation hinit hInnovation hFY hfield J n.val n.isLt.le] at hc
    exact hc
  have hthirdK : ∀ theta, theta ∈ measureMomentRegion F (sourceMomentClass alpha Kpop) D ->
      norm (iteratedFDeriv Real 3 G theta) ≤ C3 := fun theta htheta => hthirdG theta (hDomains Kpop hKpop D hD htheta)
  obtain ⟨project,hproject,horiginal,harray,views,hviews,OBS,hOBS,hOBudget,hOStrict,hOValid⟩ :=
    exists_source_recurrent_observation_event c C g p q alpha K0 Kpop D scale C3 phi
      hc hC hp hq halpha hK0 hKpop hD hscale hKscale hphi hgrowth G U hU hDomains hG hthirdK L hL hN
      nu mu0 tau eta flowX flowY field hFX hFY hfield initial innovation hinit hInnovation J lambda i0 heta
      hPopPrefix hiid hInitialLaw hFresh hInnovationLaw hPreMoment hField pTotal hpTotal hpTotal1
  have hVersionNested : ∀ᵐ e ∂ nu.map env, ∀ᵐ u ∂ mu0, ∀ j t, t ∈ Icc (a j) (btime j) ->
      sourceReferencePathEval (Phi e u) j t = sourceOriginalCharacteristic tau eta flowY field j.val e u t := by
    exact Measure.ae_ae_of_ae_prod hVersion
  have hVersionFinal := projectOriginal.quasiMeasurePreserving.ae (ae_of_ae_map henv.aemeasurable hVersionNested)
  have hYodes := source_final_reference_coordinate_odes mu0 c p alpha phi G U hU hDomains
    (hG.of_le (by norm_num)) hN tau eta flowX flowY field J T nu initial innovation hinit hInnovation
    hPopIndependent hInitialLaw hPopODE
  let Model := fun z : SourceAuxiliarySpace O (SourceStepNormal N d) J =>
    (∀ cloud i j, LipschitzOnWith B (fun t => Clouds cloud i j z t) (Icc (a j) (btime j))) ∧
    SourceVisitedEmpiricalSolutions (sourceExactEmpiricalDrift c p phi G) post tau J T
      (sourceTowerPacked innovation J z) (initial (sourceAuxiliaryOriginal J z)) ∧
    (∀ᵐ u ∂ mu0, ∀ j t, t ∈ Icc (a j) (btime j) ->
      sourceReferencePathEval (Phi (finalEnv z) u) j t = sourceOriginalCharacteristic tau eta flowY field j.val (finalEnv z) u t) ∧
    (∀ k, k ≤ J -> ∀ i,
      ∀ᵐ t ∂ volume.restrict (Ioo (tau k) (if k < J then tau (k+1) else T)),
        HasDerivAt (fun s => (branches z k s).2 i)
          ((frozenMomentConfigurationField (momentGradientField (fderiv Real F) (gradient G))
            (∫ x, F x ∂ mu0.map (fun u => Z z k u t)) (branches z k t).2) i) t)
  have hModel : ∀ᵐ z ∂ finalLaw, Model z := by
    filter_upwards [hLip,hSolutions,hVersionFinal,hYodes] with z hl he hv hy
    exact ⟨hl,he,hv,hy⟩
  obtain ⟨Good,hGood,hBudget,hGoodValid⟩ := exists_source_combined_model_event finalLaw J
    (pTotal/8) (pTotal/8) (sourceOriginalRadiusLoss J N T alpha K0 D B) pTotal
    PG OBS hPG hOBS hPGBudget hOBudget Model hModel
  have hLoss := sourceCombinedLoss_eighth_bound J pTotal (sourceOriginalRadiusLoss J N T alpha K0 D B) hpTotal hRadius.2
  refine ⟨Good,hGood,hBudget.trans hLoss.1,(hBudget.trans hLoss.1).trans_lt hLoss.2,?_⟩
  intro z hz A_sp hAsp hsp hsmall
  have hzM := (hGoodValid z hz).1
  have hpG := hPGValid z (hGoodValid z hz).2.1
  have hoG := hOValid z (hGoodValid z hz).2.2
  have hRawEq : ∀ᵐ u ∂ mu0, ∀ j t, t ∈ Icc (a j) (btime j) ->
      sourceReferencePathEval (Phi (finalEnv z) u) j t = Z z j.val u t := by
    filter_upwards [hzM.2.2.1] with u hu
    intro j t ht
    exact (hu j t ht).trans (sourceFiniteReferenceBranch_original tau eta flowY field innovation J j.val
      (Nat.le_of_lt_succ j.isLt) z u t).symm
  have hControl : SourceReferenceControl mu0 (fun j => Z z j.val) a btime B alpha Kpop scale :=
    sourceReferenceControl_congr mu0 _ _ a btime B alpha Kpop scale hRawEq hpG.2.1
  have hFint : ∀ k, k ≤ J -> ∀ t, t ∈ Icc (tau k) (if k < J then tau (k+1) else T) ->
      Integrable F (mu0.map (fun u => Z z k u t)) := by
    intro k hk t ht
    exact source_feature_integrable_of_source_class c C g p q alpha Kpop phi hc hC hp hq hKpop hphi hgrowth
      _ (hControl.2 ⟨k,Nat.lt_succ_of_le hk⟩ t ht).1
  have hGamma : ∀ k, k ≤ J -> ∀ t, t ∈ Icc (tau k) (if k < J then tau (k+1) else T) ->
      weightedSampleResidual (featureResidualWeight c p L) phi
        (fun m => ∫ u, phi m (Z z k u t) ∂ mu0) (fun i => (branches z k t).2 i) ≤
          sourceFinalGammaThreshold J N T alpha K0 D pTotal c C g p q B L := by
    intro k hk t ht
    let j : Fin (J+1) := ⟨k,Nat.lt_succ_of_le hk⟩
    have hg := hpG.2.2.2 j t ht
    have hCenters : (fun m => ∫ u, phi m (sourceReferencePathEval (Phi (finalEnv z) u) j t) ∂ mu0) =
        (fun m => ∫ u, phi m (Z z k u t) ∂ mu0) := by
      funext m
      apply integral_congr_ae
      filter_upwards [hRawEq] with u hu
      rw [hu j t ht]
    rw [hCenters] at hg
    exact hg.2
  have hLocal : ∀ k, k ≤ J -> ∀ t, t ∈ Icc (tau k) (if k < J then tau (k+1) else T) ->
      ∀ i, norm ((branches z k t).1 i) ≤ D ∧ norm ((branches z k t).2 i) ≤ D := by
    intro k hk t ht i
    exact ⟨hpG.2.2.1 0 i ⟨k,Nat.lt_succ_of_le hk⟩ t ht,
      hpG.2.2.1 1 i ⟨k,Nat.lt_succ_of_le hk⟩ t ht⟩
  have hPrePair (n : Fin J) (t : Real) := source_projected_recurrent_pre post flowX flowY initial innovation
    J n.val (Nat.succ_le_of_lt n.isLt) (project n) (horiginal n) (harray n) z t
  have hPostPair (n : Fin J) := source_projected_recurrent_post post flowX flowY initial innovation tau
    J n.val (Nat.succ_le_of_lt n.isLt) htime hXstart hYstart (project n) (horiginal n) (harray n) z
  have hPreLaw (n : Fin J) : mu0.map (fun u => Z z n.val u (tau (n.val+1))) =
      mu0.map (sourceReferencePre tau flowY (sourcePopulationFieldJump eta field) n
        (fun i => innovation i (sourceAuxiliaryOriginal J z))) := by
    congr 1
    funext u
    exact sourceFiniteReferenceBranch_original tau eta flowY field innovation J n.val n.isLt.le z u (tau (n.val+1))
  have hExponential (n : Fin J) :
      (∫⁻ x, ENNReal.ofReal (Real.exp ((norm x / scale)^alpha)) ∂
        mu0.map (sourceReferencePre tau flowY (sourcePopulationFieldJump eta field) n
          (fun i => innovation i (sourceAuxiliaryOriginal J z)))) ≤ 2 := by
    rw [<- hPreLaw n]
    exact sourceReferenceControl_exponential_eligibility mu0 _ a btime B alpha Kpop scale hControl
      ⟨n.val,Nat.lt_succ_of_lt n.isLt⟩ (tau (n.val+1))
      (by simp only [a,btime,sourceScheduleLeft,sourceScheduleRight,if_pos n.isLt]; exact ⟨(htime n n.isLt).le,le_rfl⟩)
  have hCov : ∀ k, k < J ->
      let muPre := mu0.map (fun u => Z z k u (tau (k+1)))
      matrixNuclearValue (populationCovarianceResidual muPre (fun i => (branches z k (tau (k+1))).2 i)
        (fun x => stackedKernelMatrix (fun i => actualMomentKernelMatrix F G
          (∫ y, F y ∂ muPre) ((branches z k (tau (k+1))).2 i) x))) / N ≤
          sourcePrescribedCovarianceEnvelope J N d c C g p q alpha Kpop L pTotal := by
    intro k hk
    let n : Fin J := ⟨k,hk⟩
    have hb := hoG.1 n (hExponential n)
    rw [hPrePair n (tau (k+1)), <- hPreLaw n] at hb
    exact hb
  have hXode := source_visited_empirical_coordinate_odes c p phi G
    (source_empirical_drift_contDiff_all_domains c C g p q alpha phi hc hC hp hq hphi hgrowth
      G U hU hDomains hG hN) tau J T htime hT post flowY
    (sourceTowerPacked innovation J z) (initial (sourceAuxiliaryOriginal J z)) hzM.2.1
  refine source_finite_horizon_tracking c C g p q alpha Kpop D scale C3 phi hc hC hp hq halpha hKpop hD
    hphi hgrowth hthirdphi hgrowth3 G U hU hDomains hG hthirdK L hL mu0 hN tau eta flowX flowY field
    J T B htau0 htime hT (sourceTowerPacked innovation J z) (initial (sourceAuxiliaryOriginal J z))
    hXstart hYstart (sourceFinalGammaThreshold J N T alpha K0 D pTotal c C g p q B L)
    (sourcePrescribedCovarianceEnvelope J N d c C g p q alpha Kpop L pTotal) pTotal finalLaw
    (fun n => SourceRecurrentHistory W N d n) (fun _ => SourceStepNormal N d × SourceStepNormal N d)
    views z hControl
    (fun k hk i => hzM.1 0 i ⟨k,Nat.lt_succ_of_le hk⟩)
    (fun k hk i => hzM.1 1 i ⟨k,Nat.lt_succ_of_le hk⟩) hLocal hXode hzM.2.2.2 hGamma hCov hoG.2
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ A_sp hAsp hsp hsmall
  . intro n
    exact (hviews n z).2.1.mpr (hExponential n)
  . intro n
    exact (hviews n z).2.2.2.1.trans (congrArg Prod.fst (hPrePair n (tau (n.val+1))))
  . intro n
    exact (hviews n z).2.2.2.2.1.trans (congrArg Prod.snd (hPrePair n (tau (n.val+1))))
  . intro n
    exact (hviews n z).2.2.2.2.2.1.trans (congrArg Prod.fst (hPostPair n))
  . intro n
    exact (hviews n z).2.2.2.2.2.2.trans (congrArg Prod.snd (hPostPair n))
  . intro n
    exact (hviews n z).1.trans (hPreLaw n).symm
  . intro n
    exact (hviews n z).2.2.1
end PaperFormalization.Manuscript
