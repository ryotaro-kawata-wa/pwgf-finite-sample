import PaperFormalization.Manuscript.SourceRecurrentCovarianceViews
import PaperFormalization.Manuscript.SourceObservedTrackingSchedule

/-! # Actual recurrent covariance and jump event on one final law
M13r verified unit (see CODEX_HANDOFF_M13R.md). Both observed families are constructed from the original model
and the concrete canonical recurrence. All pre/post/coefficient/sample identities
are proved. The exact covariance/jump allocation is retained. The eligibility
gate is an explicit exponential moment condition on the actual coefficient;
this event alone does not pay for the population/Gamma/radius event.
-/
open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal ProbabilityTheory Matrix.Norms.Frobenius
namespace PaperFormalization.Manuscript
attribute [local instance] sourceGramMeasurableMatrix sourceGramBorelMatrix
variable {O W : Type*} [MeasurableSpace O] [MeasurableSpace W] {N d : Nat}
variable {H : Nat -> Type*} [forall n, NormedAddCommGroup (H n)]
  [forall n, InnerProductSpace Real (H n)] [forall n, CompleteSpace (H n)]
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
set_option maxHeartbeats 6000000 in
/-- No covariance/jump views, law identities or comparison inequalities are input.
They are derived for the actual finite recurrence from original-model data. -/
theorem exists_source_recurrent_observation_event
    (c C g p q alpha K0 K D scale C3 : Real)
    (phi : forall m, EuclideanSpace Real (Fin d) -> H m)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (halpha : 0 < alpha) (hK0 : 0 < K0) (hK : 0 < K) (hD : 1 ≤ D)
    (hscale : 0 < scale) (hKscale : K = sourceExponentialMomentCoefficient alpha * scale)
    (hphi : forall m, ContDiff Real 2 (phi m))
    (hgrowth : forall m z k, k ≤ 2 -> norm (iteratedFDeriv Real k (phi m) z) ≤
      featureGrowth C g q m * (1 + norm z ^ (m+1-k)))
    (G : lp H 2 -> Real) (U : Set (lp H 2)) (hU : IsOpen U)
    (hDomains : SourceAllMomentDomains (sourceWeightedFeatureMap c p phi) alpha U)
    (hG : ContDiffOn Real 3 G U)
    (hthirdG : ∀ theta ∈ measureMomentRegion (sourceWeightedFeatureMap c p phi)
      (sourceMomentClass alpha K) D, norm (iteratedFDeriv Real 3 G theta) ≤ C3)
    (L : NNReal) (hL : (L : Real) = sourceComparisonEnvelope c C g p q K D alpha C3 phi G)
    (hN : 0 < N)
    (nu : Measure O) [IsProbabilityMeasure nu]
    (mu0 : Measure (EuclideanSpace Real (Fin d))) [IsProbabilityMeasure mu0]
    (tau eta : Nat -> Real) (flowX flowY field)
    (hFX : forall n t, Measurable (flowX n t))
    (hFY : forall n t, Measurable (fun z : (Fin n -> W) × EuclideanSpace Real (Fin d) => flowY n z.1 t z.2))
    (hfield : forall n, Measurable (fun z : ((Fin n -> W) × W) × EuclideanSpace Real (Fin d) => field n z.1.1 z.1.2 z.2))
    (initial : O -> SourceFiniteConfiguration N d) (innovation : Nat -> O -> W)
    (hinit : Measurable initial) (hInnovation : forall n, Measurable (innovation n))
    (J : Nat) (lambda : Fin J -> Measure W) [forall n, IsProbabilityMeasure (lambda n)] (i0 : Fin N)
    (heta : forall n : Fin J, 0 ≤ eta n)
    (hPopIndependent : forall n : Fin J, IndepFun (fun o (i : Fin n.val) => innovation i o) (fun o (i : Fin N) => initial o i) nu)
    (hiid : iIndepFun (fun i o => initial o i) nu)
    (hInitialLaw : forall i, nu.map (fun o => initial o i) = mu0)
    (hFresh : forall n : Fin J, IndepFun (sourceOriginalPrehistory initial innovation n) (innovation n) nu)
    (hInnovationLaw : forall n : Fin J, nu.map (innovation n) = lambda n)
    (hMoment : forall n : Fin J, nu.map (fun o => sourceReferencePre tau flowY (sourcePopulationFieldJump eta field) n
      (fun i => innovation i o) (initial o i0)) ∈ sourceMomentClass alpha K0)
    (hField : forall n : Fin J, let post := sourceActualFinitePost mu0 c p alpha phi G U hU hDomains (hG.of_le (by norm_num)) hN tau eta flowX flowY field
      let normal := stdGaussian (SourceStepNormal N d)
      let hist := sourceAuxiliaryHistory (A := SourceStepNormal N d) (sourceOriginalPrehistory initial innovation n) n
      let Y := fun h : SourceRecurrentHistory W N d n => (sourceHistoryBranch post flowX flowY n h (tau (n.val+1))).2
      let popLaw := characteristicKernel mu0 (fun (h : SourceRecurrentHistory W N d n) u =>
        sourceReferencePre tau flowY (sourcePopulationFieldJump eta field) n (sourceHistoryPopulation n h) u)
      ∀ᵐ h ∂ (sourceAuxiliaryMeasure nu normal n).map hist,
        (lambda n).map (sourceRawFieldVector field n (sourceHistoryPopulation n h) (Y h)) =
          multivariateGaussian 0 (populationGramCovariance (popLaw h)
            (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix
              (sourceWeightedFeatureMap c p phi) G
              (∫ x, sourceWeightedFeatureMap c p phi x ∂ popLaw h) (Y h i) z))))
    (pTotal : Real) (hpTotal : 0 < pTotal) (hpTotal1 : pTotal < 1) :
    let post := sourceActualFinitePost mu0 c p alpha phi G U hU hDomains (hG.of_le (by norm_num)) hN tau eta flowX flowY field
    let normal := stdGaussian (SourceStepNormal N d)
    let finalLaw := sourceAuxiliaryMeasure nu normal J
    let F := sourceWeightedFeatureMap c p phi
    ∃ project : forall n : Fin J,
        SourceAuxiliarySpace O (SourceStepNormal N d) J -> SourceAuxiliarySpace O (SourceStepNormal N d) (n.val+1),
      (forall n, MeasurePreserving (project n) finalLaw (sourceAuxiliaryMeasure nu normal (n.val+1))) ∧
      (forall n z, sourceAuxiliaryOriginal J z = sourceAuxiliaryOriginal (n.val+1) (project n z)) ∧
      (forall n z (i : Fin (n.val+1)), sourceAuxiliaryArray (n.val+1) (project n z) i =
        sourceAuxiliaryArray J z (Fin.castLE (Nat.succ_le_of_lt n.isLt) i)) ∧
      ∃ views : forall n : Fin J, SourceObservedJumpView c p K D alpha phi G U hU
          (hDomains K hK D hD) (hG.of_le (by norm_num)) hN finalLaw (SourceRecurrentHistory W N d n)
          (SourceStepNormal N d × SourceStepNormal N d),
        (forall (n : Fin J) z,
          let pre := sourceTowerBranch post flowX flowY initial innovation n (project n z).1 (tau (n.val+1))
          let pop := mu0.map (sourceReferencePre tau flowY (sourcePopulationFieldJump eta field) n
            (fun i => innovation i (sourceAuxiliaryOriginal J z)))
          (views n).κ ((views n).observation z).1 = pop ∧
          ((((views n).observation z).1 ∈ (views n).PopGood) ↔
            (∫⁻ x, ENNReal.ofReal (Real.exp ((norm x / scale)^alpha)) ∂ pop) ≤ 2) ∧
          (views n).eta = eta n ∧
          (views n).X ((views n).observation z).1 = pre.1 ∧
          (views n).Y ((views n).observation z).1 = pre.2 ∧
          (views n).Xpost ((views n).observation z).1 ((views n).observation z).2 =
            (post (n.val+1) (sourceTowerPacked innovation (n.val+1) (project n z))
              (initial (sourceAuxiliaryOriginal J z))).1 ∧
          (views n).Ypost ((views n).observation z).1 ((views n).observation z).2 =
            (post (n.val+1) (sourceTowerPacked innovation (n.val+1) (project n z))
              (initial (sourceAuxiliaryOriginal J z))).2) ∧
        ∃ Good : Set (SourceAuxiliarySpace O (SourceStepNormal N d) J), MeasurableSet Good ∧
          finalLaw.real Goodᶜ ≤ ((J : Real) / ((J : Real) + 1)) * (5 * pTotal / 32) ∧
          finalLaw.real Goodᶜ < pTotal / 4 ∧
          ∀ z ∈ Good,
            (forall n : Fin J,
              let pop := mu0.map (sourceReferencePre tau flowY (sourcePopulationFieldJump eta field) n
                (fun i => innovation i (sourceAuxiliaryOriginal J z)))
              let Y := (sourceTowerBranch post flowX flowY initial innovation n (project n z).1 (tau (n.val+1))).2
              (∫⁻ x, ENNReal.ofReal (Real.exp ((norm x / scale)^alpha)) ∂ pop) ≤ 2 ->
                matrixNuclearValue (populationCovarianceResidual pop (fun i => Y i)
                  (fun x => stackedKernelMatrix (fun i => actualMomentKernelMatrix F G
                    (∫ y, F y ∂ pop) (Y i) x))) / N ≤
                  sourcePrescribedCovarianceEnvelope J N d c C g p q alpha K L pTotal) ∧
            (forall n : Fin J, (views n).observation z ∉ actualSourceJumpFailure c C g p q D phi G L
              (views n).PopGood (fun h => (views n).κ h) (views n).X (views n).Y
              (views n).Xpost (views n).Ypost (views n).eta (pTotal / (8 * ((J : Real) + 1)))) := by
  classical
  let normal := stdGaussian (SourceStepNormal N d)
  let finalLaw := sourceAuxiliaryMeasure nu normal J
  let post := sourceActualFinitePost mu0 c p alpha phi G U hU hDomains (hG.of_le (by norm_num)) hN tau eta flowX flowY field
  have hPopCoord (n : Fin J) : IndepFun (fun o (i : Fin n.val) => innovation i o) (fun o => initial o i0) nu := by
    simpa only [Function.comp_def, id_eq] using
      (hPopIndependent n).comp measurable_id (measurable_pi_apply i0)
  obtain ⟨project, hproject, horiginal, harray, jump, hjump⟩ :=
    exists_source_recurrent_views_on_final_tower
      c C g p q alpha K0 K D scale phi hc hC hp hq halpha hK0 hK hD hscale hKscale
      hphi hgrowth G U hU hDomains (hG.of_le (by norm_num)) hN nu mu0 tau eta flowX flowY field hFX hFY hfield
      initial innovation hinit hInnovation J lambda i0 heta hPopCoord (hInitialLaw i0)
      hFresh hInnovationLaw hMoment hField
  have hcovExists : ∃ cov : forall n : Fin J, SourceObservedCovarianceView N d alpha K finalLaw
        (Fin n.val -> W) (Fin N -> EuclideanSpace Real (Fin d)),
      forall n z,
        (cov n).X ((cov n).observation z) =
          (fun i => (sourceTowerBranch post flowX flowY initial innovation n (project n z).1 (tau (n.val+1))).2 i) ∧
        (cov n).κ ((cov n).observation z).1 = mu0.map
          (sourceReferencePre tau flowY (sourcePopulationFieldJump eta field) n
            (fun i => innovation i (sourceAuxiliaryOriginal J z))) ∧
        (((cov n).observation z).1 ∈ (cov n).PopGood ↔
          (∫⁻ x, ENNReal.ofReal (Real.exp ((norm x / scale)^alpha)) ∂
            mu0.map (sourceReferencePre tau flowY (sourcePopulationFieldJump eta field) n
              (fun i => innovation i (sourceAuxiliaryOriginal J z)))) ≤ 2) := by
    rw [hKscale]
    exact exists_source_recurrent_covariance_views nu mu0 c p alpha scale halpha hscale phi G U hU hDomains
      (hG.of_le (by norm_num)) hN tau eta flowX flowY field hFY hfield initial innovation hinit hInnovation
      hiid hInitialLaw J hPopIndependent project horiginal
  obtain ⟨cov, hcov⟩ := hcovExists
  obtain ⟨Good, hGood, hbudget, hstrict, hvalid⟩ := exists_source_observed_tracking_schedule_event
    J c C g p q K D alpha C3 phi hc hC hp hq halpha hK hD hphi hgrowth
    G U hU (hDomains K hK D hD) hG hthirdG L hL hN finalLaw
    (fun n => Fin n.val -> W) (fun _ => Fin N -> EuclideanSpace Real (Fin d))
    (fun n => SourceRecurrentHistory W N d n) (fun _ => SourceStepNormal N d × SourceStepNormal N d)
    cov jump pTotal hpTotal hpTotal1 (fun _ => True) (by simp)
  refine ⟨project, hproject, horiginal, harray, jump, ?_, Good, hGood, hbudget, hstrict, ?_⟩
  · intro n z
    have hj := hjump n
    have hh := hj.2.2.2 z
    refine ⟨hh.1, ?_, hj.2.2.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2⟩
    rw [hj.2.1, ← hj.1]
    change ((∫⁻ x, ENNReal.ofReal (Real.exp ((norm x / scale)^alpha)) ∂
      (jump n).κ ((jump n).observation z).1) ≤ 2) ↔ _
    rw [hh.1]
  · intro z hz
    refine ⟨?_, (hvalid z hz).2.2⟩
    intro n
    dsimp only
    intro helig
    have hgood := (hcov n z).2.2.mpr helig
    have hb := (hvalid z hz).2.1 n hgood
    rw [(hcov n z).2.1, (hcov n z).1] at hb
    exact hb
end PaperFormalization.Manuscript
