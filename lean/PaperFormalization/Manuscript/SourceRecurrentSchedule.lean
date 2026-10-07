import PaperFormalization.Manuscript.SourceRecurrentStepView

/-! # Apply the fixed canonical construction at every prescribed stage
M13r verified unit (see CODEX_HANDOFF_M13R.md). The stage family is CONSTRUCTED by the source theorem, not
supplied as an unrelated family of views. Each view has the actual recurrent
pre/post states, with its own primitive field measure and exactly the past
auxiliaries. This theorem neither conditions on a future event nor asserts
independence of different view observations.
-/
open Matrix MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory Matrix.Norms.Frobenius
namespace PaperFormalization.Manuscript
attribute [local instance] sourceGramMeasurableMatrix sourceGramBorelMatrix
variable {O W : Type*} [MeasurableSpace O] [MeasurableSpace W] {N d : Nat}
variable {H : Nat -> Type*} [forall n, NormedAddCommGroup (H n)]
  [forall n, InnerProductSpace Real (H n)] [forall n, CompleteSpace (H n)]
set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
set_option maxHeartbeats 6000000 in
/-- A finite family of source-model views, each validated for the same concrete
recurrence. Freshness, reference moments and raw field data are supplied only
under the source-model laws; no derived observation or seed law is a premise. -/
theorem exists_source_recurrent_views_at_all_stages
    (c C g p q alpha K0 K D scale : Real)
    (phi : forall m, EuclideanSpace Real (Fin d) -> H m)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (halpha : 0 < alpha) (hK0 : 0 < K0) (hK : 0 < K) (hD : 1 ≤ D)
    (hscale : 0 < scale) (hKscale : K = sourceExponentialMomentCoefficient alpha * scale)
    (hphi : forall m, ContDiff Real 2 (phi m))
    (hgrowth : forall m z k, k ≤ 2 -> norm (iteratedFDeriv Real k (phi m) z) ≤
      featureGrowth C g q m * (1 + norm z ^ (m+1-k)))
    (G : lp H 2 -> Real) (U : Set (lp H 2)) (hU : IsOpen U)
    (hDomains : SourceAllMomentDomains (sourceWeightedFeatureMap c p phi) alpha U)
    (hG : ContDiffOn Real 2 G U) (hN : 0 < N)
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
    (hPopIndependent : forall n : Fin J, IndepFun (fun o (i : Fin n.val) => innovation i o) (fun o => initial o i0) nu)
    (hInitialLaw : nu.map (fun o => initial o i0) = mu0)
    (hFresh : forall n : Fin J, IndepFun (sourceOriginalPrehistory initial innovation n) (innovation n) nu)
    (hInnovationLaw : forall n : Fin J, nu.map (innovation n) = lambda n)
    (hMoment : forall n : Fin J, nu.map (fun o => sourceReferencePre tau flowY (sourcePopulationFieldJump eta field) n
      (fun i => innovation i o) (initial o i0)) ∈ sourceMomentClass alpha K0)
    (hField : forall n : Fin J, let post := sourceActualFinitePost mu0 c p alpha phi G U hU hDomains hG hN tau eta flowX flowY field
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
              (∫ x, sourceWeightedFeatureMap c p phi x ∂ popLaw h) (Y h i) z)))) :
    let post := sourceActualFinitePost mu0 c p alpha phi G U hU hDomains hG hN tau eta flowX flowY field
    let normal := stdGaussian (SourceStepNormal N d)
    ∃ views : forall n : Fin J, SourceObservedJumpView c p K D alpha phi G U hU (hDomains K hK D hD) hG hN
      (sourceAuxiliaryMeasure nu normal (n.val+1)) (SourceRecurrentHistory W N d n)
      (SourceStepNormal N d × SourceStepNormal N d),
      forall n : Fin J,
        let hist := sourceAuxiliaryHistory (A := SourceStepNormal N d) (sourceOriginalPrehistory initial innovation n) n
        let pre := fun h : SourceRecurrentHistory W N d n => sourceHistoryBranch post flowX flowY n h (tau (n.val+1))
        let popLaw := characteristicKernel mu0 (fun (h : SourceRecurrentHistory W N d n) u =>
          sourceReferencePre tau flowY (sourcePopulationFieldJump eta field) n (sourceHistoryPopulation n h) u)
        (views n).κ = popLaw ∧ (views n).PopGood = populationExponentialEligibility popLaw alpha scale ∧
        (views n).X = (fun h => (pre h).1) ∧ (views n).Y = (fun h => (pre h).2) ∧ (views n).eta = eta n ∧
        (forall z, (views n).observation z = (hist z.1,
          (sourceRawFieldVector field n (sourceHistoryPopulation n (hist z.1)) (pre (hist z.1)).2
            (innovation n (sourceAuxiliaryOriginal n z.1)), z.2))) ∧
        (forall z,
          (views n).X (((views n).observation z).1) = (sourceTowerBranch post flowX flowY initial innovation n z.1 (tau (n.val+1))).1 ∧
          (views n).Y (((views n).observation z).1) = (sourceTowerBranch post flowX flowY initial innovation n z.1 (tau (n.val+1))).2 ∧
          (views n).Xpost ((views n).observation z).1 ((views n).observation z).2 =
            (post (n.val+1) (sourceTowerPacked innovation (n.val+1) z) (initial (sourceAuxiliaryOriginal (n.val+1) z))).1 ∧
          (views n).Ypost ((views n).observation z).1 ((views n).observation z).2 =
            (post (n.val+1) (sourceTowerPacked innovation (n.val+1) z) (initial (sourceAuxiliaryOriginal (n.val+1) z))).2)
 := by
  classical
  have hstep (n : Fin J) := exists_source_recurrent_step_view
    c C g p q alpha K0 K D scale phi hc hC hp hq halpha hK0 hK hD hscale hKscale
    hphi hgrowth G U hU hDomains hG hN nu mu0 tau eta flowX flowY field hFX hFY hfield
    initial innovation hinit hInnovation n (lambda n) i0 (heta n) (hPopIndependent n)
    hInitialLaw (hFresh n) (hInnovationLaw n) (hMoment n) (hField n)
  exact ⟨fun n => Classical.choose (hstep n), fun n => Classical.choose_spec (hstep n)⟩
end PaperFormalization.Manuscript
