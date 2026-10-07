import PaperFormalization.Manuscript.SourceRecurrentSchedule

/-! # All actual recurrent jump views on one final probability space
M13r verified unit (see CODEX_HANDOFF_M13R.md). Every stage view is constructed using the exact source seed
and states. The projections retain each auxiliary coordinate, not just the
original marginal. The population coefficient and all pre/post state identities
hold pointwise on the final tower. No independent-view assumption is used.
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
/-- A single original extension carries ALL constructed recurrent views. -/
theorem exists_source_recurrent_views_on_final_tower
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
    ∃ project : forall n : Fin J,
        SourceAuxiliarySpace O (SourceStepNormal N d) J -> SourceAuxiliarySpace O (SourceStepNormal N d) (n.val+1),
      (forall n, MeasurePreserving (project n) (sourceAuxiliaryMeasure nu normal J)
        (sourceAuxiliaryMeasure nu normal (n.val+1))) ∧
      (forall n z, sourceAuxiliaryOriginal J z = sourceAuxiliaryOriginal (n.val+1) (project n z)) ∧
      (forall n z (i : Fin (n.val+1)), sourceAuxiliaryArray (n.val+1) (project n z) i =
        sourceAuxiliaryArray J z (Fin.castLE (Nat.succ_le_of_lt n.isLt) i)) ∧
      ∃ views : forall n : Fin J, SourceObservedJumpView c p K D alpha phi G U hU (hDomains K hK D hD) hG hN
          (sourceAuxiliaryMeasure nu normal J) (SourceRecurrentHistory W N d n)
          (SourceStepNormal N d × SourceStepNormal N d),
        forall n : Fin J,
          let popLaw := characteristicKernel mu0 (fun (h : SourceRecurrentHistory W N d n) u =>
            sourceReferencePre tau flowY (sourcePopulationFieldJump eta field) n (sourceHistoryPopulation n h) u)
          (views n).κ = popLaw ∧
          (views n).PopGood = populationExponentialEligibility popLaw alpha scale ∧
          (views n).eta = eta n ∧
          forall z,
            (views n).κ ((views n).observation z).1 = mu0.map
              (sourceReferencePre tau flowY (sourcePopulationFieldJump eta field) n
                (fun i => innovation i (sourceAuxiliaryOriginal J z))) ∧
            (views n).X ((views n).observation z).1 =
              (sourceTowerBranch post flowX flowY initial innovation n (project n z).1 (tau (n.val+1))).1 ∧
            (views n).Y ((views n).observation z).1 =
              (sourceTowerBranch post flowX flowY initial innovation n (project n z).1 (tau (n.val+1))).2 ∧
            (views n).Xpost ((views n).observation z).1 ((views n).observation z).2 =
              (post (n.val+1) (sourceTowerPacked innovation (n.val+1) (project n z))
                (initial (sourceAuxiliaryOriginal J z))).1 ∧
            (views n).Ypost ((views n).observation z).1 ((views n).observation z).2 =
              (post (n.val+1) (sourceTowerPacked innovation (n.val+1) (project n z))
                (initial (sourceAuxiliaryOriginal J z))).2 := by
  classical
  let post := sourceActualFinitePost mu0 c p alpha phi G U hU hDomains hG hN tau eta flowX flowY field
  let normal := stdGaussian (SourceStepNormal N d)
  obtain ⟨stage, hs⟩ := exists_source_recurrent_views_at_all_stages
    c C g p q alpha K0 K D scale phi hc hC hp hq halpha hK0 hK hD hscale hKscale
    hphi hgrowth G U hU hDomains hG hN nu mu0 tau eta flowX flowY field hFX hFY hfield
    initial innovation hinit hInnovation J lambda i0 heta hPopIndependent hInitialLaw
    hFresh hInnovationLaw hMoment hField
  choose project hproject horiginal harray using fun n : Fin J =>
    exists_source_auxiliary_coordinate_prefix nu normal (n.val+1) J (Nat.succ_le_of_lt n.isLt)
  let views := fun n : Fin J => sourceJumpView_pullback (project n) (hproject n) (stage n)
  refine ⟨project, hproject, horiginal, harray, views, ?_⟩
  intro n
  rcases hs n with ⟨hk, hgate, hx, hy, he, hobs, hupdate⟩
  refine ⟨hk, hgate, he, ?_⟩
  intro z
  have hjump : forall k, Measurable (fun w : ((Fin k -> W) × W) × EuclideanSpace Real (Fin d) =>
      sourcePopulationFieldJump eta field k w.1.1 w.1.2 w.2) :=
    fun k => measurable_snd.add ((hfield k).const_smul (eta k))
  have hPhi := sourceReferenceBranch_measurable tau flowY (sourcePopulationFieldJump eta field)
    hFY hjump n (tau (n.val+1))
  have hPhiFull : Measurable (fun w : SourceRecurrentHistory W N d n × EuclideanSpace Real (Fin d) =>
      sourceReferencePre tau flowY (sourcePopulationFieldJump eta field) n (sourceHistoryPopulation n w.1) w.2) :=
    hPhi.comp (((sourceHistoryPopulation_measurable n).comp measurable_fst).prodMk measurable_snd)
  have hlaw : (views n).κ ((views n).observation z).1 = mu0.map
      (sourceReferencePre tau flowY (sourcePopulationFieldJump eta field) n
        (fun i => innovation i (sourceAuxiliaryOriginal J z))) := by
    change (stage n).κ ((stage n).observation (project n z)).1 = _
    rw [hk, hobs, (characteristicKernel_properties mu0 _ hPhiFull).2]
    simp only [sourceHistoryPopulation_observation]
    rw [horiginal n z]
    rfl
  have hu := hupdate (project n z)
  refine ⟨hlaw, hu.1, hu.2.1, ?_, ?_⟩
  · change (stage n).Xpost ((stage n).observation (project n z)).1
      ((stage n).observation (project n z)).2 = _
    rw [horiginal n z]
    exact hu.2.2.1
  · change (stage n).Ypost ((stage n).observation (project n z)).1
      ((stage n).observation (project n z)).2 = _
    rw [horiginal n z]
    exact hu.2.2.2
end PaperFormalization.Manuscript
