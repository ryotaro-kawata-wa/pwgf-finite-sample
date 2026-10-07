import PaperFormalization.Manuscript.SourceFixedCanonicalJumpView
import PaperFormalization.Manuscript.SourceRecurrentBranches

/-! # Apply the canonical law to the actual recurrent states at one tower level
M13r verified unit (see CODEX_HANDOFF_M13R.md). Original initial-prefix independence and fresh innovation
independence are transported through the concrete past-auxiliary tower. The
field premise is the original per-innovation finite-evaluation model, NOT an
assumed conditional Gaussian law or an assumed canonical-seed law.
-/
open Matrix MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory Matrix.Norms.Frobenius
namespace PaperFormalization.Manuscript
attribute [local instance] sourceGramMeasurableMatrix sourceGramBorelMatrix
variable {O W : Type*} [MeasurableSpace O] [MeasurableSpace W] {N d : Nat}
variable {H : Nat -> Type*} [forall n, NormedAddCommGroup (H n)]
  [forall n, InnerProductSpace Real (H n)] [forall n, CompleteSpace (H n)]

/-- The raw original population field is evaluated at the recurrent reference
configuration. It is not replaced by a whitened surrogate. -/
def sourceRawFieldVector
    (field : (n : Nat) -> (Fin n -> W) -> W -> EuclideanSpace Real (Fin d) -> EuclideanSpace Real (Fin d))
    (n : Nat) (past : Fin n -> W) (Y : SourceFiniteConfiguration N d) (w : W) :=
  particleFlatten (WithLp.toLp 2 (fun i => field n past w (Y i)))

theorem sourceRawFieldVector_measurable
    {S : Type*} [MeasurableSpace S]
    (field : (n : Nat) -> (Fin n -> W) -> W -> EuclideanSpace Real (Fin d) -> EuclideanSpace Real (Fin d))
    (hfield : forall n, Measurable (fun z : ((Fin n -> W) × W) × EuclideanSpace Real (Fin d) => field n z.1.1 z.1.2 z.2))
    (n : Nat) (past : S -> Fin n -> W) (hpast : Measurable past)
    (Y : S -> SourceFiniteConfiguration N d) (hY : Measurable Y) :
    Measurable (fun z : S × W => sourceRawFieldVector field n (past z.1) (Y z.1) z.2) := by
  apply sourceParticleFlatten_measurable.comp
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_lambda
  intro i
  exact (hfield n).comp (((hpast.comp measurable_fst).prodMk measurable_snd).prodMk
    ((((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 _)).comp hY).comp measurable_fst))

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
set_option maxHeartbeats 6000000 in
/-- The view's pre/post states and seed are those of sourceActualFinitePost at
THIS level, pointwise for every original/auxiliary outcome. Its laws are derived
from original-model inputs, not accepted as view fields. -/
theorem exists_source_recurrent_step_view
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
    (n : Nat) (lambda : Measure W) [IsProbabilityMeasure lambda] (i0 : Fin N)
    (heta : 0 ≤ eta n)
    (hPopIndependent : IndepFun (fun o (i : Fin n) => innovation i o) (fun o => initial o i0) nu)
    (hInitialLaw : nu.map (fun o => initial o i0) = mu0)
    (hFresh : IndepFun (sourceOriginalPrehistory initial innovation n) (innovation n) nu)
    (hInnovationLaw : nu.map (innovation n) = lambda)
    (hMoment : nu.map (fun o => sourceReferencePre tau flowY (sourcePopulationFieldJump eta field) n
      (fun i => innovation i o) (initial o i0)) ∈ sourceMomentClass alpha K0)
    (hField : let post := sourceActualFinitePost mu0 c p alpha phi G U hU hDomains hG hN tau eta flowX flowY field
      let normal := stdGaussian (SourceStepNormal N d)
      let hist := sourceAuxiliaryHistory (A := SourceStepNormal N d) (sourceOriginalPrehistory initial innovation n) n
      let Y := fun h : SourceRecurrentHistory W N d n => (sourceHistoryBranch post flowX flowY n h (tau (n+1))).2
      let popLaw := characteristicKernel mu0 (fun (h : SourceRecurrentHistory W N d n) u =>
        sourceReferencePre tau flowY (sourcePopulationFieldJump eta field) n (sourceHistoryPopulation n h) u)
      ∀ᵐ h ∂ (sourceAuxiliaryMeasure nu normal n).map hist,
        lambda.map (sourceRawFieldVector field n (sourceHistoryPopulation n h) (Y h)) =
          multivariateGaussian 0 (populationGramCovariance (popLaw h)
            (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix
              (sourceWeightedFeatureMap c p phi) G
              (∫ x, sourceWeightedFeatureMap c p phi x ∂ popLaw h) (Y h i) z)))) :
    let post := sourceActualFinitePost mu0 c p alpha phi G U hU hDomains hG hN tau eta flowX flowY field
    let normal := stdGaussian (SourceStepNormal N d)
    let hist := sourceAuxiliaryHistory (A := SourceStepNormal N d) (sourceOriginalPrehistory initial innovation n) n
    let pre := fun h : SourceRecurrentHistory W N d n => sourceHistoryBranch post flowX flowY n h (tau (n+1))
    let popLaw := characteristicKernel mu0 (fun (h : SourceRecurrentHistory W N d n) u =>
      sourceReferencePre tau flowY (sourcePopulationFieldJump eta field) n (sourceHistoryPopulation n h) u)
    ∃ view : SourceObservedJumpView c p K D alpha phi G U hU (hDomains K hK D hD) hG hN
      (sourceAuxiliaryMeasure nu normal (n+1)) (SourceRecurrentHistory W N d n)
      (SourceStepNormal N d × SourceStepNormal N d),
      view.κ = popLaw ∧ view.PopGood = populationExponentialEligibility popLaw alpha scale ∧
      view.X = (fun h => (pre h).1) ∧ view.Y = (fun h => (pre h).2) ∧ view.eta = eta n ∧
      (forall z, view.observation z = (hist z.1,
        (sourceRawFieldVector field n (sourceHistoryPopulation n (hist z.1)) (pre (hist z.1)).2
          (innovation n (sourceAuxiliaryOriginal n z.1)), z.2))) ∧
      (forall z,
        view.X ((view.observation z).1) = (sourceTowerBranch post flowX flowY initial innovation n z.1 (tau (n+1))).1 ∧
        view.Y ((view.observation z).1) = (sourceTowerBranch post flowX flowY initial innovation n z.1 (tau (n+1))).2 ∧
        view.Xpost (view.observation z).1 (view.observation z).2 =
          (post (n+1) (sourceTowerPacked innovation (n+1) z) (initial (sourceAuxiliaryOriginal (n+1) z))).1 ∧
        view.Ypost (view.observation z).1 (view.observation z).2 =
          (post (n+1) (sourceTowerPacked innovation (n+1) z) (initial (sourceAuxiliaryOriginal (n+1) z))).2) := by
  let post := sourceActualFinitePost mu0 c p alpha phi G U hU hDomains hG hN tau eta flowX flowY field
  let normal := stdGaussian (SourceStepNormal N d)
  let nuN := sourceAuxiliaryMeasure nu normal n
  let original := sourceAuxiliaryOriginal (O := O) (A := SourceStepNormal N d) n
  let hist := sourceAuxiliaryHistory (A := SourceStepNormal N d) (sourceOriginalPrehistory initial innovation n) n
  let past := sourceHistoryPopulation (W := W) (N := N) (d := d) n
  let pre := fun h : SourceRecurrentHistory W N d n => sourceHistoryBranch post flowX flowY n h (tau (n+1))
  let Phi := fun e u => sourceReferencePre tau flowY (sourcePopulationFieldJump eta field) n e u
  let popLaw := characteristicKernel mu0 (fun h u => Phi (past h) u)
  let raw := fun h w => sourceRawFieldVector field n (past h) (pre h).2 w
  have hproj := sourceAuxiliaryOriginal_preserving nu normal n
  have hH0 := sourceOriginalPrehistory_measurable initial innovation hinit hInnovation n
  have hH := sourceAuxiliaryHistory_measurable (A := SourceStepNormal N d) _ hH0 n
  have hpast := sourceHistoryPopulation_measurable (N := N) (d := d) (W := W) n
  have hi0 : Measurable (fun o => initial o i0) :=
    ((measurable_pi_apply i0).comp (WithLp.measurable_ofLp 2 _)).comp hinit
  have hPrefix : Measurable (fun o (i : Fin n) => innovation i o) :=
    measurable_pi_lambda _ (fun i => hInnovation i)
  have hpost := sourceActualFinitePost_measurable mu0 c C g p q alpha phi hc hC hp hq hphi hgrowth
    G U hU hDomains hG hN tau eta flowX flowY field hFX hFY hfield
  have hpre := sourceHistoryBranch_measurable post flowX flowY hpost hFX hFY n (tau (n+1))
  have hjump : forall k, Measurable (fun z : ((Fin k -> W) × W) × EuclideanSpace Real (Fin d) =>
      sourcePopulationFieldJump eta field k z.1.1 z.1.2 z.2) :=
    fun k => measurable_snd.add ((hfield k).const_smul (eta k))
  have hPhi := sourceReferenceBranch_measurable tau flowY (sourcePopulationFieldJump eta field)
    hFY hjump n (tau (n+1))
  have hpop : IndepFun (past ∘ hist) (fun z => initial (original z) i0) nuN := by
    have h := source_independence_pullback nu nuN original hproj
      (fun o (i : Fin n) => innovation i o) (fun o => initial o i0) hPrefix hi0 hPopIndependent
    simpa only [Function.comp_def, past, hist, sourceHistoryPopulation_observation] using h
  have hiLaw : nuN.map (fun z => initial (original z) i0) = mu0 := by
    change (sourceAuxiliaryMeasure nu normal n).map
      ((fun o => initial o i0) ∘ sourceAuxiliaryOriginal n) = mu0
    rw [← Measure.map_map hi0 hproj.measurable, hproj.map_eq]
    exact hInitialLaw
  have hmoment : nuN.map (fun z => Phi (past (hist z)) (initial (original z) i0)) ∈ sourceMomentClass alpha K0 := by
    have hm : Measurable (fun o => Phi (fun i : Fin n => innovation i o) (initial o i0)) :=
      hPhi.comp (hPrefix.prodMk hi0)
    have heq : (fun z => Phi (past (hist z)) (initial (original z) i0)) =
        (fun o => Phi (fun i : Fin n => innovation i o) (initial o i0)) ∘ original := by
      funext z
      simp only [Function.comp_def, past, hist, original, sourceHistoryPopulation_observation]
    rw [heq, ← Measure.map_map hm hproj.measurable, hproj.map_eq]
    exact hMoment
  have hfresh := source_auxiliary_history_fresh_independent nu normal
    (sourceOriginalPrehistory initial innovation n) (innovation n) hH0 (hInnovation n) hFresh n
  have hinnov := (source_auxiliary_innovation_marginal nu normal (innovation n) (hInnovation n) n).trans hInnovationLaw
  have heval := sourceRawFieldVector_measurable field hfield n past hpast (fun h => (pre h).2) hpre.snd
  obtain ⟨view, hk, hgate, hx, hy, he, hobs, hseed, hseedMeas, hxp, hyp⟩ :=
    exists_source_fixed_canonical_jump_view c C g p q alpha K0 K D scale phi hc hC hp hq
      halpha hK0 hK hD hscale hKscale hphi hgrowth G U hU hDomains hG hN
      nuN mu0 lambda hist past (fun z => initial (original z) i0) (innovation n ∘ original)
      hH hpast (hi0.comp hproj.measurable) ((hInnovation n).comp hproj.measurable)
      hpop hiLaw hfresh hinnov Phi hPhi hmoment
      (fun h => (pre h).1) (fun h => (pre h).2) hpre.fst hpre.snd (eta n) heta raw heval hField
  have hPhiFull : Measurable (fun z : SourceRecurrentHistory W N d n × EuclideanSpace Real (Fin d) => Phi (past z.1) z.2) :=
    hPhi.comp ((hpast.comp measurable_fst).prodMk measurable_snd)
  have hPhiPair : Measurable (fun z : ((Fin n -> W) × SourceFiniteConfiguration N d) × EuclideanSpace Real (Fin d) => Phi z.1.1 z.2) :=
    hPhi.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hversion (h : SourceRecurrentHistory W N d n) :
      sourcePopulationGramVersion popLaw (sourceWeightedFeatureMap c p phi) G U
        (sourceWeightedFeatureMap c p phi 0) (fun h i => (pre h).2 i) h =
      sourceActualCovarianceVersion mu0 c p phi G U tau eta flowY field n (past h) (pre h).2 := by
    unfold sourceActualCovarianceVersion
    apply sourcePopulationGramVersion_congr_at
    · rw [(characteristicKernel_properties mu0 _ hPhiFull).2 h,
        (characteristicKernel_properties mu0 _ hPhiPair).2 (past h, (pre h).2)]
    · rfl
  refine ⟨view, hk, hgate, hx, hy, he, ?_, ?_⟩
  · intro z
    exact congrFun hobs z
  · intro z
    have hpreid : pre (hist z.1) = sourceTowerBranch post flowX flowY initial innovation n z.1 (tau (n+1)) :=
      sourceHistoryBranch_observation post flowX flowY initial innovation n z.1 (tau (n+1))
    have hpopid : past (hist z.1) = (fun i : Fin n => innovation i (sourceAuxiliaryOriginal n z.1)) :=
      sourceHistoryPopulation_observation initial innovation n z.1
    have hnext := sourceActualFinitePost_tower_step mu0 c p alpha phi G U hU hDomains hG hN
      tau eta flowX flowY field initial innovation n z
    change post (n+1) (sourceTowerPacked innovation (n+1) z)
      (initial (sourceAuxiliaryOriginal (n+1) z)) = _ at hnext
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hobs, hx]
      exact congrArg Prod.fst hpreid
    · rw [hobs, hy]
      exact congrArg Prod.snd hpreid
    · apply sourceParticleFlattenIsometry.injective
      change particleFlatten (view.Xpost (view.observation z).1 (view.observation z).2) =
        particleFlatten ((post (n+1) (sourceTowerPacked innovation (n+1) z)
          (initial (sourceAuxiliaryOriginal (n+1) z))).1)
      rw [hobs, hxp]
      dsimp only
      rw [hversion, hnext]
      simp only [sourceCanonicalCoupledStep, particleFlatten_sourceParticleUnflatten,
        raw, sourceRawFieldVector, hpreid, hpopid, Function.comp_def, original]
      rfl
    · apply sourceParticleFlattenIsometry.injective
      change particleFlatten (view.Ypost (view.observation z).1 (view.observation z).2) =
        particleFlatten ((post (n+1) (sourceTowerPacked innovation (n+1) z)
          (initial (sourceAuxiliaryOriginal (n+1) z))).2)
      rw [hobs, hyp, hnext]
      simp only [sourceCanonicalCoupledStep, raw, sourceRawFieldVector,
        hpreid, hpopid, Function.comp_def, original]
      rfl
end PaperFormalization.Manuscript
