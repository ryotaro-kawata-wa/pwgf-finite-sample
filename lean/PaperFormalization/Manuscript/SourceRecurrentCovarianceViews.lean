import PaperFormalization.Manuscript.SourceFinalRecurrentViews
import PaperFormalization.Manuscript.SourceScheduledCovariance

/-! # Actual covariance samples on the final recurrent extension
M13r verified unit (see CODEX_HANDOFF_M13R.md). These views are built from the original iid array, not supplied
as unrelated covariance observations. The reference-recursion identity removes
auxiliary dependence from the sample and identifies the exact population law.
-/
open Matrix MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
namespace PaperFormalization.Manuscript
variable {O W : Type*} [MeasurableSpace O] [MeasurableSpace W] {N d : Nat}
variable {H : Nat -> Type*} [forall n, NormedAddCommGroup (H n)]
  [forall n, InnerProductSpace Real (H n)] [forall n, CompleteSpace (H n)]

set_option backward.isDefEq.respectTransparency false in
set_option maxSynthPendingDepth 10 in
set_option maxHeartbeats 4000000 in
/-- On the same final law, covariance sample/pre-law identities follow from the
original initial array and the concrete recurrent reference, for every jump. -/
theorem exists_source_recurrent_covariance_views
    (nu : Measure O) [IsProbabilityMeasure nu]
    (mu0 : Measure (EuclideanSpace Real (Fin d))) [IsProbabilityMeasure mu0]
    (c p alpha scale : Real) (halpha : 0 < alpha) (hscale : 0 < scale)
    (phi : forall m, EuclideanSpace Real (Fin d) -> H m)
    (G : lp H 2 -> Real) (U : Set (lp H 2)) (hU : IsOpen U)
    (hDomains : SourceAllMomentDomains (sourceWeightedFeatureMap c p phi) alpha U)
    (hG : ContDiffOn Real 2 G U) (hN : 0 < N)
    (tau eta : Nat -> Real) (flowX flowY field)
    (hFY : forall n t, Measurable (fun z : (Fin n -> W) × EuclideanSpace Real (Fin d) => flowY n z.1 t z.2))
    (hfield : forall n, Measurable (fun z : ((Fin n -> W) × W) × EuclideanSpace Real (Fin d) => field n z.1.1 z.1.2 z.2))
    (initial : O -> SourceFiniteConfiguration N d) (innovation : Nat -> O -> W)
    (hinit : Measurable initial) (hInnovation : forall n, Measurable (innovation n))
    (hiid : iIndepFun (fun i o => initial o i) nu)
    (hlaw : forall i, nu.map (fun o => initial o i) = mu0)
    (J : Nat)
    (hPopIndependent : forall n : Fin J,
      IndepFun (fun o (i : Fin n.val) => innovation i o) (fun o (i : Fin N) => initial o i) nu)
    (project : forall n : Fin J, SourceAuxiliarySpace O (SourceStepNormal N d) J ->
      SourceAuxiliarySpace O (SourceStepNormal N d) (n.val+1))
    (hOriginal : forall n z, sourceAuxiliaryOriginal J z = sourceAuxiliaryOriginal (n.val+1) (project n z)) :
    let K := sourceExponentialMomentCoefficient alpha * scale
    let normal := stdGaussian (SourceStepNormal N d)
    let post := sourceActualFinitePost mu0 c p alpha phi G U hU hDomains hG hN tau eta flowX flowY field
    ∃ views : forall n : Fin J, SourceObservedCovarianceView N d alpha K
        (sourceAuxiliaryMeasure nu normal J) (Fin n.val -> W) (Fin N -> EuclideanSpace Real (Fin d)),
      forall n z,
        (views n).X ((views n).observation z) =
          (fun i => (sourceTowerBranch post flowX flowY initial innovation n (project n z).1 (tau (n.val+1))).2 i) ∧
        (views n).κ ((views n).observation z).1 = mu0.map
          (sourceReferencePre tau flowY (sourcePopulationFieldJump eta field) n
            (fun i => innovation i (sourceAuxiliaryOriginal J z))) ∧
        (((views n).observation z).1 ∈ (views n).PopGood ↔
          (∫⁻ x, ENNReal.ofReal (Real.exp ((norm x / scale)^alpha)) ∂
            mu0.map (sourceReferencePre tau flowY (sourcePopulationFieldJump eta field) n
              (fun i => innovation i (sourceAuxiliaryOriginal J z)))) ≤ 2) := by
  classical
  let normal := stdGaussian (SourceStepNormal N d)
  have hinit' : forall i, Measurable (fun o => initial o i) := fun i =>
    ((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 _)).comp hinit
  have hjump : forall k, Measurable (fun z : ((Fin k -> W) × W) × EuclideanSpace Real (Fin d) =>
      sourcePopulationFieldJump eta field k z.1.1 z.1.2 z.2) :=
    fun k => measurable_snd.add ((hfield k).const_smul (eta k))
  let env := fun (n : Fin J) (o : O) (i : Fin n.val) => innovation i o
  have henv (n : Fin J) : Measurable (env n) := measurable_pi_lambda _ (fun i => hInnovation i)
  let Phi := fun (n : Fin J) e u => sourceReferencePre tau flowY (sourcePopulationFieldJump eta field) n e u
  have hPhi (n : Fin J) : Measurable (fun z : (Fin n.val -> W) × EuclideanSpace Real (Fin d) => Phi n z.1 z.2) :=
    sourceReferenceBranch_measurable tau flowY (sourcePopulationFieldJump eta field) hFY hjump n (tau (n.val+1))
  let base := fun n : Fin J => sourceOriginalCovarianceView nu mu0 (env n)
    (fun i o => initial o i) (henv n) hinit' hiid (hPopIndependent n) hlaw
    (Phi n) (hPhi n) alpha scale halpha hscale
  let views := fun n : Fin J => sourceCovarianceView_on_auxiliaryTower nu normal (base n) J
  refine ⟨views, ?_⟩
  intro n z
  have hfields (k : Nat) :
      (sourceCovarianceView_on_auxiliaryTower nu normal (base n) k).X = (base n).X ∧
      (sourceCovarianceView_on_auxiliaryTower nu normal (base n) k).κ = (base n).κ ∧
      (sourceCovarianceView_on_auxiliaryTower nu normal (base n) k).PopGood = (base n).PopGood := by
    induction k with
    | zero => exact ⟨rfl, rfl, rfl⟩
    | succ k ih => exact ih
  have ho := sourceCovarianceView_on_auxiliaryTower_observation nu normal (base n) J
  have hsample : (views n).X ((views n).observation z) =
      (fun i => Phi n (env n (sourceAuxiliaryOriginal J z)) (initial (sourceAuxiliaryOriginal J z) i)) := by
    rw [(hfields J).1]
    rw [ho]
    rfl
  have hk : (views n).κ ((views n).observation z).1 =
      mu0.map (Phi n (env n (sourceAuxiliaryOriginal J z))) := by
    rw [(hfields J).2.1]
    rw [ho]
    exact (characteristicKernel_properties mu0 (Phi n) (hPhi n)).2 _
  refine ⟨?_, hk, ?_⟩
  · rw [hsample]
    funext i
    change Phi n (env n (sourceAuxiliaryOriginal J z)) (initial (sourceAuxiliaryOriginal J z) i) =
      (sourceCoupledBranch _ flowX flowY n _ _ (tau (n.val+1))).2 i
    rw [sourceActualFiniteBranch_reference, hOriginal n z]
    rfl
  · rw [(hfields J).2.2]
    change ((∫⁻ x, ENNReal.ofReal (Real.exp ((norm x / scale)^alpha)) ∂
      (base n).κ ((views n).observation z).1) ≤ 2) ↔ _
    rw [← (hfields J).2.1, hk]
end PaperFormalization.Manuscript
