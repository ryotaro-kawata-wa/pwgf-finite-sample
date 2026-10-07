import PaperFormalization.Manuscript.SourceRecurrentBranches
import PaperFormalization.Manuscript.SourceReferencePathLaw
import PaperFormalization.Manuscript.SourceMomentLeftTrace

/-! # Original first-reference moments to actual recurrent reference marginals
M13r verified unit (see CODEX_HANDOFF_M13R.md). Reference coordinates share an unconditional law because of
original environment/seed independence and the common characteristic map.
Empirical exchangeability is NOT inferred here. The left-trace result invokes
the existing all-real-order Fatou theorem and keeps exactly the same scale.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped ProbabilityTheory Topology
namespace PaperFormalization.Manuscript

/-- A shared characteristic and equal independent seed laws give equal output
laws. Independence between the two seeds themselves is not needed. -/
theorem source_independent_characteristic_marginal_eq
    {O Env Seed E : Type*} [MeasurableSpace O] [MeasurableSpace Env]
    [MeasurableSpace Seed] [MeasurableSpace E]
    (nu : Measure O) [IsProbabilityMeasure nu] (mu0 : Measure Seed) [IsProbabilityMeasure mu0]
    (environment : O -> Env) (u v : O -> Seed)
    (he : Measurable environment) (hu : Measurable u) (hv : Measurable v)
    (hiu : IndepFun environment u nu) (hiv : IndepFun environment v nu)
    (hlu : nu.map u = mu0) (hlv : nu.map v = mu0)
    (Phi : Env -> Seed -> E) (hPhi : Measurable (fun z : Env × Seed => Phi z.1 z.2)) :
    nu.map (fun o => Phi (environment o) (u o)) =
      nu.map (fun o => Phi (environment o) (v o)) := by
  have ha := independent_single_characteristic_joint_law nu mu0 environment u he hu hiu hlu Phi hPhi
  have hb := independent_single_characteristic_joint_law nu mu0 environment v he hv hiv hlv Phi hPhi
  have h := congrArg (fun m : Measure (Env × E) => m.map Prod.snd) (ha.trans hb.symm)
  have hpu : Measurable (fun o => (environment o, Phi (environment o) (u o))) :=
    he.prodMk (hPhi.comp (he.prodMk hu))
  have hpv : Measurable (fun o => (environment o, Phi (environment o) (v o))) :=
    he.prodMk (hPhi.comp (he.prodMk hv))
  simpa only [Measure.map_map measurable_snd hpu,
    Measure.map_map measurable_snd hpv, Function.comp_def] using h

variable {O W : Type*} [MeasurableSpace O] [MeasurableSpace W] {N d : Nat}
variable {H : Nat -> Type*} [forall m, NormedAddCommGroup (H m)]
  [forall m, InnerProductSpace Real (H m)] [forall m, CompleteSpace (H m)]

/-- The actual reference recurrence on its tower has the distinguished
ORIGINAL coordinate's law at every time. No localized iid statement is used. -/
theorem sourceActualFiniteBranch_reference_marginal
    (nu : Measure O) [IsProbabilityMeasure nu]
    (mu0 : Measure (EuclideanSpace Real (Fin d))) [IsProbabilityMeasure mu0]
    (c p alpha : Real) (phi : forall m, EuclideanSpace Real (Fin d) -> H m)
    (G : lp H 2 -> Real) (U : Set (lp H 2)) (hU : IsOpen U)
    (hDomains : SourceAllMomentDomains (sourceWeightedFeatureMap c p phi) alpha U)
    (hG : ContDiffOn Real 2 G U) (hN : 0 < N)
    (tau eta : Nat -> Real) (flowX flowY field)
    (hFY : forall k t, Measurable (fun z : (Fin k -> W) × EuclideanSpace Real (Fin d) => flowY k z.1 t z.2))
    (hfield : forall k, Measurable (fun z : ((Fin k -> W) × W) × EuclideanSpace Real (Fin d) => field k z.1.1 z.1.2 z.2))
    (initial : O -> SourceFiniteConfiguration N d) (innovation : Nat -> O -> W)
    (hinit : Measurable initial) (hW : forall k, Measurable (innovation k))
    (n : Nat) (t : Real) (i i0 : Fin N)
    (hind : IndepFun (fun o (k : Fin n) => innovation k o) (fun o (j : Fin N) => initial o j) nu)
    (hlaw : forall j, nu.map (fun o => initial o j) = mu0) :
    let post := sourceActualFinitePost mu0 c p alpha phi G U hU hDomains hG hN tau eta flowX flowY field
    let normal := stdGaussian (SourceStepNormal N d)
    (sourceAuxiliaryMeasure nu normal n).map
      (fun z => (sourceTowerBranch post flowX flowY initial innovation n z t).2 i) =
      nu.map (fun o => sourceReferenceBranch tau flowY (sourcePopulationFieldJump eta field) n
        (fun k => innovation k o) (initial o i0) t) := by
  let post := sourceActualFinitePost mu0 c p alpha phi G U hU hDomains hG hN tau eta flowX flowY field
  let normal := stdGaussian (SourceStepNormal N d)
  let env := fun o (k : Fin n) => innovation k o
  let Phi := fun e u => sourceReferenceBranch tau flowY (sourcePopulationFieldJump eta field) n e u t
  have he : Measurable env := measurable_pi_lambda _ (fun k => hW k)
  have hi (j : Fin N) : Measurable (fun o => initial o j) :=
    ((measurable_pi_apply j).comp (WithLp.measurable_ofLp 2 _)).comp hinit
  have hjump : forall k, Measurable (fun z : ((Fin k -> W) × W) × EuclideanSpace Real (Fin d) =>
      sourcePopulationFieldJump eta field k z.1.1 z.1.2 z.2) :=
    fun k => measurable_snd.add ((hfield k).const_smul (eta k))
  have hPhi := sourceReferenceBranch_measurable tau flowY (sourcePopulationFieldJump eta field) hFY hjump n t
  have hcoord (j : Fin N) : IndepFun env (fun o => initial o j) nu := by
    simpa only [Function.comp_def, id_eq] using hind.comp measurable_id (measurable_pi_apply j)
  have hproj := sourceAuxiliaryOriginal_preserving nu normal n
  have hpoint : (fun z => (sourceTowerBranch post flowX flowY initial innovation n z t).2 i) =
      (fun o => Phi (env o) (initial o i)) ∘ sourceAuxiliaryOriginal n := by
    funext z
    exact sourceActualFiniteBranch_reference mu0 c p alpha phi G U hU hDomains hG hN
      tau eta flowX flowY field n (sourceTowerPacked innovation n z)
      (initial (sourceAuxiliaryOriginal n z)) t i
  change (sourceAuxiliaryMeasure nu normal n).map
    (fun z => (sourceTowerBranch post flowX flowY initial innovation n z t).2 i) =
    nu.map (fun o => Phi (env o) (initial o i0))
  have hPhiI : Measurable (fun o => Phi (env o) (initial o i)) := hPhi.comp (he.prodMk (hi i))
  rw [hpoint, ← Measure.map_map hPhiI hproj.measurable, hproj.map_eq]
  exact source_independent_characteristic_marginal_eq nu mu0 env (fun o => initial o i)
    (fun o => initial o i0) he (hi i) (hi i0) (hcoord i) (hcoord i0) (hlaw i) (hlaw i0) Phi hPhi

/-- Source first-reference bounds on the open branch imply the actual pre-law
moment class. The positive-length condition is used only for a genuine jump;
a singleton final branch is not subjected to this lemma. -/
theorem sourceReferencePre_moment_of_interior
    (nu : Measure O) [IsProbabilityMeasure nu]
    (alpha K : Real) (tau : Nat -> Real)
    (flow : (n : Nat) -> (Fin n -> W) -> Real -> EuclideanSpace Real (Fin d) -> EuclideanSpace Real (Fin d))
    (jump : (n : Nat) -> (Fin n -> W) -> W -> EuclideanSpace Real (Fin d) -> EuclideanSpace Real (Fin d))
    (hflow : forall k t, Measurable (fun z : (Fin k -> W) × EuclideanSpace Real (Fin d) => flow k z.1 t z.2))
    (hjump : forall k, Measurable (fun z : ((Fin k -> W) × W) × EuclideanSpace Real (Fin d) => jump k z.1.1 z.1.2 z.2))
    (n : Nat) (htime : tau n < tau (n+1))
    (past : O -> Fin n -> W) (initial : O -> EuclideanSpace Real (Fin d))
    (hpast : Measurable past) (hinit : Measurable initial)
    (hclass : ∀ t ∈ Ioo (tau n) (tau (n+1)),
      nu.map (fun o => sourceReferenceBranch tau flow jump n (past o) (initial o) t) ∈ sourceMomentClass alpha K)
    (hcont : ∀ᵐ o ∂ nu, ContinuousOn
      (sourceReferenceBranch tau flow jump n (past o) (initial o)) (Icc (tau n) (tau (n+1)))) :
    nu.map (fun o => sourceReferencePre tau flow jump n (past o) (initial o)) ∈ sourceMomentClass alpha K := by
  apply (sourceMomentClass_map_leftTrace nu alpha K (tau n) (tau (n+1)) htime
    (fun t o => sourceReferenceBranch tau flow jump n (past o) (initial o) t)
    (fun o => sourceReferencePre tau flow jump n (past o) (initial o)) ?_ hclass ?_).2
  · intro t ht
    exact ((sourceReferenceBranch_measurable tau flow jump hflow hjump n t).comp
      (hpast.prodMk hinit)).aestronglyMeasurable
  · have hleft : Tendsto (fun t : Real => t) (nhdsWithin (tau (n+1)) (Iio (tau (n+1))))
        (nhdsWithin (tau (n+1)) (Icc (tau n) (tau (n+1)))) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨nhdsWithin_le_nhds, ?_⟩
      filter_upwards [Ioo_mem_nhdsLT htime] with t ht
      exact ⟨ht.1.le, ht.2.le⟩
    filter_upwards [hcont] with o ho
    exact Filter.Tendsto.comp (ho (tau (n+1)) ⟨htime.le, le_rfl⟩) hleft
end PaperFormalization.Manuscript
