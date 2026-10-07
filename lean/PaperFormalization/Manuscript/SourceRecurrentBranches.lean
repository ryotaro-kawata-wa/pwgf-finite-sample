import PaperFormalization.Manuscript.SourceRecurrentCoordinates

/-! # Closed branches and exact updates of the actual finite recurrence
M13r verified unit (see CODEX_HANDOFF_M13R.md). Generic coordinate helpers are instantiated below with the
literal source recurrence. Endpoint identities are pointwise identities, not
assumptions of an already-compatible observed view.
-/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ProbabilityTheory Matrix.Norms.Frobenius
namespace PaperFormalization.Manuscript
variable {O W : Type*} {N d : Nat}

abbrev SourcePostMap (W : Type*) (N d : Nat) :=
  (n : Nat) -> (Fin n -> W × SourceStepNormal N d) -> SourceFiniteConfiguration N d ->
    SourceFiniteConfiguration N d × SourceFiniteConfiguration N d

/-- Follow the prescribed branch from its already constructed post-jump value. -/
def sourceCoupledBranch (post : SourcePostMap W N d)
    (flowX : Nat -> Real -> SourceFiniteConfiguration N d -> SourceFiniteConfiguration N d)
    (flowY : (n : Nat) -> (Fin n -> W) -> Real -> EuclideanSpace Real (Fin d) -> EuclideanSpace Real (Fin d))
    (n : Nat) (past : Fin n -> W × SourceStepNormal N d)
    (u : SourceFiniteConfiguration N d) (t : Real) :=
  (flowX n t (post n past u).1,
    WithLp.toLp 2 (fun i => flowY n (sourcePopulationPrefix past) t ((post n past u).2 i)))

def sourceHistoryBranch (post : SourcePostMap W N d) (flowX flowY)
    (n : Nat) (h : SourceRecurrentHistory W N d n) (t : Real) :=
  sourceCoupledBranch post flowX flowY n (sourceHistoryPacked n h) (sourceHistoryInitial n h) t

def sourceTowerBranch (post : SourcePostMap W N d) (flowX flowY)
    (initial : O -> SourceFiniteConfiguration N d) (innovation : Nat -> O -> W)
    (n : Nat) (z : SourceAuxiliarySpace O (SourceStepNormal N d) n) (t : Real) :=
  sourceCoupledBranch post flowX flowY n (sourceTowerPacked innovation n z)
    (initial (sourceAuxiliaryOriginal n z)) t

@[simp] theorem sourceHistoryBranch_observation
    (post : SourcePostMap W N d) (flowX flowY)
    (initial : O -> SourceFiniteConfiguration N d) (innovation : Nat -> O -> W)
    (n : Nat) (z : SourceAuxiliarySpace O (SourceStepNormal N d) n) (t : Real) :
    sourceHistoryBranch post flowX flowY n
      (sourceAuxiliaryHistory (sourceOriginalPrehistory initial innovation n) n z) t =
        sourceTowerBranch post flowX flowY initial innovation n z t := by
  simp only [sourceHistoryBranch, sourceTowerBranch, sourceHistoryPacked_observation,
    sourceHistoryInitial_observation]

theorem sourceCoupledBranch_start (post : SourcePostMap W N d) (flowX flowY)
    (tau : Nat -> Real)
    (hX : forall n x, flowX n (tau n) x = x)
    (hY : forall n h x, flowY n h (tau n) x = x)
    (n : Nat) (h : Fin n -> W × SourceStepNormal N d) (u : SourceFiniteConfiguration N d) :
    sourceCoupledBranch post flowX flowY n h u (tau n) = post n h u := by
  apply Prod.ext
  · exact hX n _
  · ext i j
    change flowY n (sourcePopulationPrefix h) (tau n) ((post n h u).2 i) j = _
    rw [hY]

section Measurable
variable [MeasurableSpace W]

theorem sourceCoupledBranch_measurable (post : SourcePostMap W N d) (flowX flowY)
    (hpost : forall n, Measurable (fun z : (Fin n -> W × SourceStepNormal N d) × SourceFiniteConfiguration N d => post n z.1 z.2))
    (hX : forall n t, Measurable (flowX n t))
    (hY : forall n t, Measurable (fun z : (Fin n -> W) × EuclideanSpace Real (Fin d) => flowY n z.1 t z.2))
    (n : Nat) (t : Real) :
    Measurable (fun z : (Fin n -> W × SourceStepNormal N d) × SourceFiniteConfiguration N d =>
      sourceCoupledBranch post flowX flowY n z.1 z.2 t) := by
  apply ((hX n t).comp (hpost n).fst).prodMk
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_lambda
  intro i
  exact (hY n t).comp
    (((sourcePopulationPrefix_measurable n).comp measurable_fst).prodMk
      (((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 _)).comp (hpost n).snd))

theorem sourceHistoryBranch_measurable (post : SourcePostMap W N d) (flowX flowY)
    (hpost : forall n, Measurable (fun z : (Fin n -> W × SourceStepNormal N d) × SourceFiniteConfiguration N d => post n z.1 z.2))
    (hX : forall n t, Measurable (flowX n t))
    (hY : forall n t, Measurable (fun z : (Fin n -> W) × EuclideanSpace Real (Fin d) => flowY n z.1 t z.2))
    (n : Nat) (t : Real) : Measurable (fun h : SourceRecurrentHistory W N d n =>
      sourceHistoryBranch post flowX flowY n h t) :=
  (sourceCoupledBranch_measurable post flowX flowY hpost hX hY n t).comp
    ((sourceHistoryPacked_measurable n).prodMk (sourceHistoryInitial_measurable n))
end Measurable

section Source
variable [MeasurableSpace W]
variable {H : Nat -> Type*} [forall n, NormedAddCommGroup (H n)]
  [forall n, InnerProductSpace Real (H n)] [forall n, CompleteSpace (H n)]
variable (mu0 : Measure (EuclideanSpace Real (Fin d)))
  (c p alpha : Real) (phi : forall n, EuclideanSpace Real (Fin d) -> H n)
  (G : lp H 2 -> Real) (U : Set (lp H 2)) (hU : IsOpen U)
  (hDomains : SourceAllMomentDomains (sourceWeightedFeatureMap c p phi) alpha U)
  (hG : ContDiffOn Real 2 G U) (hN : 0 < N)
  (tau eta : Nat -> Real) (flowX flowY field)

/-- The actual reference branch is the causal single-seed branch at every label. -/
theorem sourceActualFiniteBranch_reference (n : Nat)
    (h : Fin n -> W × SourceStepNormal N d) (u : SourceFiniteConfiguration N d) (t : Real) (i : Fin N) :
    (sourceCoupledBranch
      (sourceActualFinitePost mu0 c p alpha phi G U hU hDomains hG hN tau eta flowX flowY field)
      flowX flowY n h u t).2 i =
      sourceReferenceBranch tau flowY (sourcePopulationFieldJump eta field) n
        (sourcePopulationPrefix h) (u i) t := by
  change flowY n (sourcePopulationPrefix h) t
    ((sourceActualFinitePost mu0 c p alpha phi G U hU hDomains hG hN tau eta flowX flowY field n h u).2 i) = _
  rw [sourceActualFinitePost_reference]
  rfl

/-- The next post-state uses precisely the current raw field and the last
auxiliary, while the preceding state reads only the strict past. -/
theorem sourceActualFinitePost_tower_step
    (initial : O -> SourceFiniteConfiguration N d) (innovation : Nat -> O -> W)
    (n : Nat) (z : SourceAuxiliarySpace O (SourceStepNormal N d) (n+1)) :
    let post := sourceActualFinitePost mu0 c p alpha phi G U hU hDomains hG hN tau eta flowX flowY field
    let pre := sourceTowerBranch post flowX flowY initial innovation n z.1 (tau (n+1))
    let pop := fun i : Fin n => innovation i (sourceAuxiliaryOriginal n z.1)
    let v := WithLp.toLp 2 (fun i => field n pop (innovation n (sourceAuxiliaryOriginal n z.1)) (pre.2 i))
    post (n+1) (sourceTowerPacked innovation (n+1) z) (initial (sourceAuxiliaryOriginal (n+1) z)) =
      sourceCanonicalCoupledStep (sourceEmpiricalKernelFactor c p phi G)
        (source_empirical_factor_hermitian_all_domains c p alpha phi G U hU hDomains hG hN)
        (eta n) (sourceActualCovarianceVersion mu0 c p phi G U tau eta flowY field n pop pre.2)
        pre.1 pre.2 v z.2 := by
  simp only [sourceActualFinitePost, sourceCanonicalCoupledPost,
    sourceTowerPacked_init, sourceTowerPacked_last, sourceAuxiliaryOriginal,
    sourceTowerBranch, sourceCoupledBranch, sourcePopulationPrefix, sourceTowerPacked,
    sourceAuxiliaryArray_last, Fin.val_last]
  rfl
end Source
end PaperFormalization.Manuscript
