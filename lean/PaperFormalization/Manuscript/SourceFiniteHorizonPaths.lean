import PaperFormalization.Manuscript.SourceRecurrentBranches
import PaperFormalization.Manuscript.SourceBranchGluing

/-! # One finite history gives one actual pair of horizon paths
M13r verified unit (see CODEX_HANDOFF_M13R.md). All branch prefixes come from a SINGLE finite innovation array.
Values beyond the finite schedule are harmless totalizations, never ODE claims.
The global right path, its true pretraces, and the recursive post-jump states
are identified without assuming cross-jump continuity or a nonempty final branch.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ProbabilityTheory
namespace PaperFormalization.Manuscript
variable {W : Type*} {N d : Nat}

def sourceFinitePrefix {A : Type*} {J : Nat} (h : Fin J -> A) (n : Nat) (hn : n ≤ J) : Fin n -> A :=
  fun i => h (Fin.castLE hn i)

@[simp] theorem sourceFinitePrefix_init {A : Type*} {J : Nat}
    (h : Fin J -> A) (n : Nat) (hn : n+1 ≤ J) :
    sourceHistoryInit (sourceFinitePrefix h (n+1) hn) =
      sourceFinitePrefix h n (Nat.le_trans (Nat.le_succ n) hn) := rfl

/-- The only branch selection data are the given finite history and initial cloud. -/
noncomputable def sourceFiniteHorizonBranch (post : SourcePostMap W N d)
    (flowX : Nat -> Real -> SourceFiniteConfiguration N d -> SourceFiniteConfiguration N d)
    (flowY : (n : Nat) -> (Fin n -> W) -> Real -> EuclideanSpace Real (Fin d) -> EuclideanSpace Real (Fin d))
    (J : Nat) (h : Fin J -> W × SourceStepNormal N d) (u : SourceFiniteConfiguration N d)
    (n : Nat) (t : Real) : SourceFiniteConfiguration N d × SourceFiniteConfiguration N d :=
  if hn : n ≤ J then sourceCoupledBranch post flowX flowY n (sourceFinitePrefix h n hn) u t else (u,u)

@[simp] theorem sourceFiniteHorizonBranch_eq (post : SourcePostMap W N d) (flowX flowY)
    (J : Nat) (h : Fin J -> W × SourceStepNormal N d) (u : SourceFiniteConfiguration N d)
    (n : Nat) (hn : n ≤ J) (t : Real) :
    sourceFiniteHorizonBranch post flowX flowY J h u n t =
      sourceCoupledBranch post flowX flowY n (sourceFinitePrefix h n hn) u t := by
  simp only [sourceFiniteHorizonBranch, dif_pos hn]

noncomputable def sourceFiniteHorizonPath (post : SourcePostMap W N d) (flowX flowY)
    (tau : Nat -> Real) (J : Nat) (h : Fin J -> W × SourceStepNormal N d)
    (u : SourceFiniteConfiguration N d) (t : Real) :=
  (sourceGlue tau J (fun n s => (sourceFiniteHorizonBranch post flowX flowY J h u n s).1) t,
   sourceGlue tau J (fun n s => (sourceFiniteHorizonBranch post flowX flowY J h u n s).2) t)

/-- Both RIGHT values at every scheduled boundary are the constructed post states. -/
theorem sourceFiniteHorizonPath_at_jump (post : SourcePostMap W N d) (flowX flowY)
    (tau : Nat -> Real) (J : Nat) (htime : forall n, n < J -> tau n < tau (n+1))
    (hX : forall n x, flowX n (tau n) x = x)
    (hY : forall n past x, flowY n past (tau n) x = x)
    (h : Fin J -> W × SourceStepNormal N d) (u : SourceFiniteConfiguration N d)
    (n : Nat) (hn : n ≤ J) :
    sourceFiniteHorizonPath post flowX flowY tau J h u (tau n) =
      post n (sourceFinitePrefix h n hn) u := by
  unfold sourceFiniteHorizonPath
  rw [sourceGlue_at_jump tau J _ htime n hn, sourceGlue_at_jump tau J _ htime n hn,
    sourceFiniteHorizonBranch_eq post flowX flowY J h u n hn,
    sourceCoupledBranch_start post flowX flowY tau hX hY]

/-- Both LEFT traces are the old closed branch endpoints, not the right values. -/
theorem sourceFiniteHorizonPath_pretraces (post : SourcePostMap W N d) (flowX flowY)
    (tau : Nat -> Real) (J : Nat) (htime : forall n, n < J -> tau n < tau (n+1))
    (h : Fin J -> W × SourceStepNormal N d) (u : SourceFiniteConfiguration N d)
    (n : Nat) (hn : n < J)
    (hcont : ContinuousOn (sourceCoupledBranch post flowX flowY n (sourceFinitePrefix h n hn.le) u)
      (Icc (tau n) (tau (n+1)))) :
    Tendsto (sourceFiniteHorizonPath post flowX flowY tau J h u)
      (nhdsWithin (tau (n+1)) (Iio (tau (n+1))))
      (nhds (sourceCoupledBranch post flowX flowY n (sourceFinitePrefix h n hn.le) u (tau (n+1)))) := by
  have hc1 : ContinuousOn (fun t => (sourceFiniteHorizonBranch post flowX flowY J h u n t).1)
      (Icc (tau n) (tau (n+1))) := by
    simpa only [sourceFiniteHorizonBranch_eq post flowX flowY J h u n hn.le] using hcont.fst
  have hc2 : ContinuousOn (fun t => (sourceFiniteHorizonBranch post flowX flowY J h u n t).2)
      (Icc (tau n) (tau (n+1))) := by
    simpa only [sourceFiniteHorizonBranch_eq post flowX flowY J h u n hn.le] using hcont.snd
  have h1 := (sourceGlue_traces tau J
    (fun k t => (sourceFiniteHorizonBranch post flowX flowY J h u k t).1) htime n hn hc1).2
  have h2 := (sourceGlue_traces tau J
    (fun k t => (sourceFiniteHorizonBranch post flowX flowY J h u k t).2) htime n hn hc2).2
  unfold sourceFiniteHorizonPath
  simpa only [sourceFiniteHorizonBranch_eq post flowX flowY J h u n hn.le, Prod.mk.eta] using h1.prodMk_nhds h2

/-- Coordinate-preserving tower projections give the SAME finite history prefix.
This identifies the histories of constructed views with the above horizon paths. -/
theorem sourceTowerPacked_eq_finitePrefix
    {O : Type*} (initial : O -> SourceFiniteConfiguration N d) (innovation : Nat -> O -> W)
    (J n : Nat) (hn : n ≤ J)
    (project : SourceAuxiliarySpace O (SourceStepNormal N d) J -> SourceAuxiliarySpace O (SourceStepNormal N d) n)
    (horiginal : forall z, sourceAuxiliaryOriginal J z = sourceAuxiliaryOriginal n (project z))
    (harray : forall z (i : Fin n), sourceAuxiliaryArray n (project z) i =
      sourceAuxiliaryArray J z (Fin.castLE hn i))
    (z : SourceAuxiliarySpace O (SourceStepNormal N d) J) :
    sourceTowerPacked innovation n (project z) = sourceFinitePrefix (sourceTowerPacked innovation J z) n hn := by
  funext i
  apply Prod.ext
  · change innovation i (sourceAuxiliaryOriginal n (project z)) = innovation i (sourceAuxiliaryOriginal J z)
    rw [horiginal z]
  · exact harray z i
end PaperFormalization.Manuscript
