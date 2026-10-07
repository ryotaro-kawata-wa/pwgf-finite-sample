import PaperFormalization.Manuscript.SourceFiniteHorizonPaths
import PaperFormalization.Manuscript.SourceFinalRecurrentViews

/-! # Final-tower observations refer to one finite-history time path
M13r verified unit (see CODEX_HANDOFF_M13R.md). These identities use the original/auxiliary-coordinate
preservation proved by the all-stage constructor. They remove the remaining
choice of earlier projections from the path being tracked.
-/
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
namespace PaperFormalization.Manuscript
variable {O W : Type*} {N d : Nat}

/-- The observed pre-state is the endpoint of the unique old closed branch
selected from the final finite history. No post-jump value is substituted. -/
theorem source_projected_recurrent_pre
    (post : SourcePostMap W N d) (flowX flowY)
    (initial : O -> SourceFiniteConfiguration N d) (innovation : Nat -> O -> W)
    (J n : Nat) (hn : n+1 ≤ J)
    (project : SourceAuxiliarySpace O (SourceStepNormal N d) J -> SourceAuxiliarySpace O (SourceStepNormal N d) (n+1))
    (horiginal : forall z, sourceAuxiliaryOriginal J z = sourceAuxiliaryOriginal (n+1) (project z))
    (harray : forall z (i : Fin (n+1)), sourceAuxiliaryArray (n+1) (project z) i =
      sourceAuxiliaryArray J z (Fin.castLE hn i))
    (z : SourceAuxiliarySpace O (SourceStepNormal N d) J) (t : Real) :
    sourceTowerBranch post flowX flowY initial innovation n (project z).1 t =
      sourceFiniteHorizonBranch post flowX flowY J (sourceTowerPacked innovation J z)
        (initial (sourceAuxiliaryOriginal J z)) n t := by
  have hn0 : n ≤ J := Nat.le_trans (Nat.le_succ n) hn
  have hOriginal : forall z, sourceAuxiliaryOriginal J z = sourceAuxiliaryOriginal n (project z).1 := horiginal
  have hArray : forall z (i : Fin n), sourceAuxiliaryArray n (project z).1 i =
      sourceAuxiliaryArray J z (Fin.castLE hn0 i) := by
    intro z i
    have hi : Fin.castLE hn i.castSucc = Fin.castLE hn0 i := Fin.ext rfl
    simpa only [sourceAuxiliaryArray_castSucc, hi] using harray z i.castSucc
  have hp := sourceTowerPacked_eq_finitePrefix initial innovation J n hn0 (fun z => (project z).1)
    hOriginal hArray z
  rw [sourceFiniteHorizonBranch_eq post flowX flowY J _ _ n hn0]
  unfold sourceTowerBranch
  rw [hp, ← hOriginal z]

/-- Observed post-states are exactly the RIGHT values of the final glued path
when the raw branch maps have their prescribed start identities. -/
theorem source_projected_recurrent_post
    (post : SourcePostMap W N d) (flowX flowY)
    (initial : O -> SourceFiniteConfiguration N d) (innovation : Nat -> O -> W)
    (tau : Nat -> Real) (J n : Nat) (hn : n+1 ≤ J)
    (htime : forall k, k < J -> tau k < tau (k+1))
    (hXstart : forall k x, flowX k (tau k) x = x)
    (hYstart : forall k past x, flowY k past (tau k) x = x)
    (project : SourceAuxiliarySpace O (SourceStepNormal N d) J -> SourceAuxiliarySpace O (SourceStepNormal N d) (n+1))
    (horiginal : forall z, sourceAuxiliaryOriginal J z = sourceAuxiliaryOriginal (n+1) (project z))
    (harray : forall z (i : Fin (n+1)), sourceAuxiliaryArray (n+1) (project z) i =
      sourceAuxiliaryArray J z (Fin.castLE hn i))
    (z : SourceAuxiliarySpace O (SourceStepNormal N d) J) :
    post (n+1) (sourceTowerPacked innovation (n+1) (project z)) (initial (sourceAuxiliaryOriginal J z)) =
      sourceFiniteHorizonPath post flowX flowY tau J (sourceTowerPacked innovation J z)
        (initial (sourceAuxiliaryOriginal J z)) (tau (n+1)) := by
  rw [sourceFiniteHorizonPath_at_jump post flowX flowY tau J htime hXstart hYstart _ _ (n+1) hn]
  rw [sourceTowerPacked_eq_finitePrefix initial innovation J (n+1) hn project horiginal harray z]
end PaperFormalization.Manuscript
