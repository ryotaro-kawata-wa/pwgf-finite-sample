import PaperFormalization.Manuscript.SourceFreshAuxiliaryHistories
import Mathlib.Data.Fin.Tuple.Basic

/-! # Read the precise finite auxiliary coordinates
M13r verified unit (see CODEX_HANDOFF_M13R.md). These maps preserve the original outcome and never inspect a
future auxiliary. No probability law is assumed for a reconstructed history.
-/
open MeasureTheory ProbabilityTheory Set
namespace PaperFormalization.Manuscript
variable {O S A : Type*}

/-- Coordinates in chronological order; the original space may have any universe. -/
def sourceAuxiliaryArray : (n : Nat) -> SourceAuxiliarySpace O A n -> Fin n -> A
  | 0, _ => Fin.elim0
  | n+1, z => Fin.snoc (sourceAuxiliaryArray n z.1) z.2

@[simp] theorem sourceAuxiliaryArray_castSucc (n : Nat)
    (z : SourceAuxiliarySpace O A (n+1)) (i : Fin n) :
    sourceAuxiliaryArray (n+1) z i.castSucc = sourceAuxiliaryArray n z.1 i := by
  simp [sourceAuxiliaryArray]

@[simp] theorem sourceAuxiliaryArray_last (n : Nat)
    (z : SourceAuxiliarySpace O A (n+1)) :
    sourceAuxiliaryArray (n+1) z (Fin.last n) = z.2 := by
  simp [sourceAuxiliaryArray]

@[simp] theorem sourceAuxiliaryArray_history (history : O -> S) (n : Nat)
    (z : SourceAuxiliarySpace O A n) :
    sourceAuxiliaryArray n (sourceAuxiliaryHistory history n z) =
      sourceAuxiliaryArray n z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact congrArg (fun f : Fin n -> A => Fin.snoc (α := fun _ => A) f z.2) (ih z.1)

/-- Restriction discards only the last m coordinates. -/
theorem sourceAuxiliaryArray_projection (n m : Nat)
    (z : SourceAuxiliarySpace O A (n+m)) (i : Fin n) :
    sourceAuxiliaryArray n (sourceAuxiliaryProjection n m z) i =
      sourceAuxiliaryArray (n+m) z (Fin.castLE (Nat.le_add_right n m) i) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change sourceAuxiliaryArray n (sourceAuxiliaryProjection n m z.1) i = _
    rw [ih]
    exact (sourceAuxiliaryArray_castSucc (n+m) z
      (Fin.castLE (Nat.le_add_right n m) i)).symm

section Measurable
variable [MeasurableSpace O] [MeasurableSpace S] [MeasurableSpace A]

set_option backward.isDefEq.respectTransparency false in
theorem sourceAuxiliaryArray_measurable (n : Nat) :
    Measurable (sourceAuxiliaryArray (O := O) (A := A) n) := by
  induction n with
  | zero => exact measurable_pi_lambda _ (fun i => Fin.elim0 i)
  | succ n ih =>
    change Measurable (fun z : SourceAuxiliarySpace O A n × A =>
      Fin.snoc (α := fun _ => A) (sourceAuxiliaryArray n z.1) z.2)
    apply measurable_pi_lambda
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using
        (measurable_snd : Measurable (fun z : SourceAuxiliarySpace O A n × A => z.2))
    · simpa only [Fin.snoc_castSucc, Function.comp_def] using
        ((measurable_pi_apply j).comp ih).comp measurable_fst

/-- A universe-correct coordinate map, sufficient for all subsequent recurrences. -/
def sourceAuxiliaryCoordinates (n : Nat) (z : SourceAuxiliarySpace O A n) : O × (Fin n -> A) :=
  (sourceAuxiliaryOriginal n z, sourceAuxiliaryArray n z)

theorem sourceAuxiliaryCoordinates_measurable
    (nu : Measure O) [IsProbabilityMeasure nu]
    (lambda : Measure A) [IsProbabilityMeasure lambda] (n : Nat) :
    Measurable (sourceAuxiliaryCoordinates (O := O) (A := A) n) :=
  (sourceAuxiliaryOriginal_preserving nu lambda n).measurable.prodMk
    (sourceAuxiliaryArray_measurable n)

/-- History reconstruction preserves all original-history and auxiliary data
pointwise, before any AE or conditional-law reasoning. -/
theorem sourceAuxiliaryCoordinates_history (history : O -> S) (n : Nat)
    (z : SourceAuxiliarySpace O A n) :
    sourceAuxiliaryCoordinates n (sourceAuxiliaryHistory history n z) =
      (history (sourceAuxiliaryOriginal n z), sourceAuxiliaryArray n z) := by
  simp only [sourceAuxiliaryCoordinates, sourceAuxiliaryHistory_original,
    sourceAuxiliaryArray_history]

/-- Prefix projection retains both the original point and the chronological
auxiliary array. Thus later view pullbacks cannot choose an unrelated coupling. -/
theorem exists_source_auxiliary_coordinate_prefix
    (nu : Measure O) [IsProbabilityMeasure nu]
    (lambda : Measure A) [IsProbabilityMeasure lambda] (n J : Nat) (hn : n ≤ J) :
    ∃ project : SourceAuxiliarySpace O A J -> SourceAuxiliarySpace O A n,
      MeasurePreserving project (sourceAuxiliaryMeasure nu lambda J) (sourceAuxiliaryMeasure nu lambda n) ∧
      (forall z, sourceAuxiliaryOriginal J z = sourceAuxiliaryOriginal n (project z)) ∧
      (forall z (i : Fin n), sourceAuxiliaryArray n (project z) i =
        sourceAuxiliaryArray J z (Fin.castLE hn i)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact ⟨sourceAuxiliaryProjection n m, sourceAuxiliaryProjection_preserving nu lambda n m,
    sourceAuxiliaryProjection_original n m, sourceAuxiliaryArray_projection n m⟩
end Measurable
end PaperFormalization.Manuscript
