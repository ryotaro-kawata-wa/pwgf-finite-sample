import PaperFormalization.Manuscript.SourceAuxiliaryCoordinates
import PaperFormalization.Manuscript.SourceActualFiniteConstruction

/-! # Actual prehistories and recursive coordinates on the common tower
M13r verified unit (see CODEX_HANDOFF_M13R.md). An original prehistory consists of the original initial array
and the strict population-innovation prefix. The existing auxiliary history
adds exactly the past auxiliaries. Neither current input is revealed early.
-/
open MeasureTheory ProbabilityTheory Set
namespace PaperFormalization.Manuscript
variable {O W : Type*} {N d : Nat}
abbrev SourceStepNormal (N d : Nat) := EuclideanSpace Real (Fin N × Fin d)
abbrev SourceRecurrentHistory (W : Type*) (N d n : Nat) :=
  SourceAuxiliarySpace ((Fin n -> W) × SourceFiniteConfiguration N d) (SourceStepNormal N d) n

/-- Original data only: no auxiliary is present here. -/
def sourceOriginalPrehistory (initial : O -> SourceFiniteConfiguration N d)
    (innovation : Nat -> O -> W) (n : Nat) (o : O) :=
  ((fun i : Fin n => innovation i o), initial o)

def sourceHistoryPopulation (n : Nat) (h : SourceRecurrentHistory W N d n) : Fin n -> W :=
  (sourceAuxiliaryOriginal n h).1

def sourceHistoryInitial (n : Nat) (h : SourceRecurrentHistory W N d n) : SourceFiniteConfiguration N d :=
  (sourceAuxiliaryOriginal n h).2

def sourceHistoryPacked (n : Nat) (h : SourceRecurrentHistory W N d n) : Fin n -> W × SourceStepNormal N d :=
  fun i => (sourceHistoryPopulation n h i, sourceAuxiliaryArray n h i)

def sourceTowerPacked (innovation : Nat -> O -> W) (n : Nat)
    (z : SourceAuxiliarySpace O (SourceStepNormal N d) n) : Fin n -> W × SourceStepNormal N d :=
  fun i => (innovation i (sourceAuxiliaryOriginal n z), sourceAuxiliaryArray n z i)

@[simp] theorem sourceHistoryPacked_population (n : Nat) (h : SourceRecurrentHistory W N d n) :
    sourcePopulationPrefix (sourceHistoryPacked n h) = sourceHistoryPopulation n h := rfl

@[simp] theorem sourceHistoryPacked_observation
    (initial : O -> SourceFiniteConfiguration N d) (innovation : Nat -> O -> W)
    (n : Nat) (z : SourceAuxiliarySpace O (SourceStepNormal N d) n) :
    sourceHistoryPacked n (sourceAuxiliaryHistory (sourceOriginalPrehistory initial innovation n) n z) =
      sourceTowerPacked innovation n z := by
  letI : MeasurableSpace O := ⊤
  letI : MeasurableSpace W := ⊤
  funext i
  simp only [sourceHistoryPacked, sourceHistoryPopulation, sourceTowerPacked,
    sourceAuxiliaryHistory_original, sourceOriginalPrehistory, sourceAuxiliaryArray_history]

@[simp] theorem sourceHistoryInitial_observation
    (initial : O -> SourceFiniteConfiguration N d) (innovation : Nat -> O -> W)
    (n : Nat) (z : SourceAuxiliarySpace O (SourceStepNormal N d) n) :
    sourceHistoryInitial n (sourceAuxiliaryHistory (sourceOriginalPrehistory initial innovation n) n z) =
      initial (sourceAuxiliaryOriginal n z) := by
  letI : MeasurableSpace O := ⊤
  letI : MeasurableSpace W := ⊤
  simp only [sourceHistoryInitial, sourceAuxiliaryHistory_original, sourceOriginalPrehistory]

@[simp] theorem sourceHistoryPopulation_observation
    (initial : O -> SourceFiniteConfiguration N d) (innovation : Nat -> O -> W)
    (n : Nat) (z : SourceAuxiliarySpace O (SourceStepNormal N d) n) :
    sourceHistoryPopulation n (sourceAuxiliaryHistory (sourceOriginalPrehistory initial innovation n) n z) =
      (fun i : Fin n => innovation i (sourceAuxiliaryOriginal n z)) := by
  letI : MeasurableSpace O := ⊤
  letI : MeasurableSpace W := ⊤
  simp only [sourceHistoryPopulation, sourceAuxiliaryHistory_original, sourceOriginalPrehistory]

@[simp] theorem sourceTowerPacked_init (innovation : Nat -> O -> W)
    (n : Nat) (z : SourceAuxiliarySpace O (SourceStepNormal N d) (n+1)) :
    sourceHistoryInit (sourceTowerPacked innovation (n+1) z) = sourceTowerPacked innovation n z.1 := by
  funext i
  simp only [sourceHistoryInit, sourceTowerPacked, sourceAuxiliaryOriginal,
    sourceAuxiliaryArray_castSucc, Fin.val_castSucc]

@[simp] theorem sourceTowerPacked_last (innovation : Nat -> O -> W)
    (n : Nat) (z : SourceAuxiliarySpace O (SourceStepNormal N d) (n+1)) :
    sourceTowerPacked innovation (n+1) z (Fin.last n) =
      (innovation n (sourceAuxiliaryOriginal n z.1), z.2) := by
  simp only [sourceTowerPacked, sourceAuxiliaryOriginal, sourceAuxiliaryArray_last, Fin.val_last]

section Measurable
variable [MeasurableSpace O] [MeasurableSpace W]

theorem sourceOriginalPrehistory_measurable
    (initial : O -> SourceFiniteConfiguration N d) (innovation : Nat -> O -> W)
    (hinit : Measurable initial) (hW : forall n, Measurable (innovation n)) (n : Nat) :
    Measurable (sourceOriginalPrehistory initial innovation n) :=
  (measurable_pi_lambda _ (fun i : Fin n => hW i)).prodMk hinit

/-- The original projection is measurable independently of any chosen measure. -/
theorem sourceAuxiliaryOriginal_measurable (n : Nat) :
    Measurable (sourceAuxiliaryOriginal (O := O) (A := SourceStepNormal N d) n) := by
  induction n with
  | zero => exact measurable_down
  | succ n ih => exact ih.comp measurable_fst

theorem sourceHistoryPopulation_measurable (n : Nat) :
    Measurable (sourceHistoryPopulation (W := W) (N := N) (d := d) n) :=
  measurable_fst.comp (sourceAuxiliaryOriginal_measurable n)

theorem sourceHistoryInitial_measurable (n : Nat) :
    Measurable (sourceHistoryInitial (W := W) (N := N) (d := d) n) :=
  measurable_snd.comp (sourceAuxiliaryOriginal_measurable n)

theorem sourceHistoryPacked_measurable (n : Nat) :
    Measurable (sourceHistoryPacked (W := W) (N := N) (d := d) n) :=
  measurable_pi_lambda _ (fun i =>
    ((measurable_pi_apply i).comp (sourceHistoryPopulation_measurable n)).prodMk
      ((measurable_pi_apply i).comp (sourceAuxiliaryArray_measurable n)))

theorem sourceTowerPacked_measurable (innovation : Nat -> O -> W)
    (hW : forall n, Measurable (innovation n)) (n : Nat) :
    Measurable (sourceTowerPacked (N := N) (d := d) innovation n) :=
  measurable_pi_lambda _ (fun i =>
    ((hW i).comp (sourceAuxiliaryOriginal_measurable n)).prodMk
      ((measurable_pi_apply i).comp (sourceAuxiliaryArray_measurable n)))
end Measurable
end PaperFormalization.Manuscript
