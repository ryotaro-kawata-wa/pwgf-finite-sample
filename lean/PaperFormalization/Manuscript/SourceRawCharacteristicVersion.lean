import PaperFormalization.Manuscript.SourceRawScheduledTracking

/-! # Source-facing characteristic-version and failure-event adapters
M13s verified unit; see CODEX_HANDOFF_M13S.md. Raw characteristic paths can use the existing simultaneous
measurable-version construction. The final failure bound is unconditional and
restricted, never a conditional probability given anti-spikiness/smallness.
-/
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ProbabilityTheory
namespace PaperFormalization.Manuscript

/-- Supply the path-valued realization used by the final theorem from the raw
source characteristic maps on the ORIGINAL population/one-seed product law.
No all-history or all-initial-state continuity premise is added. -/
theorem exists_source_final_characteristic_version
    {O W : Type*} [MeasurableSpace O] [MeasurableSpace W] {J d : Nat}
    (nu : Measure O) (mu0 : Measure (EuclideanSpace Real (Fin d)))
    (innovation : Nat -> O -> W)
    (tau eta : Nat -> Real) (T : Real) (B : NNReal)
    (htime : ∀ k, k < J -> tau k < tau (k+1)) (hT : tau J ≤ T)
    (flowY : (n : Nat) -> (Fin n -> W) -> Real -> EuclideanSpace Real (Fin d) -> EuclideanSpace Real (Fin d))
    (field : (n : Nat) -> (Fin n -> W) -> W -> EuclideanSpace Real (Fin d) -> EuclideanSpace Real (Fin d))
    (hFY : ∀ n t, Measurable (fun z : (Fin n -> W) × EuclideanSpace Real (Fin d) => flowY n z.1 t z.2))
    (hfield : ∀ n, Measurable (fun z : ((Fin n -> W) × W) × EuclideanSpace Real (Fin d) => field n z.1.1 z.1.2 z.2))
    (hRawLip : ∀ᵐ z ∂ (nu.map (fun o n => innovation n o)).prod mu0, ∀ j : Fin (J+1),
      LipschitzOnWith B (sourceOriginalCharacteristic tau eta flowY field j.val z.1 z.2)
        (Icc (sourceScheduleLeft tau J j) (sourceScheduleRight tau J T j))) :
    ∃ Phi : (Nat -> W) -> EuclideanSpace Real (Fin d) ->
        SourceReferencePathSpace J d (sourceScheduleLeft tau J) (sourceScheduleRight tau J T),
      Measurable (fun z : (Nat -> W) × EuclideanSpace Real (Fin d) => Phi z.1 z.2) ∧
      ∀ᵐ z ∂ (nu.map (fun o n => innovation n o)).prod mu0, ∀ j t,
        t ∈ Icc (sourceScheduleLeft tau J j) (sourceScheduleRight tau J T j) ->
          sourceReferencePathEval (Phi z.1 z.2) j t = sourceOriginalCharacteristic tau eta flowY field j.val z.1 z.2 t := by
  have hjump : ∀ n, Measurable (fun z : ((Fin n -> W) × W) × EuclideanSpace Real (Fin d) =>
      sourcePopulationFieldJump eta field n z.1.1 z.1.2 z.2) :=
    fun n => measurable_snd.add ((hfield n).const_smul (eta n))
  exact exists_source_causal_reference_path_version (nu.map (fun o n => innovation n o)) mu0
    (sourceScheduleLeft tau J) (sourceScheduleRight tau J T) (sourceSchedule_ordered tau J T htime hT)
    B tau flowY (sourcePopulationFieldJump eta field) hFY hjump
    (fun (j : Fin (J+1)) e (i : Fin j.val) => e i.val)
    (fun _ => measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)) hRawLip

/-- The final measurable event implies the desired restricted OUTER-probability
bound even before measurability of the two path restrictions is separately used. -/
theorem source_final_restricted_tracking_failure
    {S : Type*} [MeasurableSpace S] (rho : Measure S) [IsProbabilityMeasure rho]
    (p : Real) (hp : 0 < p) (Good : Set S)
    (Restriction Conclusion : S -> Prop)
    (hBudget : rho.real Good.compl ≤ 17*p/32)
    (hResult : ∀ s, s ∈ Good -> Restriction s -> Conclusion s) :
    rho.real {s | Restriction s ∧ ¬ Conclusion s} ≤ 17*p/32 ∧
      rho.real {s | Restriction s ∧ ¬ Conclusion s} < p := by
  have hb := source_restricted_failure_probability rho Good Restriction Conclusion _ hBudget hResult
  exact ⟨hb,hb.trans_lt (by linarith)⟩
end PaperFormalization.Manuscript
