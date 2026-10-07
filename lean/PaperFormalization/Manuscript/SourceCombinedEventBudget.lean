import PaperFormalization.Manuscript.SourcePopulationGammaRadius
import PaperFormalization.Manuscript.SourceRadiusChoice
import PaperFormalization.Manuscript.OriginalPopulationEvent

/-! # Exact final allocation arithmetic without conditioning on path restrictions
M13r verified unit (see CODEX_HANDOFF_M13R.md). This is a reusable final assembly lemma, NOT a claim that the
remaining empirical exchangeability/ODE instantiation has been completed.
It accepts the outputs of the two separately derived event constructors, applies
the actual radius choice, and retains model restrictions as implications rather
than assigning them an unproved high-probability bound.
-/
open MeasureTheory Set
open scoped NNReal
namespace PaperFormalization.Manuscript

/-- The literal radius loss in M13q is paid for with p/8, not an arbitrary p/3. -/
theorem sourceOriginalRadiusLoss_eighth_budget
    (J N : Nat) (T alpha K0 D p : Real) (B : NNReal)
    (hN : 0 < N) (hT : 0 ≤ T) (halpha : 0 < alpha) (hK0 : 0 < K0)
    (hp : 0 < p) (hp1 : p < 1)
    (hchoice : 2 * Real.exp 1 * K0 *
      (1 + Real.log (2 * N * (2*((J : Real)+1) + (B : Real)*T/(Real.exp 1*K0))/(p/8)))^(1/alpha) ≤ D) :
    2 * Real.exp 1 * K0 ≤ D ∧ sourceOriginalRadiusLoss J N T alpha K0 D B ≤ p/8 := by
  exact source_uniform_radius_bound_le_budget J N alpha K0 D T B (p/8)
    hN halpha hK0 hT B.coe_nonneg (by positivity) (by linarith) hchoice

/-- The source allocations actually leave slack. No event independence is used. -/
theorem sourceCombinedLoss_eighth_bound (J : Nat) (p radiusLoss : Real)
    (hp : 0 < p) (hRadius : radiusLoss ≤ p/8) :
    p/8 + p/8 + radiusLoss + ((J : Real)/((J : Real)+1))*(5*p/32) ≤ 17*p/32 ∧
      17*p/32 < p := by
  have hratio : (J : Real)/((J : Real)+1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith)
  have hmult := mul_le_mul_of_nonneg_right hratio (by positivity : 0 ≤ 5*p/32)
  constructor <;> nlinarith

/-- Intersect the population/Gamma/radius and recurrent covariance/jump events
on their SAME measure, remove only a genuine AE defect, and retain exact losses.
No probability is claimed for anti-spikiness, curvature or nonlinear smallness. -/
theorem exists_source_combined_model_event
    {O : Type*} [MeasurableSpace O] (nu : Measure O) [IsProbabilityMeasure nu]
    (J : Nat) (pPop pGamma radiusLoss pTotal : Real)
    (PopulationGammaRadius Observations : Set O)
    (hP : MeasurableSet PopulationGammaRadius) (hO : MeasurableSet Observations)
    (hPB : nu.real PopulationGammaRadiusᶜ ≤ pPop+pGamma+radiusLoss)
    (hOB : nu.real Observationsᶜ ≤ ((J : Real)/((J : Real)+1))*(5*pTotal/32))
    (Model : O -> Prop) (hModel : ∀ᵐ o ∂ nu, Model o) :
    ∃ Good : Set O, MeasurableSet Good ∧
      nu.real Goodᶜ ≤ pPop+pGamma+radiusLoss+((J : Real)/((J : Real)+1))*(5*pTotal/32) ∧
      forall o, o ∈ Good -> Model o ∧ o ∈ PopulationGammaRadius ∧ o ∈ Observations := by
  have hbudget : nu.real (PopulationGammaRadius ∩ Observations)ᶜ ≤
      pPop+pGamma+radiusLoss+((J : Real)/((J : Real)+1))*(5*pTotal/32) := by
    rw [compl_inter]
    exact (measureReal_union_le _ _).trans (add_le_add hPB hOB)
  obtain ⟨Good,hGood,hGB,hvalid⟩ := exists_original_population_event nu nu id measurable_id
    (by simp) (PopulationGammaRadius ∩ Observations) (hP.inter hO) _ hbudget Model hModel
  exact ⟨Good,hGood,hGB,fun o ho => ⟨(hvalid o ho).1,(hvalid o ho).2.1,(hvalid o ho).2.2⟩⟩

/-- A deterministic restricted conclusion fails only outside the constructed
Good set. This is an unconditional bound on failures WITH the restriction,
not a conditional probability bound given a possibly rare restriction. -/
theorem source_restricted_failure_subset
    {O : Type*} (Good : Set O) (Restriction Conclusion : O -> Prop)
    (h : forall o, o ∈ Good -> Restriction o -> Conclusion o) :
    {o | Restriction o ∧ ¬ Conclusion o} ⊆ Goodᶜ := by
  intro o ho hGood
  exact ho.2 (h o hGood ho.1)
/-- Monotonicity yields an unconditional failure OUTER-measure bound even when
measurability of the path restriction has not yet been supplied. -/
theorem source_restricted_failure_probability
    {O : Type*} [MeasurableSpace O] (nu : Measure O) [IsProbabilityMeasure nu]
    (Good : Set O) (Restriction Conclusion : O -> Prop) (budget : Real)
    (hbudget : nu.real Goodᶜ ≤ budget)
    (hvalid : forall o, o ∈ Good -> Restriction o -> Conclusion o) :
    nu.real {o | Restriction o ∧ ¬ Conclusion o} ≤ budget :=
  (measureReal_mono (source_restricted_failure_subset Good Restriction Conclusion hvalid)).trans hbudget
end PaperFormalization.Manuscript
