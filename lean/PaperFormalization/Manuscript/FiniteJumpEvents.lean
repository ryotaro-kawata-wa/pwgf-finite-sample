import PaperFormalization.Manuscript.JointWhitenedSeed
import Mathlib.Data.ENNReal.BigOperators

/-! # Common events for a finite prescribed jump schedule

Each jump is observed from the same original probability space. Its supplied
observation-law identity identifies an actual history/sample view with its
Markov-kernel joint law. Conditional budgets are integrated and pulled back to
that one space before the finite union. An arbitrary AE model predicate is
retained with no additional loss using a measurable null-set cover.

The current manuscript uses p0=p/8 and per-jump budget p0/(L+1), not p/3.
This module does not construct repeated couplings or conditional distributions.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory ENNReal BigOperators

namespace PaperFormalization.Manuscript

/-- The prescribed-schedule budget is valid for every finite jump count,
including L=0, and the exact sum is strictly below the allocated p0. -/
theorem prescribed_jump_budget_bounds (L : ℕ) (p0 : ℝ) (hp0 : 0 < p0) (hp01 : p0 < 1) :
    0 < p0 / ((L : ℝ) + 1) ∧ p0 / ((L : ℝ) + 1) < 1 ∧
      (L : ℝ) * (p0 / ((L : ℝ) + 1)) < p0 := by
  have hL : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
  have hden : 0 < (L : ℝ) + 1 := by positivity
  refine ⟨div_pos hp0 hden, (div_lt_one hden).mpr (by linarith), ?_⟩
  apply (lt_of_mul_lt_mul_right (a := (L : ℝ) + 1) (by
    calc
      ((L : ℝ) * (p0 / ((L : ℝ) + 1))) * ((L : ℝ) + 1) = (L : ℝ) * p0 := by field_simp
      _ < p0 * ((L : ℝ) + 1) := by nlinarith))
  exact hden.le

/-- Conditional jump budgets produce one measurable event on the actual
original space, after the supplied observation laws identify each jump's
history/sample distribution. No independence between jumps is assumed. -/
theorem exists_finite_prescribed_jump_event
    {Ω H Z : Type*} [MeasurableSpace Ω] [MeasurableSpace H] [MeasurableSpace Z]
    (μ : Measure Ω) (L : ℕ)
    (ν : Fin L → Measure H) [∀ i, IsProbabilityMeasure (ν i)]
    (k : Fin L → Kernel H Z) [∀ i, IsMarkovKernel (k i)]
    (obs : Fin L → Ω → H × Z) (hobs : ∀ i, Measurable (obs i))
    (hview : ∀ i, μ.map (obs i) = ν i ⊗ₘ k i)
    (Bad : Fin L → Set (H × Z)) (hBad : ∀ i, MeasurableSet (Bad i))
    (budget : Fin L → ℝ≥0∞)
    (hbudget : ∀ i, ∀ᵐ h ∂ν i, k i h (Prod.mk h ⁻¹' Bad i) ≤ budget i)
    (Model : Ω → Prop) (hModel : ∀ᵐ ω ∂μ, Model ω) :
    ∃ Good : Set Ω, MeasurableSet Good ∧ μ Goodᶜ ≤ ∑ i, budget i ∧
      ∀ ω ∈ Good, Model ω ∧ ∀ i, obs i ω ∉ Bad i := by
  have hsingle (i : Fin L) : μ ((obs i) ⁻¹' Bad i) ≤ budget i := by
    rw [← Measure.map_apply (hobs i) (hBad i), hview i]
    have hb := joint_kernel_failure_budget (ν i) (k i) (Bad i) (hBad i)
      (fun _ => budget i) (hbudget i)
    simpa using hb
  obtain ⟨Null, hNullSub, hNullMeas, hNullZero⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hModel)
  let Fail := ⋃ i : Fin L, (obs i) ⁻¹' Bad i
  have hFail : MeasurableSet Fail := MeasurableSet.iUnion (fun i => (hBad i).preimage (hobs i))
  have hFailBound : μ Fail ≤ ∑ i, budget i :=
    (measure_iUnion_fintype_le μ (fun i => (obs i) ⁻¹' Bad i)).trans
      (Finset.sum_le_sum (fun i _ => hsingle i))
  refine ⟨Nullᶜ ∩ Failᶜ, hNullMeas.compl.inter hFail.compl, ?_, ?_⟩
  · rw [compl_inter, compl_compl, compl_compl]
    exact (measure_union_le Null Fail).trans (by simpa only [hNullZero, zero_add] using hFailBound)
  · intro ω hω
    refine ⟨?_, ?_⟩
    · by_contra hm
      exact hω.1 (hNullSub hm)
    · intro i hi
      exact hω.2 (mem_iUnion.mpr ⟨i, hi⟩)

/-- The literal current source allocation p0=p/8 gives a common finite-jump
comparison event with exact loss at most L/(L+1) times p/8, hence strictly
less than p/8. For L=0 the event loses zero probability. The model predicate
still costs no additional probability. -/
theorem exists_source_finite_jump_event
    {Ω H Z : Type*} [MeasurableSpace Ω] [MeasurableSpace H] [MeasurableSpace Z]
    (μ : Measure Ω) (L : ℕ)
    (ν : Fin L → Measure H) [∀ i, IsProbabilityMeasure (ν i)]
    (k : Fin L → Kernel H Z) [∀ i, IsMarkovKernel (k i)]
    (obs : Fin L → Ω → H × Z) (hobs : ∀ i, Measurable (obs i))
    (hview : ∀ i, μ.map (obs i) = ν i ⊗ₘ k i)
    (Bad : Fin L → Set (H × Z)) (hBad : ∀ i, MeasurableSet (Bad i))
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hbudget : ∀ i, ∀ᵐ h ∂ν i,
      k i h (Prod.mk h ⁻¹' Bad i) ≤ ENNReal.ofReal (p / (8 * ((L : ℝ) + 1))))
    (Model : Ω → Prop) (hModel : ∀ᵐ ω ∂μ, Model ω) :
    ∃ Good : Set Ω, MeasurableSet Good ∧
      μ Goodᶜ ≤ ENNReal.ofReal (((L : ℝ) / ((L : ℝ) + 1)) * (p / 8)) ∧
      μ Goodᶜ < ENNReal.ofReal (p / 8) ∧
      ∀ ω ∈ Good, Model ω ∧ ∀ i, obs i ω ∉ Bad i := by
  obtain ⟨Good, hGood, hb, hvalid⟩ := exists_finite_prescribed_jump_event μ L ν k obs hobs hview
    Bad hBad (fun _ => ENNReal.ofReal (p / (8 * ((L : ℝ) + 1)))) hbudget Model hModel
  have hsum : (∑ _i : Fin L, ENNReal.ofReal (p / (8 * ((L : ℝ) + 1)))) =
      ENNReal.ofReal (((L : ℝ) / ((L : ℝ) + 1)) * (p / 8)) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_nsmul]
    congr 1
    simp only [nsmul_eq_mul]
    field_simp
  rw [hsum] at hb
  have hstrict : ((L : ℝ) / ((L : ℝ) + 1)) * (p / 8) < p / 8 := by
    have hh := (prescribed_jump_budget_bounds L (p / 8) (by positivity) (by linarith)).2.2
    convert hh using 1
    ring
  refine ⟨Good, hGood, hb, hb.trans_lt ?_, hvalid⟩
  exact ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < p / 8) |>.mpr hstrict

end PaperFormalization.Manuscript
