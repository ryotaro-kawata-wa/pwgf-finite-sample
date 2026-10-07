import PaperFormalization.Manuscript.FiniteTimeGrid
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-! # A measurable common event from eligible labelled-grid failures

Only finitely many actual node failures need to be measurable. The pathwise
model predicate is retained using a measurable null cover; no measurability
of a continuum supremum or of the sample localization event is required.
All probabilities are under the same original finite measure.
-/
open MeasureTheory Set
open scoped BigOperators NNReal
namespace PaperFormalization.Manuscript

/-- Eligible node budgets give a measurable event of loss at most p. On that
event the AE model predicate holds, and localization plus actual branch
Lipschitz and raw/clipped comparison estimates imply every-time bounds.
Branches retain their separate endpoints, including zero-length branches. -/
theorem exists_eligible_finite_branch_event {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν]
    (Eligible Local : Set Ω) (hEligible : MeasurableSet Eligible)
    (Model : Ω → Prop) (hModel : ∀ᵐ ω ∂ν, Model ω)
    (L N : ℕ) (hN : 0 < N) (a b : Fin (L+1) → ℝ) (hab : ∀ j, a j ≤ b j)
    (T : ℝ) (hlen : ∀ j, b j-a j ≤ T) (K : ℝ≥0)
    (F R : Fin (L+1) → Ω → ℝ → ℝ)
    (hF : ∀ j ω, Model ω → ω ∈ Eligible → ω ∈ Local →
      LipschitzOnWith K (F j ω) (Icc (a j) (b j)))
    (beta r p : ℝ)
    (hraw : ∀ j ω, Model ω → ω ∈ Eligible → ω ∈ Local →
      ∀ t ∈ Icc (a j) (b j), R j ω t ≤ F j ω t + beta)
    (hmeas : ∀ j i, Measurable (fun ω => F j ω (closedBranchGrid (a j) (b j) N i)))
    (hnode : ∀ j i, ν.real {ω | ω ∈ Eligible ∧
        r < F j ω (closedBranchGrid (a j) (b j) N i)} ≤
      p / (((L+1 : ℕ) : ℝ) * ((N+1 : ℕ) : ℝ))) :
    ∃ Good : Set Ω, MeasurableSet Good ∧ ν.real Goodᶜ ≤ p ∧
      ∀ ω ∈ Good, Model ω ∧ (ω ∈ Eligible → ω ∈ Local →
        ∀ j t, t ∈ Icc (a j) (b j) →
          R j ω t ≤ beta + r + (K : ℝ) * (T/N)) := by
  let Bad : (Fin (L+1) × Fin (N+1)) → Set Ω :=
    fun ji => {ω | ω ∈ Eligible ∧
      r < F ji.1 ω (closedBranchGrid (a ji.1) (b ji.1) N ji.2)}
  have hBad (ji) : MeasurableSet (Bad ji) :=
    hEligible.inter (measurableSet_lt measurable_const (hmeas ji.1 ji.2))
  let Fail : Set Ω := ⋃ ji, Bad ji
  have hFailMeas : MeasurableSet Fail := MeasurableSet.iUnion hBad
  have hFail : ν.real Fail ≤ p := by
    calc
      _ ≤ ∑ ji, ν.real (Bad ji) := measureReal_iUnion_fintype_le Bad
      _ ≤ ∑ _ji : Fin (L+1) × Fin (N+1),
          p / (((L+1 : ℕ) : ℝ) * ((N+1 : ℕ) : ℝ)) :=
        Finset.sum_le_sum (fun ji _ => hnode ji.1 ji.2)
      _ = p := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_mul]
        field_simp
  obtain ⟨Null, hNullSub, hNullMeas, hNullZero⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hModel)
  refine ⟨Nullᶜ ∩ Failᶜ, hNullMeas.compl.inter hFailMeas.compl, ?_, ?_⟩
  · rw [compl_inter, compl_compl, compl_compl]
    have hNullReal : ν.real Null = 0 := by simp only [measureReal_def, hNullZero, ENNReal.toReal_zero]
    exact (measureReal_union_le Null Fail).trans (by simpa only [hNullReal, zero_add] using hFail)
  · intro ω hω
    have hm : Model ω := by
      by_contra hn
      exact hω.1 (hNullSub hn)
    refine ⟨hm, ?_⟩
    intro he hl j t ht
    have hgrid : ∀ i, F j ω (closedBranchGrid (a j) (b j) N i) ≤ r := by
      intro i
      exact le_of_not_gt (fun hi => hω.2 (mem_iUnion.mpr ⟨(j,i), he, hi⟩))
    have hb := closedBranchGrid_lipschitz_bound (a j) (b j) (hab j) hN
      (F j ω) K (hF j ω hm he hl) r hgrid t ht
    have herr : (K : ℝ) * ((b j-a j)/N) ≤ (K : ℝ) * (T/N) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (hlen j) (Nat.cast_nonneg N)) K.coe_nonneg
    have hr := hraw j ω hm he hl t ht
    linarith
end PaperFormalization.Manuscript
