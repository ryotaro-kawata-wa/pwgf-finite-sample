import PaperFormalization.Manuscript.FiniteTimeGrid

/-! # Finite labelled-branch concentration from actual grids

The label j distinguishes pre-jump and post-jump traces. Neither their values
nor their laws are equated. Failure events can be intersected with path and
sample eligibility without altering any node law used for concentration.
-/
open MeasureTheory Set
open scoped BigOperators NNReal
namespace PaperFormalization.Manuscript

/-- Actual branchwise interpolation reduces the continuum event to at most
(L+1)(N+1) labelled node failures under one unchanged finite measure. -/
theorem measureReal_finite_branch_failure_le {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] (Good : Set Ω) (L N : ℕ) (hN : 0 < N)
    (a b : Fin (L+1) → ℝ) (hab : ∀ j, a j ≤ b j)
    (T : ℝ) (hlen : ∀ j, b j-a j ≤ T) (K : ℝ≥0)
    (F : Fin (L+1) → Ω → ℝ → ℝ)
    (hF : ∀ j ω, ω ∈ Good → LipschitzOnWith K (F j ω) (Icc (a j) (b j)))
    (r p : ℝ)
    (hnode : ∀ j i, ν.real {ω | r < F j ω (closedBranchGrid (a j) (b j) N i)} ≤
      p / (((L+1 : ℕ) : ℝ) * ((N+1 : ℕ) : ℝ))) :
    ν.real {ω | ω ∈ Good ∧ ∃ j, ∃ t ∈ Icc (a j) (b j),
      r + (K : ℝ) * (T/N) < F j ω t} ≤ p := by
  let Bad : (Fin (L+1) × Fin (N+1)) → Set Ω :=
    fun ji => {ω | r < F ji.1 ω (closedBranchGrid (a ji.1) (b ji.1) N ji.2)}
  have hs : {ω | ω ∈ Good ∧ ∃ j, ∃ t ∈ Icc (a j) (b j),
      r + (K : ℝ) * (T/N) < F j ω t} ⊆ ⋃ ji, Bad ji := by
    intro ω hω
    by_contra hn
    obtain ⟨j,t,ht,hbad⟩ := hω.2
    have hgrid : ∀ i, F j ω (closedBranchGrid (a j) (b j) N i) ≤ r := by
      intro i
      exact le_of_not_gt (fun hi => hn (mem_iUnion.mpr ⟨(j,i),hi⟩))
    have hb := closedBranchGrid_lipschitz_bound (a j) (b j) (hab j) hN
      (F j ω) K (hF j ω hω.1) r hgrid t ht
    have herr : (K : ℝ) * ((b j-a j)/N) ≤ (K : ℝ) * (T/N) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (hlen j) (Nat.cast_nonneg N)) K.coe_nonneg
    linarith
  calc
    _ ≤ ν.real (⋃ ji, Bad ji) := measureReal_mono hs
    _ ≤ ∑ ji, ν.real (Bad ji) := measureReal_iUnion_fintype_le Bad
    _ ≤ ∑ _ji : Fin (L+1) × Fin (N+1),
        p / (((L+1 : ℕ) : ℝ) * ((N+1 : ℕ) : ℝ)) :=
      Finset.sum_le_sum (fun ji _ => hnode ji.1 ji.2)
    _ = p := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul]
      field_simp

/-- An actual pointwise unclipping inequality carries the same finite-grid
budget to the localized original residual, with its literal additive bias. -/
theorem measureReal_localized_raw_branch_failure_le {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] (Good Local : Set Ω) (L N : ℕ) (hN : 0 < N)
    (a b : Fin (L+1) → ℝ) (hab : ∀ j, a j ≤ b j)
    (T : ℝ) (hlen : ∀ j, b j-a j ≤ T) (K : ℝ≥0)
    (F R : Fin (L+1) → Ω → ℝ → ℝ)
    (hF : ∀ j ω, ω ∈ Good → LipschitzOnWith K (F j ω) (Icc (a j) (b j)))
    (beta r p : ℝ)
    (hraw : ∀ j ω, ω ∈ Good → ω ∈ Local → ∀ t ∈ Icc (a j) (b j),
      R j ω t ≤ F j ω t + beta)
    (hnode : ∀ j i, ν.real {ω | r < F j ω (closedBranchGrid (a j) (b j) N i)} ≤
      p / (((L+1 : ℕ) : ℝ) * ((N+1 : ℕ) : ℝ))) :
    ν.real {ω | ω ∈ Good ∧ ω ∈ Local ∧ ∃ j, ∃ t ∈ Icc (a j) (b j),
      beta + r + (K : ℝ) * (T/N) < R j ω t} ≤ p := by
  apply (measureReal_mono (μ := ν) (show
    {ω | ω ∈ Good ∧ ω ∈ Local ∧ ∃ j, ∃ t ∈ Icc (a j) (b j),
      beta + r + (K : ℝ) * (T/N) < R j ω t} ⊆
    {ω | ω ∈ Good ∧ ∃ j, ∃ t ∈ Icc (a j) (b j),
      r + (K : ℝ) * (T/N) < F j ω t} from ?_)).trans
    (measureReal_finite_branch_failure_le ν Good L N hN a b hab T hlen K F hF r p hnode)
  intro ω hω
  obtain ⟨j,t,ht,hbad⟩ := hω.2.2
  refine ⟨hω.1,j,t,ht,?_⟩
  have hb := hraw j ω hω.1 hω.2.1 t ht
  linarith
end PaperFormalization.Manuscript
