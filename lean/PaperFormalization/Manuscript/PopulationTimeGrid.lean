import PaperFormalization.Manuscript.AdaptiveRadiusGrid

/-! # Actual labelled population grids at mesh 1/(1+B)

Each branch retains both endpoint labels, including duplicate labels when its
length is zero. The label count is bounded by the source Q using the sum of
branch lengths. A B-Lipschitz path moves by at most B/(1+B), hence at most one,
from its selected node. No probability or conditional-law assumption is used.
-/
open Set
open scoped BigOperators NNReal
namespace PaperFormalization.Manuscript

noncomputable def populationBranchSubdivisions (B : ℝ≥0) (a b : ℝ) : ℕ :=
  radiusBranchSubdivisions ((1+B)/2) 1 a b

noncomputable abbrev PopulationGridLabel (B : ℝ≥0) (J : ℕ) (a b : Fin (J+1) → ℝ) :=
  (j : Fin (J+1)) × Fin (populationBranchSubdivisions B (a j) (b j)+1)

noncomputable def populationGridTime (B : ℝ≥0) (J : ℕ) (a b : Fin (J+1) → ℝ)
    (label : PopulationGridLabel B J a b) : ℝ :=
  closedBranchGrid (a label.1) (b label.1) (populationBranchSubdivisions B (a label.1) (b label.1)) label.2

noncomputable def populationGridBudget (B : ℝ≥0) (J : ℕ) (T : ℝ) : ℕ :=
  ⌈(1+(B : ℝ))*T⌉₊ + 2*(J+1)

/-- Literal ceil subdivisions, with a harmless max-one guard at zero length. -/
theorem populationBranchSubdivisions_eq (B : ℝ≥0) (a b : ℝ) :
    populationBranchSubdivisions B a b = max 1 ⌈(1+(B : ℝ))*(b-a)⌉₊ := by
  unfold populationBranchSubdivisions radiusBranchSubdivisions
  congr 2
  simp only [NNReal.coe_div,NNReal.coe_add,NNReal.coe_one,NNReal.coe_ofNat,div_one]
  ring

theorem populationBranchSubdivisions_pos (B : ℝ≥0) (a b : ℝ) :
    0 < populationBranchSubdivisions B a b := radiusBranchSubdivisions_pos _ _ _ _

/-- The actual mesh has the source length bound even at zero branch length. -/
theorem populationBranchSubdivisions_mesh_le (B : ℝ≥0) (a b : ℝ) :
    (b-a)/populationBranchSubdivisions B a b ≤ 1/(1+(B : ℝ)) := by
  have hb := radiusBranchSubdivisions_mesh_le ((1+B)/2) 1 a b (by norm_num)
  simp only [NNReal.coe_div,NNReal.coe_add,NNReal.coe_one,NNReal.coe_ofNat] at hb
  apply (le_div_iff₀ (by positivity : 0 < 1+(B : ℝ))).mpr
  change _ ≤ _ at hb
  dsimp only [populationBranchSubdivisions]
  nlinarith

/-- All sigma-labelled nodes lie in the indicated closed branch. -/
theorem populationGridTime_mem (B : ℝ≥0) (J : ℕ) (a b : Fin (J+1) → ℝ)
    (hab : ∀ j, a j ≤ b j) (label : PopulationGridLabel B J a b) :
    populationGridTime B J a b label ∈ Icc (a label.1) (b label.1) :=
  closedBranchGrid_mem _ _ (hab _) (populationBranchSubdivisions_pos _ _ _) _

/-- Both endpoint labels are present; they may evaluate to the same time. -/
theorem populationBranchGrid_endpoints (B : ℝ≥0) (a b : ℝ) :
    closedBranchGrid a b (populationBranchSubdivisions B a b) 0 = a ∧
    closedBranchGrid a b (populationBranchSubdivisions B a b)
      (Fin.last (populationBranchSubdivisions B a b)) = b :=
  radiusBranchGrid_endpoints _ _ _ _

/-- Actual labelled cardinality is bounded by the source Q; its fixed two
labels per branch account for all degenerate branches without a false count. -/
theorem populationGridLabel_card_le (B : ℝ≥0) (J : ℕ) (T : ℝ) (a b : Fin (J+1) → ℝ)
    (hab : ∀ j, a j ≤ b j) (hlen : ∑ j, (b j-a j) ≤ T) :
    Fintype.card (PopulationGridLabel B J a b) ≤ populationGridBudget B J T := by
  have hb := radiusBranchGrid_total_card_le ((1+B)/2) 1 T a b (by norm_num) hab hlen
  simp only [NNReal.coe_div,NNReal.coe_add,NNReal.coe_one,NNReal.coe_ofNat,div_one,Fintype.card_fin] at hb
  have hc := Nat.le_ceil ((1+(B : ℝ))*T)
  have hcard : (Fintype.card (PopulationGridLabel B J a b) : ℝ) =
      ∑ j, ((populationBranchSubdivisions B (a j) (b j) : ℝ)+1) := by
    simp only [PopulationGridLabel,Fintype.card_sigma,Fintype.card_fin,Nat.cast_sum,Nat.cast_add,Nat.cast_one]
  have hbudget : (populationGridBudget B J T : ℝ) =
      (⌈(1+(B : ℝ))*T⌉₊ : ℝ)+2*((J : ℝ)+1) := by
    simp only [populationGridBudget,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  suffices hh : (Fintype.card (PopulationGridLabel B J a b) : ℝ) ≤ (populationGridBudget B J T : ℝ) by exact_mod_cast hh
  rw [hcard,hbudget]
  change (∑ j, ((radiusBranchSubdivisions ((1+B)/2) 1 (a j) (b j) : ℝ)+1)) ≤ _
  push_cast at hb
  nlinarith

theorem populationGridBudget_two_le (B : ℝ≥0) (J : ℕ) (T : ℝ) :
    2 ≤ populationGridBudget B J T := by unfold populationGridBudget; omega

/-- Every actual branch point has a same-branch grid node at time distance
at most 1/(1+B), and path displacement at most B/(1+B), hence at most one. -/
theorem exists_populationBranchGrid_near {E : Type*} [PseudoMetricSpace E]
    (B : ℝ≥0) (a b : ℝ) (hab : a ≤ b) (Z : ℝ → E)
    (hZ : LipschitzOnWith B Z (Icc a b)) (t : ℝ) (ht : t ∈ Icc a b) :
    ∃ i : Fin (populationBranchSubdivisions B a b+1),
      dist t (closedBranchGrid a b (populationBranchSubdivisions B a b) i) ≤ 1/(1+(B : ℝ)) ∧
      dist (Z t) (Z (closedBranchGrid a b (populationBranchSubdivisions B a b) i)) ≤
        (B : ℝ)/(1+(B : ℝ)) ∧
      dist (Z t) (Z (closedBranchGrid a b (populationBranchSubdivisions B a b) i)) ≤ 1 := by
  obtain ⟨i,hi⟩ := exists_closedBranchGrid_near a b hab (populationBranchSubdivisions_pos B a b) t ht
  have htime := hi.trans (populationBranchSubdivisions_mesh_le B a b)
  have hdist := (hZ.dist_le_mul t ht _ (closedBranchGrid_mem a b hab (populationBranchSubdivisions_pos B a b) i)).trans
    (mul_le_mul_of_nonneg_left htime B.coe_nonneg)
  have hone : (B : ℝ)/(1+(B : ℝ)) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hdist' : dist (Z t) (Z (closedBranchGrid a b (populationBranchSubdivisions B a b) i)) ≤
      (B : ℝ)/(1+(B : ℝ)) := by simpa only [mul_one_div] using hdist
  exact ⟨i,htime,hdist',hdist'.trans hone⟩
end PaperFormalization.Manuscript
