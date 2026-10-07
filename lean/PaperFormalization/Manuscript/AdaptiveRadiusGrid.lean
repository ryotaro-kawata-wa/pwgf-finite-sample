import PaperFormalization.Manuscript.FiniteTimeGrid

/-! # Actual adaptive grids for the uniform radius event

The grid retains separate endpoint labels on every closed branch. The number
of subdivisions is at least one, even for a zero-length branch or zero speed;
the common radius increment is at most D/2 without dividing by the speed.
-/
open Set MeasureTheory
open scoped BigOperators NNReal
namespace PaperFormalization.Manuscript

/-- Actual subdivision count for mesh controlled by the radius and speed. -/
noncomputable def radiusBranchSubdivisions (B : ℝ≥0) (D a b : ℝ) : ℕ :=
  max 1 ⌈2 * (B : ℝ) * (b-a) / D⌉₊

/-- Every branch has a positive subdivision count, also at zero speed/length. -/
theorem radiusBranchSubdivisions_pos (B : ℝ≥0) (D a b : ℝ) :
    0 < radiusBranchSubdivisions B D a b :=
  lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) (le_max_left _ _)

/-- Both endpoint traces are represented, including the two labelled copies
when a=b. -/
theorem radiusBranchGrid_endpoints (B : ℝ≥0) (D a b : ℝ) :
    closedBranchGrid a b (radiusBranchSubdivisions B D a b) 0 = a ∧
    closedBranchGrid a b (radiusBranchSubdivisions B D a b)
      (Fin.last (radiusBranchSubdivisions B D a b)) = b := by
  have hM : (radiusBranchSubdivisions B D a b : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (radiusBranchSubdivisions_pos B D a b))
  constructor
  · simp [closedBranchGrid]
  · simp only [closedBranchGrid, Fin.val_last]
    field_simp
    ring

/-- Exact labelled node count, including both endpoints. -/
theorem radiusBranchSubdivisions_card_le (B : ℝ≥0) (D a b : ℝ)
    (hD : 0 < D) (hab : a ≤ b) :
    ((radiusBranchSubdivisions B D a b : ℕ) : ℝ) + 1 ≤
      2 + 2 * (B : ℝ) * (b-a) / D := by
  have hr : 0 ≤ 2 * (B : ℝ) * (b-a) / D := by positivity
  have hc := (Nat.ceil_lt_add_one hr).le
  have hmax : (radiusBranchSubdivisions B D a b : ℝ) ≤
      1 + 2 * (B : ℝ) * (b-a) / D := by
    simp only [radiusBranchSubdivisions, Nat.cast_max, Nat.cast_one]
    exact max_le (by linarith) (by linarith)
  linarith

/-- The speed times a mesh width is at most half the radius, including B=0. -/
theorem radiusBranchSubdivisions_mesh_le (B : ℝ≥0) (D a b : ℝ)
    (hD : 0 < D) :
    (B : ℝ) * ((b-a) / radiusBranchSubdivisions B D a b) ≤ D / 2 := by
  have hM : 0 < (radiusBranchSubdivisions B D a b : ℝ) :=
    Nat.cast_pos.mpr (radiusBranchSubdivisions_pos B D a b)
  have hceil := Nat.le_ceil (2 * (B : ℝ) * (b-a) / D)
  have hmax : (⌈2 * (B : ℝ) * (b-a) / D⌉₊ : ℝ) ≤
      radiusBranchSubdivisions B D a b := by
    exact_mod_cast (le_max_right 1 ⌈2 * (B : ℝ) * (b-a) / D⌉₊)
  have hmul := (div_le_iff₀ hD).mp (hceil.trans hmax)
  rw [← mul_div_assoc, div_le_iff₀ hM]
  nlinarith

/-- Bounds at the actual adaptive nodes give the radius bound everywhere
on the same branch, with no relation to a different branch's endpoint trace. -/
theorem radiusBranchGrid_norm_bound {E : Type*} [NormedAddCommGroup E]
    (B : ℝ≥0) (D a b : ℝ) (hD : 0 < D) (hab : a ≤ b)
    (Z : ℝ → E) (hZ : LipschitzOnWith B Z (Icc a b))
    (hnode : ∀ i, ‖Z (closedBranchGrid a b (radiusBranchSubdivisions B D a b) i)‖ ≤ D/2)
    (t : ℝ) (ht : t ∈ Icc a b) : ‖Z t‖ ≤ D := by
  have hn : LipschitzOnWith B (fun s => ‖Z s‖) (Icc a b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    exact (dist_norm_norm_le (Z s) (Z t)).trans (by simpa only [dist_eq_norm] using hZ.dist_le_mul s hs t ht)
  have hb := closedBranchGrid_lipschitz_bound a b hab
    (radiusBranchSubdivisions_pos B D a b) (fun s => ‖Z s‖) B hn (D/2) hnode t ht
  have hm := radiusBranchSubdivisions_mesh_le B D a b hD
  linarith

/-- The sum of actual labelled node counts depends on the total branch
length, not on a separate T bound for each branch. -/
theorem radiusBranchGrid_total_card_le {ι : Type*} [Fintype ι]
    (B : ℝ≥0) (D T : ℝ) (a b : ι → ℝ)
    (hD : 0 < D) (hab : ∀ j, a j ≤ b j) (hT : ∑ j, (b j-a j) ≤ T) :
    (∑ j, (((radiusBranchSubdivisions B D (a j) (b j) : ℕ) : ℝ) + 1)) ≤
      2 * Fintype.card ι + 2 * (B : ℝ) * T / D := by
  calc
    _ ≤ ∑ j, (2 + 2 * (B : ℝ) * (b j-a j) / D) :=
      Finset.sum_le_sum (fun j _ => radiusBranchSubdivisions_card_le B D (a j) (b j) hD (hab j))
    _ = 2 * Fintype.card ι + 2 * (B : ℝ) * (∑ j, (b j-a j)) / D := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, ← Finset.sum_div, ← Finset.mul_sum]
      ring
    _ ≤ _ := add_le_add le_rfl (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hT (by positivity : 0 ≤ 2 * (B : ℝ))) hD.le)

end PaperFormalization.Manuscript
