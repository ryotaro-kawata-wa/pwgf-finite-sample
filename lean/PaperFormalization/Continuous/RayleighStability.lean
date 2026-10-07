import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-! # Stability of the unit-sphere Rayleigh infimum

The manuscript defines sampled curvature directly as the infimum of
`⟪v, A v⟫` over unit vectors. This file uses precisely that definition.
The stability estimate needs neither symmetry nor finite dimensionality.
Nontriviality ensures that the unit sphere is nonempty. No assertion that
the infimum is attained or is an eigenvalue is made here.
-/

open MeasureTheory Set
open scoped NNReal

namespace PaperFormalization.Continuous

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Values of the quadratic form on unit vectors, with the manuscript's order
of the arguments in the inner product. -/
def rayleighValues (A : E →L[ℝ] E) : Set ℝ :=
  (fun v => inner ℝ v (A v)) '' {v : E | ‖v‖ = 1}

/-- The unit-sphere infimum used to define the manuscript's sampled curvature. -/
noncomputable def rayleighInf (A : E →L[ℝ] E) : ℝ := sInf (rayleighValues A)

/-- A unit-vector quadratic form is bounded by the operator norm. -/
theorem abs_inner_apply_le_opNorm (A : E →L[ℝ] E) (v : E) (hv : ‖v‖ = 1) :
    |inner ℝ v (A v)| ≤ ‖A‖ := by
  calc
    |inner ℝ v (A v)| ≤ ‖v‖ * ‖A v‖ := abs_real_inner_le_norm v (A v)
    _ ≤ ‖v‖ * (‖A‖ * ‖v‖) := mul_le_mul_of_nonneg_left (A.le_opNorm v) (norm_nonneg v)
    _ = ‖A‖ := by rw [hv]; ring

/-- The Rayleigh values are bounded below, even without nontriviality. -/
theorem rayleighValues_bddBelow (A : E →L[ℝ] E) : BddBelow (rayleighValues A) := by
  refine ⟨-‖A‖, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  exact (abs_le.mp (abs_inner_apply_le_opNorm A v hv)).1

/-- A nontrivial real inner product space has a unit vector, so its Rayleigh
value set is nonempty. -/
theorem rayleighValues_nonempty [Nontrivial E] (A : E →L[ℝ] E) :
    (rayleighValues A).Nonempty := by
  obtain ⟨v, hv⟩ := exists_norm_eq E (show (0 : ℝ) ≤ 1 by norm_num)
  exact ⟨inner ℝ v (A v), v, hv, rfl⟩

/-- The infimum is below each unit-vector quadratic form. -/
theorem rayleighInf_le_unit (A : E →L[ℝ] E) (v : E) (hv : ‖v‖ = 1) :
    rayleighInf A ≤ inner ℝ v (A v) :=
  csInf_le (rayleighValues_bddBelow A) ⟨v, hv, rfl⟩

/-- The unit-sphere infimum controls the quadratic form on every vector.
The zero-vector case is handled explicitly, without division by its norm. -/
theorem rayleighInf_mul_norm_sq_le (A : E →L[ℝ] E) (v : E) :
    rayleighInf A * ‖v‖ ^ 2 ≤ inner ℝ v (A v) := by
  by_cases hv : v = 0
  · simp [hv]
  have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hunit : ‖‖v‖⁻¹ • v‖ = 1 := by
    simp [norm_smul, hvnorm]
  have h := rayleighInf_le_unit A (‖v‖⁻¹ • v) hunit
  rw [map_smul, real_inner_smul_left, real_inner_smul_right] at h
  calc
    rayleighInf A * ‖v‖ ^ 2 ≤
        (‖v‖⁻¹ * (‖v‖⁻¹ * inner ℝ v (A v))) * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h (sq_nonneg ‖v‖)
    _ = inner ℝ v (A v) := by field_simp

/-- The absolute Rayleigh infimum is bounded by the operator norm. -/
theorem abs_rayleighInf_le_opNorm [Nontrivial E] (A : E →L[ℝ] E) :
    |rayleighInf A| ≤ ‖A‖ := by
  apply abs_le.mpr
  constructor
  · apply le_csInf (rayleighValues_nonempty A)
    rintro _ ⟨v, hv, rfl⟩
    exact (abs_le.mp (abs_inner_apply_le_opNorm A v hv)).1
  · obtain ⟨v, hv⟩ := exists_norm_eq E (show (0 : ℝ) ≤ 1 by norm_num)
    exact (rayleighInf_le_unit A v hv).trans (abs_le.mp (abs_inner_apply_le_opNorm A v hv)).2

/-- Quadratic forms at a common unit vector differ by at most the operator
norm of the difference. -/
theorem abs_inner_apply_sub_le_opNorm (A B : E →L[ℝ] E) (v : E) (hv : ‖v‖ = 1) :
    |inner ℝ v (A v) - inner ℝ v (B v)| ≤ ‖A - B‖ := by
  have h := abs_inner_apply_le_opNorm (A - B) v hv
  change |inner ℝ v (A v - B v)| ≤ ‖A - B‖ at h
  simpa only [inner_sub_right] using h

/-- A one-sided perturbation estimate for the Rayleigh infimum. -/
theorem rayleighInf_sub_le_opNorm [Nontrivial E] (A B : E →L[ℝ] E) :
    rayleighInf A - rayleighInf B ≤ ‖A - B‖ := by
  have h : rayleighInf A - ‖A - B‖ ≤ rayleighInf B := by
    apply le_csInf (rayleighValues_nonempty B)
    rintro _ ⟨v, hv, rfl⟩
    have hA := rayleighInf_le_unit A v hv
    have hdiff := (abs_le.mp (abs_inner_apply_sub_le_opNorm A B v hv)).2
    linarith
  linarith

/-- Dimension-free stability; no eigenvalue characterization or symmetry
assumption is used. -/
theorem abs_rayleighInf_sub_le_opNorm [Nontrivial E] (A B : E →L[ℝ] E) :
    |rayleighInf A - rayleighInf B| ≤ ‖A - B‖ := by
  apply abs_le.mpr
  constructor
  · have h := rayleighInf_sub_le_opNorm B A
    rw [norm_sub_rev B A] at h
    linarith
  · exact rayleighInf_sub_le_opNorm A B

/-- The Rayleigh infimum is a 1-Lipschitz function of the operator. -/
theorem rayleighInf_lipschitz [Nontrivial E] :
    LipschitzWith 1 (rayleighInf (E := E)) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul] using
    abs_rayleighInf_sub_le_opNorm A B

/-- An operator path transfers its Lipschitz constant to the sampled curvature. -/
theorem rayleighInf_lipschitzOn [Nontrivial E] (A : ℝ → E →L[ℝ] E)
    (K : ℝ≥0) (s : Set ℝ) (hA : LipschitzOnWith K A s) :
    LipschitzOnWith K (fun t => rayleighInf (A t)) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht u hu
  calc
    dist (rayleighInf (A t)) (rayleighInf (A u)) ≤ dist (A t) (A u) := by
      simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using abs_rayleighInf_sub_le_opNorm (A t) (A u)
    _ ≤ (K : ℝ) * dist t u := hA.dist_le_mul t ht u hu

/-- Continuous operator paths give continuous Rayleigh infima on the same set. -/
theorem rayleighInf_continuousOn [Nontrivial E] (A : ℝ → E →L[ℝ] E)
    (s : Set ℝ) (hA : ContinuousOn A s) :
    ContinuousOn (fun t => rayleighInf (A t)) s :=
  rayleighInf_lipschitz.continuous.comp_continuousOn hA

/-- Branch-Lipschitz operator paths give absolutely continuous curvature. -/
theorem rayleighInf_ac [Nontrivial E] (A : ℝ → E →L[ℝ] E)
    (K : ℝ≥0) (a b : ℝ) (hA : LipschitzOnWith K A (uIcc a b)) :
    AbsolutelyContinuousOnInterval (fun t => rayleighInf (A t)) a b :=
  (rayleighInf_lipschitzOn A K (uIcc a b) hA).absolutelyContinuousOnInterval

/-- Continuity alone suffices for branch curvature integrability. -/
theorem rayleighInf_intervalIntegrable [Nontrivial E] (A : ℝ → E →L[ℝ] E)
    (a b : ℝ) (hA : ContinuousOn A (uIcc a b)) :
    IntervalIntegrable (fun t => rayleighInf (A t)) volume a b :=
  (rayleighInf_continuousOn A (uIcc a b) hA).intervalIntegrable

end PaperFormalization.Continuous
