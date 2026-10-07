import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! # The actual radial clipping map of the source

The norm bound and nonexpansiveness are proved for the concrete formula,
including the sphere and zero. No differentiability of clipping is used.
-/

open Set

namespace PaperFormalization.Manuscript

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Radial projection onto the closed radius-D ball, with identity on it. -/
noncomputable def sourceRadialClip (D : ℝ) (x : E) : E :=
  if ‖x‖ ≤ D then x else (D / ‖x‖) • x

/-- Clipping changes no point in the original closed ball. -/
theorem sourceRadialClip_of_norm_le (D : ℝ) (x : E) (hx : ‖x‖ ≤ D) :
    sourceRadialClip D x = x := if_pos hx

/-- Outside the ball the formula has exactly the source radial scale. -/
theorem sourceRadialClip_of_lt_norm (D : ℝ) (x : E) (hx : D < ‖x‖) :
    sourceRadialClip D x = (D / ‖x‖) • x := if_neg (not_le.mpr hx)

/-- The clipped point always belongs to the radius-D ball, including D=0. -/
theorem norm_sourceRadialClip_le (D : ℝ) (hD : 0 ≤ D) (x : E) :
    ‖sourceRadialClip D x‖ ≤ D := by
  by_cases hx : ‖x‖ ≤ D
  · simpa only [sourceRadialClip_of_norm_le D x hx] using hx
  · have hn : 0 < ‖x‖ := lt_of_le_of_lt hD (lt_of_not_ge hx)
    rw [sourceRadialClip, if_neg hx, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hD hn.le), div_mul_cancel₀ _ hn.ne']

/-- Clipping never increases the original norm. -/
theorem norm_sourceRadialClip_le_norm (D : ℝ) (hD : 0 ≤ D) (x : E) :
    ‖sourceRadialClip D x‖ ≤ ‖x‖ := by
  by_cases hx : ‖x‖ ≤ D
  · rw [sourceRadialClip_of_norm_le D x hx]
  · exact (norm_sourceRadialClip_le D hD x).trans (lt_of_not_ge hx).le

/-- The concrete clipped point satisfies the metric projection variational
inequality against every point in the closed ball. -/
theorem sourceRadialClip_inner_sub_le_zero (D : ℝ) (hD : 0 ≤ D) (x y : E)
    (hy : ‖y‖ ≤ D) :
    inner ℝ (x - sourceRadialClip D x) (y - sourceRadialClip D x) ≤ 0 := by
  by_cases hx : ‖x‖ ≤ D
  · simp [sourceRadialClip_of_norm_le D x hx]
  · have hn : 0 < ‖x‖ := lt_of_le_of_lt hD (lt_of_not_ge hx)
    have hr : 0 ≤ 1 - D / ‖x‖ := by
      have hh := (div_le_one hn).mpr (lt_of_not_ge hx).le
      linarith
    have hi : inner ℝ x y ≤ ‖x‖ * D :=
      (real_inner_le_norm x y).trans (mul_le_mul_of_nonneg_left hy (norm_nonneg x))
    rw [sourceRadialClip, if_neg hx]
    have heq : x - (D / ‖x‖) • x = (1 - D / ‖x‖) • x := by rw [sub_smul, one_smul]
    rw [heq, real_inner_smul_left, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    have hcancel : D / ‖x‖ * ‖x‖ ^ 2 = ‖x‖ * D := by field_simp
    rw [hcancel]
    exact mul_nonpos_of_nonneg_of_nonpos hr (sub_nonpos.mpr hi)

/-- Two variational inequalities yield the sharp nonexpansive bound. -/
theorem sourceRadialClip_norm_sub_le (D : ℝ) (hD : 0 ≤ D) (x y : E) :
    ‖sourceRadialClip D x - sourceRadialClip D y‖ ≤ ‖x - y‖ := by
  let a := sourceRadialClip D x
  let b := sourceRadialClip D y
  have hx := sourceRadialClip_inner_sub_le_zero D hD x b (norm_sourceRadialClip_le D hD y)
  have hy := sourceRadialClip_inner_sub_le_zero D hD y a (norm_sourceRadialClip_le D hD x)
  change inner ℝ (x-a) (b-a) ≤ 0 at hx
  change inner ℝ (y-b) (a-b) ≤ 0 at hy
  have hid : ‖a-b‖ ^ 2 ≤ inner ℝ (x-y) (a-b) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_comm b a] at hx hy ⊢
    linarith
  have hi := real_inner_le_norm (x-y) (a-b)
  have hnon : 0 ≤ ‖a-b‖ := norm_nonneg _
  change ‖a-b‖ ≤ ‖x-y‖
  nlinarith [norm_nonneg (x-y)]

/-- The actual radial clipping map has Lipschitz constant exactly one. -/
theorem sourceRadialClip_lipschitz (D : ℝ) (hD : 0 ≤ D) :
    LipschitzWith 1 (sourceRadialClip (E := E) D) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using
    sourceRadialClip_norm_sub_le D hD x y

/-- Clipping is continuous even on the boundary sphere. -/
theorem sourceRadialClip_continuous (D : ℝ) (hD : 0 ≤ D) :
    Continuous (sourceRadialClip (E := E) D) := (sourceRadialClip_lipschitz D hD).continuous

/-- Equality with the original min formula, with the zero point also valid. -/
theorem sourceRadialClip_eq_min (D : ℝ) (hD : 0 ≤ D) (x : E) :
    sourceRadialClip D x = (min 1 (D / ‖x‖)) • x := by
  by_cases hz : x = 0
  · subst x
    simp [sourceRadialClip, hD]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hz
  by_cases hx : ‖x‖ ≤ D
  · rw [sourceRadialClip_of_norm_le D x hx,
      min_eq_left ((le_div_iff₀ hn).mpr (by simpa using hx)), one_smul]
  · rw [sourceRadialClip, if_neg hx,
      min_eq_right ((div_le_one hn).mpr (lt_of_not_ge hx).le)]

end PaperFormalization.Manuscript
