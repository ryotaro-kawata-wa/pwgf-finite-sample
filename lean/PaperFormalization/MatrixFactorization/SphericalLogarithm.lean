import PaperFormalization.MatrixFactorization.SphericalExponential

/-! # MF03b: shortest spherical LOG, with its actual domain

LOG takes an explicit distance<pi proof. No logarithm or unique shortest arc is
claimed at an antipodal pair. The pole is treated separately, so no derivative
of the unsquared distance at zero is used. All equalities concern the ambient
representatives of the SAME UnitSphere and sphericalExp used in MF02/03a.
-/
open MeasureTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

@[simp] theorem cos_sphericalDistance {d : Nat} (y w : UnitSphere d) :
    Real.cos (sphericalDistance y w) = inner Real y.val w.val := by
  rw [sphericalDistance_eq_angle, InnerProductGeometry.cos_angle]
  simp

theorem sphericalDistance_pos_of_ne {d : Nat} (y w : UnitSphere d) (h : w ≠ y) :
    0 < sphericalDistance y w := by
  have hn := sphericalDistance_nonneg y w
  have he : sphericalDistance y w ≠ 0 := fun he => h ((sphericalDistance_eq_zero_iff y w).1 he).symm
  exact lt_of_le_of_ne hn (Ne.symm he)

/-- Algebraic normalization; unit/tangent claims below require 0<distance<pi. -/
noncomputable def shortArcUnit {d : Nat} (y w : UnitSphere d) : Weight d :=
  (Real.sin (sphericalDistance y w))⁻¹ •
    (w.val - Real.cos (sphericalDistance y w) • y.val)

theorem shortArcUnit_tangent {d : Nat} (y w : UnitSphere d) :
    inner Real y.val (shortArcUnit y w) = 0 := by
  simp only [shortArcUnit, inner_smul_right, inner_sub_right,
    real_inner_self_eq_norm_sq, unitSphere_norm, one_pow, mul_one,
    cos_sphericalDistance, sub_self, mul_zero]

theorem shortArcUnit_norm {d : Nat} (y w : UnitSphere d)
    (hp : 0 < sphericalDistance y w) (hs : sphericalDistance y w < Real.pi) :
    ‖shortArcUnit y w‖ = 1 := by
  let t := sphericalDistance y w
  have hsin : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi hp hs
  have hc : inner Real w.val y.val = Real.cos t := by
    rw [real_inner_comm]
    exact (cos_sphericalDistance y w).symm
  have hres : ‖w.val - Real.cos t • y.val‖^2 = (Real.sin t)^2 := by
    rw [norm_sub_sq_real, norm_smul, inner_smul_right, hc]
    simp only [unitSphere_norm, Real.norm_eq_abs, sq_abs, one_pow, mul_one]
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hsq : ‖shortArcUnit y w‖^2 = 1 := by
    change ‖(Real.sin t)⁻¹ • (w.val - Real.cos t • y.val)‖^2 = 1
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hres]
    field_simp [hsin.ne']
  nlinarith [norm_nonneg (shortArcUnit y w)]

theorem shortArc_decomposition {d : Nat} (y w : UnitSphere d)
    (hp : 0 < sphericalDistance y w) (hs : sphericalDistance y w < Real.pi) :
    w.val = Real.cos (sphericalDistance y w) • y.val +
      Real.sin (sphericalDistance y w) • shortArcUnit y w := by
  have hsin := Real.sin_pos_of_pos_of_lt_pi hp hs
  rw [shortArcUnit, smul_smul, mul_inv_cancel₀ hsin.ne', one_smul]
  abel

/-- The hshort argument is the domain restriction, not a conclusion to be supplied later. -/
noncomputable def sphericalLog {d : Nat} (y w : UnitSphere d)
    (_hshort : sphericalDistance y w < Real.pi) : Weight d :=
  if w = y then 0 else sphericalDistance y w • shortArcUnit y w

@[simp] theorem sphericalLog_self {d : Nat} (y : UnitSphere d)
    (hs : sphericalDistance y y < Real.pi) : sphericalLog y y hs = 0 := by
  simp [sphericalLog]

theorem sphericalLog_tangent {d : Nat} (y w : UnitSphere d)
    (hs : sphericalDistance y w < Real.pi) : inner Real y.val (sphericalLog y w hs) = 0 := by
  unfold sphericalLog
  split_ifs
  · simp
  · rw [inner_smul_right, shortArcUnit_tangent, mul_zero]

theorem sphericalLog_norm {d : Nat} (y w : UnitSphere d)
    (hs : sphericalDistance y w < Real.pi) : ‖sphericalLog y w hs‖ = sphericalDistance y w := by
  by_cases h : w = y
  · subst w
    simp
  · rw [sphericalLog, if_neg h, norm_smul,
      shortArcUnit_norm y w (sphericalDistance_pos_of_ne y w h) hs,
      Real.norm_eq_abs, abs_of_nonneg (sphericalDistance_nonneg y w), mul_one]

/-- Source EXP_y(LOG_y w)=w on the entire stated domain, including w=y. -/
theorem sphericalExp_log {d : Nat} (y w : UnitSphere d)
    (hs : sphericalDistance y w < Real.pi) :
    sphericalExp y (sphericalLog y w hs) (sphericalLog_tangent y w hs) = w := by
  by_cases h : w = y
  · subst w
    apply Subtype.ext
    simp
  · have hp := sphericalDistance_pos_of_ne y w h
    have hn := shortArcUnit_norm y w hp hs
    have hu : shortArcUnit y w ≠ 0 := by
      intro he
      rw [he, norm_zero] at hn
      norm_num at hn
    apply Subtype.ext
    change sphereExpVector y (sphericalLog y w hs) = w.val
    rw [sphericalLog, if_neg h, sphereExpVector_scaled y (shortArcUnit y w) hu,
      hn, mul_one, div_one]
    exact (shortArc_decomposition y w hp hs).symm

/-- Below the injectivity radius the length of the EXP displacement is ||v||. -/
theorem sphericalDistance_exp {d : Nat} (y : UnitSphere d) (v : Weight d)
    (htan : inner Real y.val v = 0) (hv : ‖v‖ < Real.pi) :
    sphericalDistance y (sphericalExp y v htan) = ‖v‖ := by
  unfold sphericalDistance
  change Real.arccos (inner Real y.val (sphereExpVector y v)) = ‖v‖
  have hi : inner Real y.val (sphereExpVector y v) = Real.cos ‖v‖ := by
    simp [sphereExpVector, inner_add_right, inner_smul_right, htan]
  rw [hi, Real.arccos_cos (norm_nonneg v) hv.le]

/-- The reverse local inverse, not asserted for tangent lengths >= pi. -/
theorem sphericalLog_exp {d : Nat} (y : UnitSphere d) (v : Weight d)
    (htan : inner Real y.val v = 0) (hv : ‖v‖ < Real.pi) :
    sphericalLog y (sphericalExp y v htan)
      (by rw [sphericalDistance_exp y v htan hv]; exact hv) = v := by
  by_cases hz : v = 0
  · subst v
    simp
  · have hr := norm_pos_iff.mpr hz
    have hsin := Real.sin_pos_of_pos_of_lt_pi hr hv
    have hd := sphericalDistance_exp y v htan hv
    have hne : sphericalExp y v htan ≠ y := by
      intro he
      rw [he, sphericalDistance_self] at hd
      linarith
    rw [sphericalLog, if_neg hne, shortArcUnit, hd]
    change ‖v‖ • ((Real.sin ‖v‖)⁻¹ •
      (sphereExpVector y v - Real.cos ‖v‖ • y.val)) = v
    rw [sphereExpVector_formula y v hz]
    ext i
    simp only [PiLp.smul_apply, PiLp.add_apply, PiLp.sub_apply, smul_eq_mul]
    field_simp [hr.ne', hsin.ne']
    ring

end PaperFormalization.MatrixFactorization
