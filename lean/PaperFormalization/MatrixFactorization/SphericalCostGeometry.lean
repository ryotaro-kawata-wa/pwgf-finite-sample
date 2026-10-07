import PaperFormalization.MatrixFactorization.SphericalRadialWeight

/-! # MF03: half-squared cost, tangent gradient, and Hessian quadratic form

MF03 checkpoint candidate; see MF03_VALIDATION.md for execution status.
These are expressions for the existing angular cost.
The derivative identifications are proved in SphericalCostDifferential.
The normalized radial direction is totalized at the pole, but its coefficient
vanishes there; the Hessian is exactly the tangent-space identity at the pole.
No formula is asserted to be a derivative at the antipode or equatorial tie.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def poleCost {d : Nat} (y w : UnitSphere d) : Real :=
  (sphericalDistance w y)^2/2

noncomputable def poleGradient {d : Nat} (y w : UnitSphere d) : Weight d :=
  (Real.sinc (sphericalDistance w y))⁻¹ •
    (Real.cos (sphericalDistance w y) • w.val-y.val)

noncomputable def poleCostSlope {d : Nat} (y w : UnitSphere d) (v : Weight d) : Real :=
  inner Real (poleGradient y w) v

noncomputable def poleHessian {d : Nat} (y w : UnitSphere d) (v : Weight d) : Real :=
  sphericalRadialWeight (sphericalDistance w y) * (norm v)^2 +
    (1-sphericalRadialWeight (sphericalDistance w y)) *
      (inner Real (shortArcUnit w y) v)^2

@[simp] theorem poleCost_self {d : Nat} (y : UnitSphere d) : poleCost y y = 0 := by
  simp [poleCost]

@[simp] theorem poleGradient_self {d : Nat} (y : UnitSphere d) : poleGradient y y = 0 := by
  simp [poleGradient]

@[simp] theorem poleCostSlope_self {d : Nat} (y : UnitSphere d) (v : Weight d) :
    poleCostSlope y y v = 0 := by simp [poleCostSlope]

@[simp] theorem poleHessian_self {d : Nat} (y : UnitSphere d) (v : Weight d) :
    poleHessian y y v = (norm v)^2 := by simp [poleHessian]

@[simp] theorem poleCostSlope_zero {d : Nat} (y w : UnitSphere d) :
    poleCostSlope y w 0 = 0 := by simp [poleCostSlope]

@[simp] theorem poleHessian_zero {d : Nat} (y w : UnitSphere d) :
    poleHessian y w 0 = 0 := by simp [poleHessian]

theorem poleCost_continuous {d : Nat} (y : UnitSphere d) : Continuous (poleCost y) := by
  unfold poleCost sphericalDistance
  fun_prop

theorem poleGradient_measurable (d : Nat) :
    Measurable (fun z : UnitSphere d × UnitSphere d => poleGradient z.1 z.2) := by
  unfold poleGradient sphericalDistance
  fun_prop

theorem poleCostSlope_measurable (d : Nat) :
    Measurable (fun z : (UnitSphere d × UnitSphere d) × Weight d =>
      poleCostSlope z.1.1 z.1.2 z.2) := by
  unfold poleCostSlope
  exact ((poleGradient_measurable d).comp measurable_fst).inner measurable_snd

theorem poleHessian_measurable (d : Nat) :
    Measurable (fun z : (UnitSphere d × UnitSphere d) × Weight d =>
      poleHessian z.1.1 z.1.2 z.2) := by
  unfold poleHessian sphericalRadialWeight shortArcUnit sphericalDistance
  fun_prop

/-- The sign is outward: grad (d(w,y)^2/2) = -LOG_w(y). -/
theorem poleGradient_eq_neg_log {d : Nat} (y w : UnitSphere d)
    (hs : sphericalDistance w y < Real.pi) :
    poleGradient y w = -sphericalLog w y hs := by
  by_cases h : y = w
  · subst y
    simp
  · have hr := sphericalDistance_pos_of_ne w y h
    have hsin := Real.sin_pos_of_pos_of_lt_pi hr hs
    rw [poleGradient, sphericalLog, if_neg h, shortArcUnit,
      Real.sinc_of_ne_zero hr.ne']
    ext i
    simp only [PiLp.smul_apply, PiLp.sub_apply, PiLp.neg_apply, smul_eq_mul]
    field_simp [hr.ne', hsin.ne']
    ring

theorem poleGradient_tangent {d : Nat} (y w : UnitSphere d) :
    inner Real w.val (poleGradient y w) = 0 := by
  simp only [poleGradient, inner_smul_right, inner_sub_right,
    real_inner_self_eq_norm_sq, unitSphere_norm, one_pow, mul_one,
    cos_sphericalDistance, sub_self, mul_zero]

theorem poleGradient_norm {d : Nat} (y w : UnitSphere d)
    (hs : sphericalDistance w y < Real.pi) :
    norm (poleGradient y w) = sphericalDistance w y := by
  rw [poleGradient_eq_neg_log y w hs, norm_neg, sphericalLog_norm]

theorem poleCostSlope_bound {d : Nat} (y w : UnitSphere d) (v : Weight d)
    (hs : sphericalDistance w y < Real.pi) :
    |poleCostSlope y w v| ≤ sphericalDistance w y * norm v := by
  simpa only [poleCostSlope, poleGradient_norm y w hs] using
    abs_real_inner_le_norm (poleGradient y w) v

theorem poleCostSlope_tangent_formula {d : Nat} (y w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) :
    poleCostSlope y w v = -(inner Real y.val v)/Real.sinc (sphericalDistance w y) := by
  simp only [poleCostSlope, poleGradient, real_inner_smul_left, inner_sub_left, hv,
    mul_zero, zero_sub, div_eq_mul_inv]
  ring

theorem shortArcUnit_inner_tangent {d : Nat} (y w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) :
    inner Real (shortArcUnit w y) v =
      inner Real y.val v/Real.sin (sphericalDistance w y) := by
  simp only [shortArcUnit, real_inner_smul_left, inner_sub_left, hv,
    mul_zero, sub_zero, div_eq_mul_inv]
  ring

/-- The formula used for the arccos chain rule away from the pole. -/
theorem poleHessian_tangent_formula {d : Nat} (y w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (hr : 0 < sphericalDistance w y) :
    poleHessian y w v =
      (sphericalDistance w y*Real.cos (sphericalDistance w y)/Real.sin (sphericalDistance w y)) * (norm v)^2 +
      (1-sphericalDistance w y*Real.cos (sphericalDistance w y)/Real.sin (sphericalDistance w y)) *
        (inner Real y.val v/Real.sin (sphericalDistance w y))^2 := by
  rw [poleHessian, sphericalRadialWeight_formula hr.ne', shortArcUnit_inner_tangent y w v hv]

/-- Original compact-cap lower coefficient and sharp upper coefficient 1.
No positivity hypothesis on the Hessian is taken as input. -/
theorem poleHessian_bounds {d : Nat} (y w : UnitSphere d) (v : Weight d)
    {R : Real} (hrR : sphericalDistance w y ≤ R) (hR : R < Real.pi/2) :
    sphericalRadialWeight R*(norm v)^2 ≤ poleHessian y w v ∧
      poleHessian y w v ≤ (norm v)^2 := by
  have hb := sphericalRadialWeight_bounds (sphericalDistance_nonneg w y) hrR hR
  have h01 : 0 ≤ 1-sphericalRadialWeight (sphericalDistance w y) := sub_nonneg.mpr hb.2.2
  have hk : (inner Real (shortArcUnit w y) v)^2 ≤ (norm v)^2 := by
    by_cases h : y = w
    · subst y
      simp [shortArcUnit]
    · have hr := sphericalDistance_pos_of_ne w y h
      have hs : sphericalDistance w y < Real.pi := by linarith [Real.pi_pos]
      have hi := abs_real_inner_le_norm (shortArcUnit w y) v
      rw [shortArcUnit_norm w y hr hs, one_mul] at hi
      have hh := abs_le.mp hi
      nlinarith
  constructor
  · unfold poleHessian
    exact (mul_le_mul_of_nonneg_right hb.2.1 (sq_nonneg _)).trans
      (le_add_of_nonneg_right (mul_nonneg h01 (sq_nonneg _)))
  · unfold poleHessian
    calc
      _ ≤ sphericalRadialWeight (sphericalDistance w y)*(norm v)^2 +
        (1-sphericalRadialWeight (sphericalDistance w y))*(norm v)^2 :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hk h01)
      _ = _ := by ring

theorem poleHessian_abs_bound {d : Nat} (y w : UnitSphere d) (v : Weight d)
    (hs : sphericalDistance w y < Real.pi/2) :
    |poleHessian y w v| ≤ (norm v)^2 := by
  have hb := poleHessian_bounds y w v le_rfl hs
  have hpos := sphericalRadialWeight_pos (sphericalDistance_nonneg w y) hs
  have hn := (mul_nonneg hpos.le (sq_nonneg (norm v))).trans hb.1
  simpa only [abs_of_nonneg hn] using hb.2

end PaperFormalization.MatrixFactorization
