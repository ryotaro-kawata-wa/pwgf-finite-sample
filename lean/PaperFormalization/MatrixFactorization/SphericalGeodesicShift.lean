import PaperFormalization.MatrixFactorization.SphericalLogarithm

/-! # MF03: re-centering the same spherical EXP curve

MF03 checkpoint candidate; see MF03_VALIDATION.md for execution status.
The identities in this file concern the actual MF02
EXP and its actual velocity. They allow a pointwise calculation at time zero
to be used at every time in one common integration interval. No geodesic,
ODE, or re-centering identity is added as a model hypothesis.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def geodesicPoint {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t : Real) : UnitSphere d :=
  sphericalExp w (t • v) (by rw [inner_smul_right, hv, mul_zero])

@[simp] theorem geodesicPoint_val {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t : Real) :
    (geodesicPoint w v hv t).val = sphereExpVector w (t • v) := rfl

@[simp] theorem geodesicPoint_zero {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) : geodesicPoint w v hv 0 = w := by
  apply Subtype.ext
  simp [geodesicPoint]

@[simp] theorem geodesicPoint_zero_velocity {d : Nat} (w : UnitSphere d)
    (hv : inner Real w.val (0 : Weight d) = 0) (t : Real) :
    geodesicPoint w 0 hv t = w := by
  apply Subtype.ext
  simp [geodesicPoint]

theorem geodesicPoint_continuous {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) : Continuous (geodesicPoint w v hv) := by
  exact ((sphereExpVector_continuous d).comp
    (continuous_const.prodMk (continuous_id.smul continuous_const))).subtype_mk _

/-- The velocity at any time is tangent at the actual point at that time. -/
theorem geodesicVelocity_tangent {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t : Real) :
    inner Real (geodesicPoint w v hv t).val (sphereExpVelocity w v t) = 0 := by
  by_cases hz : v = 0
  · subst v
    simp [sphereExpVelocity]
  · rw [geodesicPoint_val, sphereExpVector_scaled w v hz t]
    have hr : norm v ≠ 0 := norm_ne_zero_iff.mpr hz
    have hv' : inner Real v w.val = 0 := by rw [real_inner_comm, hv]
    simp only [sphereExpVelocity, inner_add_left, inner_add_right,
      real_inner_smul_left, inner_smul_right, hv, hv',
      real_inner_self_eq_norm_sq, unitSphere_norm, one_pow]
    field_simp [hr]
    ring

/-- Time translation of EXP. This is an exact identity for all signed s,t. -/
theorem geodesicPoint_shift {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t s : Real) :
    geodesicPoint (geodesicPoint w v hv t) (sphereExpVelocity w v t)
      (geodesicVelocity_tangent w v hv t) s = geodesicPoint w v hv (t+s) := by
  by_cases hz : v = 0
  · subst v
    apply Subtype.ext
    simp [geodesicPoint, sphereExpVelocity]
  · have hr : norm v ≠ 0 := norm_ne_zero_iff.mpr hz
    have hs : sphereExpVelocity w v t ≠ 0 := by
      intro h
      have hh := sphereExpVelocity_norm w v hv t
      rw [h, norm_zero] at hh
      exact hr hh.symm
    apply Subtype.ext
    rw [geodesicPoint_val, sphereExpVector_scaled _ _ hs s,
      sphereExpVelocity_norm w v hv t, geodesicPoint_val,
      sphereExpVector_scaled w v hz t, geodesicPoint_val,
      sphereExpVector_scaled w v hz (t+s)]
    ext i
    simp only [sphereExpVelocity, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, add_mul, Real.sin_add, Real.cos_add]
    field_simp [hr]
    ring

/-- The velocity is translated along with the curve, rather than reset. -/
theorem geodesicVelocity_shift {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t s : Real) :
    sphereExpVelocity (geodesicPoint w v hv t) (sphereExpVelocity w v t) s =
      sphereExpVelocity w v (t+s) := by
  by_cases hz : v = 0
  · subst v
    simp [sphereExpVelocity]
  · have hr : norm v ≠ 0 := norm_ne_zero_iff.mpr hz
    rw [sphereExpVelocity, sphereExpVelocity_norm w v hv t,
      geodesicPoint_val, sphereExpVector_scaled w v hz t]
    ext i
    simp only [sphereExpVelocity, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, add_mul, Real.sin_add, Real.cos_add]
    field_simp [hr]
    ring

/-- Returning for time -t returns to the same initial point. -/
theorem geodesicPoint_return {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t : Real) :
    geodesicPoint (geodesicPoint w v hv t) (sphereExpVelocity w v t)
      (geodesicVelocity_tangent w v hv t) (-t) = w := by
  rw [geodesicPoint_shift, add_neg_cancel, geodesicPoint_zero]

/-- Translation adapter used twice for the cost and its first variation. -/
theorem hasDerivAt_from_time_shift {f : Real → Real} {t c : Real}
    (h : HasDerivAt (fun s => f (t+s)) c 0) : HasDerivAt f c t := by
  have h0 : HasDerivAt (fun s => f (t+s)) c (t-t) := by simpa using h
  have h' := h0.comp (h := fun x : Real => x-t) t ((hasDerivAt_id t).sub_const t)
  have he : ((fun s => f (t+s)) ∘ fun x : Real => x-t) = f := by
    funext x
    simp only [Function.comp_apply]
    congr 1
    ring
  simpa only [he, mul_one] using h'

end PaperFormalization.MatrixFactorization
