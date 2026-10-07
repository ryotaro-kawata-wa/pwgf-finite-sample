import PaperFormalization.MatrixFactorization.SphericalRetraction

/-! # All-time differential bounds for the original normalized retraction

The path remains the literal normalization of `w+t*v`. The rational slope
below is derived from that path and supplies global signed-time bounds, with
no cutoff on the original continuous tangent field.
-/
open MeasureTheory Set Filter Asymptotics
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def retractionSlope (q t : Real) : Real := q*t/(1+t^2*q)

theorem retractionSlope_hasDerivAt {q : Real} (hq : 0 ≤ q) (t : Real) :
    HasDerivAt (retractionSlope q)
      (q/(1+t^2*q)^2-(retractionSlope q t)^2) t := by
  have hD : 0 < 1+t^2*q := by positivity
  have hd := ((hasDerivAt_id t).const_mul q).div
    ((((hasDerivAt_id t).pow 2).mul_const q).const_add 1) hD.ne'
  apply hd.congr_deriv
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, retractionSlope]
  field_simp
  ring

theorem retractionScaleFirst_eq_slope {q : Real} (hq : 0 ≤ q) (t : Real) :
    retractionScaleFirst q t = -retractionSlope q t*retractionScale q t := by
  have hD : 0 < 1+t^2*q := by positivity
  unfold retractionScaleFirst retractionScale retractionSlope
  rw [show (-3/2 : Real) = (-1/2 : Real)-1 by norm_num,
    Real.rpow_sub hD, Real.rpow_one]
  ring

theorem sphericalRetractVelocity_eq_slope {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t : Real) :
    sphericalRetractVelocity w v t =
      retractionScale (norm v^2) t • v - retractionSlope (norm v^2) t • sphericalRetractVector w v t := by
  rw [sphericalRetractVelocity, sphericalRetractVector_scale w v hv,
    retractionScaleFirst_eq_slope (sq_nonneg (norm v))]
  module

noncomputable def sphericalRetractAcceleration {d : Nat} (w : UnitSphere d)
    (v : Weight d) (t : Real) : Weight d :=
  -(norm v^2/(1+t^2*norm v^2)^2) • sphericalRetractVector w v t -
    (2*retractionSlope (norm v^2) t) • sphericalRetractVelocity w v t

/-- The derivative is proved at every signed time, including zero velocity. -/
theorem sphericalRetractVelocity_hasDerivAt {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t : Real) :
    HasDerivAt (sphericalRetractVelocity w v) (sphericalRetractAcceleration w v t) t := by
  have he : sphericalRetractVelocity w v = fun s =>
      retractionScale (norm v^2) s • v -
        retractionSlope (norm v^2) s • sphericalRetractVector w v s :=
    funext (sphericalRetractVelocity_eq_slope w v hv)
  rw [he]
  have hd := ((retractionScale_hasDerivAt (sq_nonneg (norm v)) t).smul_const v).sub
    ((retractionSlope_hasDerivAt (sq_nonneg (norm v)) t).smul
      (sphericalRetractVector_hasDerivAt w v hv t))
  apply hd.congr_deriv
  rw [retractionScaleFirst_eq_slope (sq_nonneg (norm v))]
  rw [sphericalRetractAcceleration, sphericalRetractVelocity_eq_slope w v hv]
  module

@[simp] theorem sphericalRetractAcceleration_zero {d : Nat} (w : UnitSphere d) (v : Weight d) :
    sphericalRetractAcceleration w v 0 = -(norm v^2) • w.val := by
  simp [sphericalRetractAcceleration, retractionSlope]

theorem retractionScale_nonneg {q : Real} (hq : 0 ≤ q) (t : Real) :
    0 ≤ retractionScale q t := Real.rpow_nonneg (by positivity) _

theorem retractionScale_le_one {q : Real} (hq : 0 ≤ q) (t : Real) :
    retractionScale q t ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [mul_nonneg (sq_nonneg t) hq]) (by norm_num)

/-- The rational angular slope is bounded by the original tangent speed. -/
theorem retractionSlope_norm_le {d : Nat} (v : Weight d) (t : Real) :
    abs (retractionSlope (norm v^2) t) ≤ norm v := by
  have hD : 0 < 1+t^2*norm v^2 := by positivity
  have ht : abs t*norm v ≤ 1+t^2*norm v^2 := by
    have hs := sq_nonneg (abs t*norm v-1)
    have ha := sq_abs t
    nlinarith [norm_nonneg v]
  rw [retractionSlope, abs_div, abs_mul, abs_pow, abs_of_nonneg (norm_nonneg v), abs_of_pos hD]
  apply (div_le_iff₀ hD).mpr
  nlinarith [mul_le_mul_of_nonneg_left ht (norm_nonneg v)]

theorem sphericalRetractVelocity_norm_le {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t : Real) : norm (sphericalRetractVelocity w v t) ≤ 2*norm v := by
  rw [sphericalRetractVelocity_eq_slope w v hv]
  calc
    _ ≤ norm (retractionScale (norm v^2) t • v) +
        norm (retractionSlope (norm v^2) t • sphericalRetractVector w v t) := norm_sub_le _ _
    _ = retractionScale (norm v^2) t*norm v + abs (retractionSlope (norm v^2) t) := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (retractionScale_nonneg (sq_nonneg (norm v)) t),
        sphericalRetractVector_norm w v hv t, mul_one]
    _ ≤ 2*norm v := by
      have hc := mul_le_mul_of_nonneg_right (retractionScale_le_one (sq_nonneg (norm v)) t) (norm_nonneg v)
      have hb := retractionSlope_norm_le v t
      linarith

/-- A uniform quadratic-speed envelope for the actual ambient acceleration. -/
theorem sphericalRetractAcceleration_norm_le {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t : Real) :
    norm (sphericalRetractAcceleration w v t) ≤ 6*norm v^2 := by
  have hD : 1 ≤ 1+t^2*norm v^2 := by nlinarith [mul_nonneg (sq_nonneg t) (sq_nonneg (norm v))]
  have hcoef : norm v^2/(1+t^2*norm v^2)^2 ≤ norm v^2 :=
    div_le_self (sq_nonneg (norm v)) (by nlinarith)
  rw [sphericalRetractAcceleration]
  calc
    _ ≤ norm (-(norm v^2/(1+t^2*norm v^2)^2) • sphericalRetractVector w v t) +
        norm ((2*retractionSlope (norm v^2) t) • sphericalRetractVelocity w v t) := norm_sub_le _ _
    _ = norm v^2/(1+t^2*norm v^2)^2 +
        2*abs (retractionSlope (norm v^2) t)*norm (sphericalRetractVelocity w v t) := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_neg, abs_of_nonneg (by positivity), sphericalRetractVector_norm w v hv t,
        mul_one, abs_mul]
      norm_num
    _ ≤ norm v^2 + (2*norm v)*(2*norm v) := by
      exact add_le_add hcoef (mul_le_mul
        (mul_le_mul_of_nonneg_left (retractionSlope_norm_le v t) (by norm_num))
        (sphericalRetractVelocity_norm_le w v hv t) (norm_nonneg _) (by positivity))
    _ ≤ _ := by nlinarith [sq_nonneg (norm v)]

theorem sphericalRetractVelocity_continuous {d : Nat} (v : UnitSphere d → Weight d)
    (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) :
    Continuous (fun p : Real × UnitSphere d => sphericalRetractVelocity p.2 (v p.2) p.1) := by
  have hD : Continuous (fun p : Real × UnitSphere d => 1+p.1^2*norm (v p.2)^2) := by fun_prop
  have hDn (p : Real × UnitSphere d) : 1+p.1^2*norm (v p.2)^2 ≠ 0 := by positivity
  have hscale : Continuous (fun p : Real × UnitSphere d => retractionScale (norm (v p.2)^2) p.1) :=
    hD.rpow_const (fun p => Or.inl (hDn p))
  have hslope : Continuous (fun p : Real × UnitSphere d => retractionSlope (norm (v p.2)^2) p.1) := by
    unfold retractionSlope
    exact (hc.norm.comp continuous_snd |>.pow 2 |>.mul continuous_fst).div hD hDn
  have hR := (sphericalRetractFamily_continuous v hv hc).subtype_val
  have he : (fun p : Real × UnitSphere d => sphericalRetractVelocity p.2 (v p.2) p.1) =
      (fun p => retractionScale (norm (v p.2)^2) p.1 • v p.2 -
        retractionSlope (norm (v p.2)^2) p.1 • sphericalRetractVector p.2 (v p.2) p.1) :=
    funext (fun p => sphericalRetractVelocity_eq_slope p.2 (v p.2) (hv p.2) p.1)
  rw [he]
  exact (hscale.smul (hc.comp continuous_snd)).sub (hslope.smul hR)

theorem sphericalRetractAcceleration_continuous {d : Nat} (v : UnitSphere d → Weight d)
    (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) :
    Continuous (fun p : Real × UnitSphere d => sphericalRetractAcceleration p.2 (v p.2) p.1) := by
  have hD : Continuous (fun p : Real × UnitSphere d => 1+p.1^2*norm (v p.2)^2) := by fun_prop
  have hDn (p : Real × UnitSphere d) : 1+p.1^2*norm (v p.2)^2 ≠ 0 := by positivity
  have hR := (sphericalRetractFamily_continuous v hv hc).subtype_val
  have hV := sphericalRetractVelocity_continuous v hv hc
  unfold sphericalRetractAcceleration retractionSlope
  exact (((hc.norm.comp continuous_snd).pow 2).div (hD.pow 2) (fun p => pow_ne_zero 2 (hDn p))).neg.smul hR |>.sub
    ((continuous_const.mul (((hc.norm.comp continuous_snd).pow 2).mul continuous_fst |>.div hD hDn)).smul hV)

end PaperFormalization.MatrixFactorization
