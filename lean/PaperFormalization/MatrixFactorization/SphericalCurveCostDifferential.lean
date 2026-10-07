import PaperFormalization.MatrixFactorization.SphericalCostDifferential

/-! # Cost derivatives along arbitrary differentiable sphere curves

Tangency follows from the original unit-sphere constraint. The curve is not
assumed to be an exponential path. This module treats positive distance below
pi; the separate pole argument supplies the removable endpoint of the cost.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The ambient derivative of an actual sphere curve is tangent automatically. -/
theorem sphereCurve_derivative_tangent {d : Nat} (w : Real → UnitSphere d)
    (v : Weight d) (t : Real) (hw : HasDerivAt (fun s => (w s).val) v t) :
    inner Real (w t).val v = 0 := by
  have hd := hw.inner Real hw
  have hc : HasDerivAt (fun s => inner Real (w s).val (w s).val) 0 t := by
    simpa only [real_inner_self_eq_norm_sq, unitSphere_norm, one_pow] using
      hasDerivAt_const t (1 : Real)
  have hh := hd.unique hc
  nlinarith [real_inner_comm v (w t).val]

/-- The arccos chain rule is used only away from its two singular endpoints. -/
theorem poleAngle_curve_hasDerivAt_nonpole {d : Nat} (y : UnitSphere d)
    (w : Real → UnitSphere d) (v : Weight d) (t : Real)
    (hw : HasDerivAt (fun s => (w s).val) v t)
    (hr : 0 < sphericalDistance (w t) y) (hs : sphericalDistance (w t) y < Real.pi) :
    HasDerivAt (fun s => sphericalDistance (w s) y)
      (-inner Real y.val v/Real.sin (sphericalDistance (w t) y)) t := by
  have hm : inner Real (w t).val y.val ≠ -1 := by
    intro h
    have hh : sphericalDistance (w t) y = Real.pi := by simp [sphericalDistance,h]
    linarith
  have hp : inner Real (w t).val y.val ≠ 1 := by
    intro h
    have hh : sphericalDistance (w t) y = 0 := by simp [sphericalDistance,h]
    linarith
  have hi := hw.inner Real (hasDerivAt_const t y.val)
  have hd := (Real.hasDerivAt_arccos hm hp).comp t hi
  apply hd.congr_deriv
  rw [← Real.sin_arccos]
  change -(1/Real.sin (sphericalDistance (w t) y))*
    (inner Real (w t).val 0+inner Real v y.val) = _
  rw [inner_zero_right, zero_add, real_inner_comm v y.val]
  ring

/-- The gradient pairing is the derivative of the actual cost along any sphere curve. -/
theorem poleCost_curve_hasDerivAt_nonpole {d : Nat} (y : UnitSphere d)
    (w : Real → UnitSphere d) (v : Weight d) (t : Real)
    (hw : HasDerivAt (fun s => (w s).val) v t)
    (hr : 0 < sphericalDistance (w t) y) (hs : sphericalDistance (w t) y < Real.pi) :
    HasDerivAt (fun s => poleCost y (w s))
      (inner Real (poleGradient y (w t)) v) t := by
  have hv := sphereCurve_derivative_tangent w v t hw
  have hd := ((poleAngle_curve_hasDerivAt_nonpole y w v t hw hr hs).pow 2).div_const 2
  change HasDerivAt _ (poleCostSlope y (w t) v) t
  apply hd.congr_deriv
  rw [poleCostSlope_tangent_formula y (w t) v hv, Real.sinc_of_ne_zero hr.ne']
  simp only [Nat.cast_ofNat]
  field_simp [(Real.sin_pos_of_pos_of_lt_pi hr hs).ne', hr.ne']
  ring

end PaperFormalization.MatrixFactorization
