import PaperFormalization.MatrixFactorization.SphericalCostGeometry

/-! # MF03: actual first and second cost derivatives along spherical EXP

MF03 checkpoint candidate; see MF03_VALIDATION.md for execution status.
At a pole, the half-cost is exactly a quadratic in signed
time, although the unsquared distance is not differentiable there. Away from
a pole the arccos chain rule applies. Exact time translation supplies both
identities at all times; the final lemma identifies the literal iterated deriv.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The angle derivative is deliberately restricted away from BOTH endpoints. -/
theorem poleAngle_hasDerivAt_zero {d : Nat} (y w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0)
    (hr : 0 < sphericalDistance w y) (hs : sphericalDistance w y < Real.pi) :
    HasDerivAt (fun t => sphericalDistance (geodesicPoint w v hv t) y)
      (-inner Real y.val v/Real.sin (sphericalDistance w y)) 0 := by
  have hm : inner Real w.val y.val ≠ -1 := by
    intro h
    have hh : sphericalDistance w y = Real.pi := by simp [sphericalDistance,h]
    linarith
  have hp : inner Real w.val y.val ≠ 1 := by
    intro h
    have hh : sphericalDistance w y = 0 := by simp [sphericalDistance,h]
    linarith
  have hi : HasDerivAt
      (fun t => inner Real (geodesicPoint w v hv t).val y.val)
      (inner Real v y.val) 0 := by
    simpa only [geodesicPoint_val, sphereExpVelocity_at_zero,
      inner_zero_right, zero_add] using
      (sphereExpVector_hasDerivAt w v 0).inner Real (hasDerivAt_const (0 : Real) y.val)
  have hd := (Real.hasDerivAt_arccos hm hp).comp_of_eq 0 hi (by simp)
  apply hd.congr_deriv
  rw [← Real.sin_arccos]
  change -(1/Real.sin (sphericalDistance w y))*inner Real v y.val = _
  rw [real_inner_comm v y.val]
  ring

/-- On a short arc starting at its pole the half-cost is EXACTLY quadratic. -/
theorem poleCost_along_pole {d : Nat} (y : UnitSphere d) (v : Weight d)
    (hv : inner Real y.val v = 0) {t : Real} (ht : norm (t • v) < Real.pi) :
    poleCost y (geodesicPoint y v hv t) = t^2*(norm v)^2/2 := by
  rw [poleCost, sphericalDistance_comm]
  change (sphericalDistance y
    (sphericalExp y (t • v) (by rw [inner_smul_right,hv,mul_zero])))^2/2 = _
  rw [sphericalDistance_exp _ _ _ ht, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

/-- All tangent directions, including v=0, and the pole case are included. -/
theorem poleCost_hasDerivAt_zero {d : Nat} (y w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (hs : sphericalDistance w y < Real.pi) :
    HasDerivAt (fun t => poleCost y (geodesicPoint w v hv t))
      (poleCostSlope y w v) 0 := by
  by_cases h : w = y
  · subst w
    have ht : ∀ᶠ t in 𝓝 (0 : Real), norm (t • v) < Real.pi := by
      have hc : Continuous (fun t : Real => norm (t • v)) := by fun_prop
      exact hc.continuousAt.eventually (gt_mem_nhds (by simpa using Real.pi_pos))
    have he : (fun t => t^2*(norm v)^2/2) =ᶠ[𝓝 (0 : Real)]
        (fun t => poleCost y (geodesicPoint y v hv t)) := by
      filter_upwards [ht] with t ht
      exact (poleCost_along_pole y v hv ht).symm
    have hd : HasDerivAt (fun t : Real => t^2*(norm v)^2/2) 0 0 := by
      simpa using (((hasDerivAt_id (0 : Real)).pow 2).mul_const ((norm v)^2)).div_const 2
    simpa only [poleCostSlope_self] using hd.congr_of_eventuallyEq he.symm
  · have hr := sphericalDistance_pos_of_ne w y (Ne.symm h)
    have hd := ((poleAngle_hasDerivAt_zero y w v hv hr hs).pow 2).div_const 2
    apply hd.congr_deriv
    rw [poleCostSlope_tangent_formula y w v hv, Real.sinc_of_ne_zero hr.ne']
    simp only [geodesicPoint_zero, Nat.cast_ofNat]
    field_simp [(Real.sin_pos_of_pos_of_lt_pi hr hs).ne',hr.ne']
    ring

/-- The first derivative at an arbitrary time uses the same moving velocity. -/
theorem poleCost_hasDerivAt {d : Nat} (y w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t : Real)
    (hs : sphericalDistance (geodesicPoint w v hv t) y < Real.pi) :
    HasDerivAt (fun s => poleCost y (geodesicPoint w v hv s))
      (poleCostSlope y (geodesicPoint w v hv t) (sphereExpVelocity w v t)) t := by
  apply hasDerivAt_from_time_shift
  simpa only [geodesicPoint_shift] using
    poleCost_hasDerivAt_zero y (geodesicPoint w v hv t) (sphereExpVelocity w v t)
      (geodesicVelocity_tangent w v hv t) hs

/-- Along a short arc from the pole, grad(cost)=t*velocity, for signed time. -/
theorem poleGradient_along_pole {d : Nat} (y : UnitSphere d) (v : Weight d)
    (hv : inner Real y.val v = 0) {t : Real} (ht : norm (t • v) < Real.pi) :
    poleGradient y (geodesicPoint y v hv t) = t • sphereExpVelocity y v t := by
  have hs : sphericalDistance (geodesicPoint y v hv t) y < Real.pi := by
    rw [sphericalDistance_comm]
    exact (sphericalDistance_exp y (t • v) _ ht).trans_lt ht
  have htan : inner Real (geodesicPoint y v hv t).val
      ((-t) • sphereExpVelocity y v t) = 0 := by
    rw [inner_smul_right, geodesicVelocity_tangent, mul_zero]
  have hlen : norm ((-t) • sphereExpVelocity y v t) < Real.pi := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_neg,
      sphereExpVelocity_norm y v hv t] using ht
  have he : sphericalExp (geodesicPoint y v hv t)
      ((-t) • sphereExpVelocity y v t) htan = y :=
    geodesicPoint_return y v hv t
  have hl := sphericalLog_exp (geodesicPoint y v hv t)
    ((-t) • sphereExpVelocity y v t) htan hlen
  have hl' : sphericalLog (geodesicPoint y v hv t) y hs =
      (-t) • sphereExpVelocity y v t := by simpa only [he] using hl
  rw [poleGradient_eq_neg_log y (geodesicPoint y v hv t) hs, hl']
  simp

/-- The gradient pairing has its correct second derivative at a pole. -/
theorem poleCostSlope_hasDerivAt_pole {d : Nat} (y : UnitSphere d) (v : Weight d)
    (hv : inner Real y.val v = 0) :
    HasDerivAt (fun t => poleCostSlope y (geodesicPoint y v hv t) (sphereExpVelocity y v t))
      ((norm v)^2) 0 := by
  have ht : ∀ᶠ t in 𝓝 (0 : Real), norm (t • v) < Real.pi := by
    have hc : Continuous (fun t : Real => norm (t • v)) := by fun_prop
    exact hc.continuousAt.eventually (gt_mem_nhds (by simpa using Real.pi_pos))
  have he : (fun t : Real => t*(norm v)^2) =ᶠ[𝓝 (0 : Real)]
      (fun t => poleCostSlope y (geodesicPoint y v hv t) (sphereExpVelocity y v t)) := by
    filter_upwards [ht] with t ht
    rw [poleCostSlope, poleGradient_along_pole y v hv ht,
      real_inner_smul_left, real_inner_self_eq_norm_sq, sphereExpVelocity_norm y v hv t]
  simpa only [one_mul] using ((hasDerivAt_id (0 : Real)).mul_const ((norm v)^2)).congr_of_eventuallyEq he.symm

/-- Away from a pole both scalar quotients are ordinary differentiable functions. -/
theorem poleCostSlope_hasDerivAt_nonpole {d : Nat} (y w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0)
    (hr : 0 < sphericalDistance w y) (hs : sphericalDistance w y < Real.pi) :
    HasDerivAt (fun t => poleCostSlope y (geodesicPoint w v hv t) (sphereExpVelocity w v t))
      (poleHessian y w v) 0 := by
  let r := fun t => sphericalDistance (geodesicPoint w v hv t) y
  let k := fun t => inner Real y.val (sphereExpVelocity w v t)
  have hsin := Real.sin_pos_of_pos_of_lt_pi hr hs
  have dr : HasDerivAt r (-inner Real y.val v/Real.sin (sphericalDistance w y)) 0 :=
    poleAngle_hasDerivAt_zero y w v hv hr hs
  have dk : HasDerivAt k (-(norm v)^2*Real.cos (sphericalDistance w y)) 0 := by
    have hd := (hasDerivAt_const (0 : Real) y.val).inner Real
      (sphereExpVelocity_hasDerivAt w v 0)
    apply hd.congr_deriv
    simp only [zero_smul, sphereExpVector_zero, inner_zero_left, add_zero,
      inner_smul_right, cos_sphericalDistance, real_inner_comm]
  have hn : Real.sin (r 0) ≠ 0 := by simpa only [r,geodesicPoint_zero] using hsin.ne'
  have hd := ((dr.mul dk).neg).div dr.sin hn
  have hd' : HasDerivAt (fun t => -(r t*k t)/Real.sin (r t)) (poleHessian y w v) 0 := by
    apply hd.congr_deriv
    simp only [Pi.neg_apply, Pi.mul_apply, r,k,geodesicPoint_zero,sphereExpVelocity_at_zero]
    rw [poleHessian_tangent_formula y w v hv hr]
    field_simp [hsin.ne']
    ring
  have hc : Continuous r := by
    have hg : Continuous (fun t => (geodesicPoint w v hv t).val) :=
      continuous_subtype_val.comp (geodesicPoint_continuous w v hv)
    exact Real.continuous_arccos.comp (hg.inner continuous_const)
  have he : ∀ᶠ t in 𝓝 (0 : Real), r t ∈ Ioo 0 Real.pi := by
    exact hc.continuousAt.eventually (Ioo_mem_nhds (by simpa [r] using hr) (by simpa [r] using hs))
  apply hd'.congr_of_eventuallyEq
  filter_upwards [he] with t ht
  rw [poleCostSlope_tangent_formula y (geodesicPoint w v hv t)
    (sphereExpVelocity w v t) (geodesicVelocity_tangent w v hv t),
    Real.sinc_of_ne_zero ht.1.ne']
  change -(k t)/(Real.sin (r t)/r t) = -(r t*k t)/Real.sin (r t)
  field_simp [ht.1.ne', (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne']

/-- The Hessian is obtained from the actual EXP derivative, including the pole. -/
theorem poleCostSlope_hasDerivAt_zero {d : Nat} (y w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (hs : sphericalDistance w y < Real.pi) :
    HasDerivAt (fun t => poleCostSlope y (geodesicPoint w v hv t) (sphereExpVelocity w v t))
      (poleHessian y w v) 0 := by
  by_cases h : w = y
  · subst w
    simpa only [poleHessian_self] using poleCostSlope_hasDerivAt_pole y v hv
  · exact poleCostSlope_hasDerivAt_nonpole y w v hv
      (sphericalDistance_pos_of_ne w y (Ne.symm h)) hs

theorem poleCostSlope_hasDerivAt {d : Nat} (y w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t : Real)
    (hs : sphericalDistance (geodesicPoint w v hv t) y < Real.pi) :
    HasDerivAt (fun s => poleCostSlope y (geodesicPoint w v hv s) (sphereExpVelocity w v s))
      (poleHessian y (geodesicPoint w v hv t) (sphereExpVelocity w v t)) t := by
  apply hasDerivAt_from_time_shift
  simpa only [geodesicPoint_shift,geodesicVelocity_shift] using
    poleCostSlope_hasDerivAt_zero y (geodesicPoint w v hv t) (sphereExpVelocity w v t)
      (geodesicVelocity_tangent w v hv t) hs

/-- The literal second derivative, not just a named quadratic-form surrogate. -/
theorem poleCost_second_derivative {d : Nat} (y w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (hs : sphericalDistance w y < Real.pi) :
    HasDerivAt (deriv (fun t => poleCost y (geodesicPoint w v hv t)))
      (poleHessian y w v) 0 := by
  have he : (fun t => poleCostSlope y (geodesicPoint w v hv t) (sphereExpVelocity w v t))
      =ᶠ[𝓝 (0 : Real)] (deriv (fun t => poleCost y (geodesicPoint w v hv t))) := by
    have hc : Continuous (fun t => sphericalDistance (geodesicPoint w v hv t) y) := by
      have hg : Continuous (fun t => (geodesicPoint w v hv t).val) :=
        continuous_subtype_val.comp (geodesicPoint_continuous w v hv)
      exact Real.continuous_arccos.comp (hg.inner continuous_const)
    have hn : ∀ᶠ t in 𝓝 (0 : Real),
        sphericalDistance (geodesicPoint w v hv t) y < Real.pi :=
      hc.continuousAt.eventually (gt_mem_nhds (by simpa only [geodesicPoint_zero] using hs))
    filter_upwards [hn] with t ht
    exact (poleCost_hasDerivAt y w v hv t ht).deriv.symm
  exact (poleCostSlope_hasDerivAt_zero y w v hv hs).congr_of_eventuallyEq he.symm

end PaperFormalization.MatrixFactorization
