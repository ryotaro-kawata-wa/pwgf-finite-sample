import PaperFormalization.MatrixFactorization.SphericalRegularizerFlat

/-! # MF03: fixed-pole contraction and the original assigned-cost derivatives

MF03 checkpoint candidate; see MF03_VALIDATION.md for execution status.
This closes the geometric connection between the source
contraction velocity, the outward half-cost gradient, and the negative LOG.
All identities refer to the same MF02 EXP and angular distance. No connecting
WGF trajectory or finite-particle curvature is asserted.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def poleContraction {d : Nat} (y w : UnitSphere d)
    (hs : sphericalDistance y w < Real.pi) (s : Real) : UnitSphere d :=
  geodesicPoint y (sphericalLog y w hs) (sphericalLog_tangent y w hs) s

@[simp] theorem poleContraction_zero {d : Nat} (y w : UnitSphere d)
    (hs : sphericalDistance y w < Real.pi) : poleContraction y w hs 0 = y := by
  exact geodesicPoint_zero _ _ _

@[simp] theorem poleContraction_one {d : Nat} (y w : UnitSphere d)
    (hs : sphericalDistance y w < Real.pi) : poleContraction y w hs 1 = w := by
  unfold poleContraction geodesicPoint
  simpa only [one_smul] using sphericalExp_log y w hs

@[simp] theorem poleContraction_self {d : Nat} (y : UnitSphere d)
    (hs : sphericalDistance y y < Real.pi) (s : Real) : poleContraction y y hs s = y := by
  simp [poleContraction]

/-- Exact contraction of the ANGULAR distance on the full segment 0<=s<=1. -/
theorem poleContraction_distance {d : Nat} (y w : UnitSphere d)
    (hs : sphericalDistance y w < Real.pi) {s : Real} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    sphericalDistance (poleContraction y w hs s) y = s*sphericalDistance y w := by
  have hn : norm (s • sphericalLog y w hs) = s*sphericalDistance y w := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0, sphericalLog_norm]
  have hl : norm (s • sphericalLog y w hs) < Real.pi := by
    rw [hn]
    exact (mul_le_of_le_one_left (sphericalDistance_nonneg y w) hs1).trans_lt hs
  rw [sphericalDistance_comm]
  change sphericalDistance y (sphericalExp y (s • sphericalLog y w hs)
    (by rw [inner_smul_right, sphericalLog_tangent, mul_zero])) = _
  rw [sphericalDistance_exp _ _ _ hl,hn]

/-- Pole contraction remains in its ORIGINAL open cap, endpoints included. -/
theorem poleContraction_mem_cap {d : Nat} (y w : UnitSphere d) {r : Real}
    (hr : 0 < r) (hrpi : r < Real.pi) (hw : w ∈ sphericalCap y r)
    {s : Real} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    poleContraction y w (by rw [sphericalDistance_comm]; exact hw.trans hrpi) s ∈ sphericalCap y r := by
  change sphericalDistance _ y < r
  rw [poleContraction_distance _ _ _ hs0 hs1, sphericalDistance_comm y w]
  exact (mul_le_of_le_one_left (sphericalDistance_nonneg w y) hs1).trans_lt hw

noncomputable def poleContractionVelocity {d : Nat} (y w : UnitSphere d)
    (hs : sphericalDistance y w < Real.pi) (s : Real) : Weight d :=
  sphereExpVelocity y (sphericalLog y w hs) s

theorem poleContraction_hasDerivAt {d : Nat} (y w : UnitSphere d)
    (hs : sphericalDistance y w < Real.pi) (s : Real) :
    HasDerivAt (fun t => (poleContraction y w hs t).val) (poleContractionVelocity y w hs s) s :=
  sphereExpVector_hasDerivAt y (sphericalLog y w hs) s

theorem poleContractionVelocity_hasDerivAt {d : Nat} (y w : UnitSphere d)
    (hs : sphericalDistance y w < Real.pi) (s : Real) :
    HasDerivAt (poleContractionVelocity y w hs)
      (-(sphericalDistance y w)^2 • (poleContraction y w hs s).val) s := by
  apply (sphereExpVelocity_hasDerivAt y (sphericalLog y w hs) s).congr_deriv
  simp only [sphericalLog_norm, poleContraction, geodesicPoint_val]

theorem poleContractionVelocity_norm {d : Nat} (y w : UnitSphere d)
    (hs : sphericalDistance y w < Real.pi) (s : Real) :
    norm (poleContractionVelocity y w hs s) = sphericalDistance y w := by
  rw [poleContractionVelocity,sphereExpVelocity_norm _ _ (sphericalLog_tangent y w hs),sphericalLog_norm]

/-- Ambient acceleration is radial; its actual tangent projection is zero. -/
theorem poleContraction_tangent_acceleration_zero {d : Nat} (y w : UnitSphere d)
    (hs : sphericalDistance y w < Real.pi) (s : Real) :
    let x := (poleContraction y w hs s).val
    let acc := -(sphericalDistance y w)^2 • x
    acc - (inner Real x acc) • x = 0 := by
  dsimp only
  simp only [inner_smul_right, real_inner_self_eq_norm_sq,unitSphere_norm,one_pow,mul_one,sub_self]

/-- The outward contraction velocity at the original point IS the cost gradient. -/
theorem poleContractionVelocity_one {d : Nat} (y w : UnitSphere d)
    (hs : sphericalDistance y w < Real.pi) :
    poleContractionVelocity y w hs 1 = poleGradient y w := by
  have hl : norm ((1 : Real) • sphericalLog y w hs) < Real.pi := by
    simpa only [one_smul,sphericalLog_norm] using hs
  have he := poleGradient_along_pole y (sphericalLog y w hs) (sphericalLog_tangent y w hs) hl
  change poleGradient y (poleContraction y w hs 1) =
    (1 : Real) • poleContractionVelocity y w hs 1 at he
  simpa only [poleContraction_one,one_smul] using he.symm

theorem poleContractionVelocity_eq_neg_log {d : Nat} (y w : UnitSphere d)
    (hs : sphericalDistance y w < Real.pi) :
    poleContractionVelocity y w hs 1 =
      -sphericalLog w y (by rwa [sphericalDistance_comm]) := by
  rw [poleContractionVelocity_one,poleGradient_eq_neg_log]

/-- Shortest LOG commutes with simultaneous antipodal reflection. -/
theorem sphericalLog_reflected {d : Nat} (y w : UnitSphere d)
    (hs : sphericalDistance y w < Real.pi) :
    sphericalLog (reflect y) (reflect w) (by rwa [sphericalDistance_reflect_reflect]) =
      -sphericalLog y w hs := by
  by_cases hw : w = y
  · subst w
    simp
  · have hwr : reflect w ≠ reflect y := by
      intro h
      apply hw
      simpa only [reflect_reflect] using congrArg reflect h
    simp only [sphericalLog,if_neg hwr,if_neg hw,shortArcUnit,
      sphericalDistance_reflect_reflect,reflect_val]
    ext i
    simp only [PiLp.smul_apply,PiLp.sub_apply,PiLp.neg_apply,smul_eq_mul]
    ring

theorem geodesicPoint_reflected {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (s : Real) :
    geodesicPoint (reflect w) (-v) (by simpa only [reflect_val,inner_neg_neg] using hv) s =
      reflect (geodesicPoint w v hv s) := by
  apply Subtype.ext
  simp only [geodesicPoint_val,reflect_val,smul_neg,sphereExpVector_reflect]

/-- With the reflected pole this is exactly C_s(-w)=-C_s(w). The assigned-pole
version follows from the existing assignedPole_reflect_on_caps, not at a tie. -/
theorem poleContraction_reflected {d : Nat} (y w : UnitSphere d)
    (hs : sphericalDistance y w < Real.pi) (s : Real) :
    poleContraction (reflect y) (reflect w) (by rwa [sphericalDistance_reflect_reflect]) s =
      reflect (poleContraction y w hs s) := by
  apply Subtype.ext
  simp only [poleContraction, geodesicPoint_val, reflect_val]
  rw [sphericalLog_reflected y w hs, smul_neg, sphereExpVector_reflect]

/-- The frozen-pole cost equals the original assigned cost locally at any
point in the two caps. This is pointwise geometry, not a new support premise. -/
theorem assignedCost_eventually_poleCost {d : Nat} (a w : UnitSphere d) (r : Real)
    (hr : r < Real.pi/2) (hw : w ∈ sphericalCap a r ∪ sphericalCap (reflect a) r)
    (v : Weight d) (hv : inner Real w.val v = 0) :
    (fun t => assignedCost a (geodesicPoint w v hv t)) =ᶠ[𝓝 (0 : Real)]
      (fun t => poleCost (assignedPole a w) (geodesicPoint w v hv t)) := by
  have hc := geodesicPoint_continuous w v hv
  rcases hw with hp | hn
  · have hnear : ∀ᶠ t in 𝓝 (0 : Real), geodesicPoint w v hv t ∈ sphericalCap a r :=
      hc.continuousAt.eventually
        ((sphericalCap_isOpen a r).mem_nhds (by simpa only [geodesicPoint_zero] using hp))
    filter_upwards [hnear] with t ht
    simp only [assignedCost,poleCost,assignedPole_positive a r hr hp,
      assignedPole_positive a r hr ht]
  · have hnear : ∀ᶠ t in 𝓝 (0 : Real), geodesicPoint w v hv t ∈ sphericalCap (reflect a) r :=
      hc.continuousAt.eventually
        ((sphericalCap_isOpen (reflect a) r).mem_nhds (by simpa only [geodesicPoint_zero] using hn))
    filter_upwards [hnear] with t ht
    simp only [assignedCost,poleCost,assignedPole_negative a r hr hn,
      assignedPole_negative a r hr ht]

/-- Tangent gradient and Hessian identified with the ORIGINAL c_star on its
whole cap domain, including both poles. No derivative formula is a premise. -/
theorem assignedCost_exp_variations {d : Nat} (a w : UnitSphere d) (r : Real)
    (hr : r < Real.pi/2) (hw : w ∈ sphericalCap a r ∪ sphericalCap (reflect a) r)
    (v : Weight d) (hv : inner Real w.val v = 0) :
    HasDerivAt (fun t => assignedCost a (geodesicPoint w v hv t))
      (inner Real (assignedGradient a w) v) 0 ∧
    HasDerivAt (deriv (fun t => assignedCost a (geodesicPoint w v hv t)))
      (assignedHessian a w v) 0 := by
  have hs : sphericalDistance w (assignedPole a w) < Real.pi := by
    have hh := assignedPole_distance_lt_cap a r hr hw
    linarith [Real.pi_pos]
  have he := assignedCost_eventually_poleCost a w r hr hw v hv
  exact ⟨(poleCost_hasDerivAt_zero (assignedPole a w) w v hv hs).congr_of_eventuallyEq he,
    (poleCost_second_derivative (assignedPole a w) w v hv hs).congr_of_eventuallyEq he.deriv⟩

end PaperFormalization.MatrixFactorization
