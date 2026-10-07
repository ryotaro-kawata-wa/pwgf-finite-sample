import PaperFormalization.MatrixFactorization.CapPushforward

/-! # MF03a: actual spherical EXP paths, including the zero tangent vector

The continuous sinc extension avoids differentiating norm at zero. Derivatives
are proved for the actual great-circle path by a zero/nonzero split, not for an
unrelated linear output ray. Fixed-assignment cost along the resulting EXP
pushforward follows from MF02 and compact support; cap preservation is derived.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The removable singularity identity is valid also at zero. -/
theorem spherical_sinc_mul (x : Real) : Real.sinc x * x = Real.sin x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.sinc_of_ne_zero hx]
    exact div_mul_cancel₀ _ hx

theorem spherical_sinc_abs (x : Real) : Real.sinc |x| = Real.sinc x := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, Real.sinc_neg]

noncomputable def sphereExpVector {d : Nat} (y : UnitSphere d) (v : Weight d) : Weight d :=
  Real.cos ‖v‖ • y.val + Real.sinc ‖v‖ • v

theorem sphereExpVector_continuous (d : Nat) :
    Continuous (fun z : UnitSphere d × Weight d => sphereExpVector z.1 z.2) := by
  unfold sphereExpVector
  fun_prop

@[simp] theorem sphereExpVector_zero {d : Nat} (y : UnitSphere d) :
    sphereExpVector y 0 = y.val := by simp [sphereExpVector]

/-- Tangency is the original ambient orthogonality constraint. -/
theorem sphereExpVector_norm_sq {d : Nat} (y : UnitSphere d) (v : Weight d)
    (htan : inner Real y.val v = 0) : ‖sphereExpVector y v‖^2 = 1 := by
  have he : ‖sphereExpVector y v‖^2 =
      (Real.cos ‖v‖)^2 + (Real.sinc ‖v‖ * ‖v‖)^2 := by
    simp [sphereExpVector, norm_add_sq_real, norm_smul, real_inner_smul_left,
      inner_smul_right, htan, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [he, spherical_sinc_mul]
  nlinarith [Real.sin_sq_add_cos_sq ‖v‖]

/-- Source EXP, bundled on the sphere. No inverse statement at the antipode is made. -/
noncomputable def sphericalExp {d : Nat} (y : UnitSphere d) (v : Weight d)
    (htan : inner Real y.val v = 0) : UnitSphere d :=
  ⟨sphereExpVector y v, by
    have h := sphereExpVector_norm_sq y v htan
    have hn : ‖sphereExpVector y v‖ = 1 := by nlinarith [norm_nonneg (sphereExpVector y v)]
    simpa only [Metric.mem_sphere, dist_zero_right] using hn⟩

@[simp] theorem sphericalExp_val {d : Nat} (y : UnitSphere d) (v : Weight d)
    (htan : inner Real y.val v = 0) : (sphericalExp y v htan).val = sphereExpVector y v := rfl

@[simp] theorem sphericalExp_zero {d : Nat} (y : UnitSphere d)
    (htan : inner Real y.val (0 : Weight d) = 0) : sphericalExp y 0 htan = y := by
  apply Subtype.ext
  simp

/-- Literal trigonometric source formula for a nonzero tangent vector. -/
theorem sphereExpVector_formula {d : Nat} (y : UnitSphere d) (v : Weight d) (hv : v ≠ 0) :
    sphereExpVector y v = Real.cos ‖v‖ • y.val + (Real.sin ‖v‖ / ‖v‖) • v := by
  rw [sphereExpVector, Real.sinc_of_ne_zero (norm_ne_zero_iff.mpr hv)]

/-- Exact EXP(t*v) formula for every real t, including negative t and t=0. -/
theorem sphereExpVector_scaled {d : Nat} (y : UnitSphere d) (v : Weight d)
    (hv : v ≠ 0) (t : Real) :
    sphereExpVector y (t • v) =
      Real.cos (t * ‖v‖) • y.val + (Real.sin (t * ‖v‖) / ‖v‖) • v := by
  have hr : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hn : ‖t • v‖ = |t * ‖v‖| := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg v)]
  have hcoef : Real.sinc (t * ‖v‖) * t = Real.sin (t * ‖v‖) / ‖v‖ := by
    apply (eq_div_iff hr).2
    calc
      _ = Real.sinc (t * ‖v‖) * (t * ‖v‖) := by ring
      _ = _ := spherical_sinc_mul _
  rw [sphereExpVector, hn, Real.cos_abs, spherical_sinc_abs, smul_smul, hcoef]

noncomputable def sphereExpVelocity {d : Nat} (y : UnitSphere d) (v : Weight d) (t : Real) : Weight d :=
  (-(‖v‖ * Real.sin (t * ‖v‖))) • y.val + Real.cos (t * ‖v‖) • v

@[simp] theorem sphereExpVelocity_at_zero {d : Nat} (y : UnitSphere d) (v : Weight d) :
    sphereExpVelocity y v 0 = v := by simp [sphereExpVelocity]

/-- First derivative of the ambient representative of the actual spherical EXP path. -/
theorem sphereExpVector_hasDerivAt {d : Nat} (y : UnitSphere d) (v : Weight d) (t : Real) :
    HasDerivAt (fun s : Real => sphereExpVector y (s • v)) (sphereExpVelocity y v t) t := by
  by_cases hv : v = 0
  · subst v
    simpa [sphereExpVelocity] using hasDerivAt_const t y.val
  · have hr : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have he : (fun s : Real => sphereExpVector y (s • v)) =
        (fun s : Real => Real.cos (s * ‖v‖) • y.val + (Real.sin (s * ‖v‖) / ‖v‖) • v) := by
      funext s
      exact sphereExpVector_scaled y v hv s
    rw [he]
    have hd := (((hasDerivAt_id t).mul_const ‖v‖).cos.smul_const y.val).add
      ((((hasDerivAt_id t).mul_const ‖v‖).sin.div_const ‖v‖).smul_const v)
    apply hd.congr_deriv
    ext i
    simp only [sphereExpVelocity, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, id_eq, one_mul]
    field_simp [hr]

/-- The second ambient derivative is radial: -||v||^2 EXP_y(t v). -/
theorem sphereExpVelocity_hasDerivAt {d : Nat} (y : UnitSphere d) (v : Weight d) (t : Real) :
    HasDerivAt (sphereExpVelocity y v) (-(‖v‖^2) • sphereExpVector y (t • v)) t := by
  by_cases hv : v = 0
  · subst v
    change HasDerivAt (fun s : Real => sphereExpVelocity y 0 s) _ t
    simpa [sphereExpVelocity] using hasDerivAt_const t (0 : Weight d)
  · have hr : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    unfold sphereExpVelocity
    have hd := (((((hasDerivAt_id t).mul_const ‖v‖).sin.const_mul ‖v‖).neg).smul_const y.val).add
      (((hasDerivAt_id t).mul_const ‖v‖).cos.smul_const v)
    apply hd.congr_deriv
    rw [sphereExpVector_scaled y v hv t]
    ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, id_eq, one_mul]
    field_simp [hr]
    ring

/-- Constant speed, including the stationary v=0 path. -/
theorem sphereExpVelocity_norm {d : Nat} (y : UnitSphere d) (v : Weight d)
    (htan : inner Real y.val v = 0) (t : Real) : ‖sphereExpVelocity y v t‖ = ‖v‖ := by
  have hs : ‖sphereExpVelocity y v t‖^2 = ‖v‖^2 := by
    calc
      _ = ‖v‖^2 * ((Real.sin (t * ‖v‖))^2 + (Real.cos (t * ‖v‖))^2) := by
        simp [sphereExpVelocity, norm_add_sq_real, norm_smul, real_inner_smul_left,
          inner_smul_right, htan, Real.norm_eq_abs, mul_pow, sq_abs]
        nlinarith [Real.sin_sq_add_cos_sq (t * ‖v‖)]
      _ = _ := by rw [Real.sin_sq_add_cos_sq, mul_one]
  nlinarith [norm_nonneg (sphereExpVelocity y v t), norm_nonneg v]

/-- Simultaneously reflecting base point and tangent vector reflects the EXP path. -/
theorem sphereExpVector_reflect {d : Nat} (y : UnitSphere d) (v : Weight d) :
    sphereExpVector (reflect y) (-v) = -sphereExpVector y v := by
  simp [sphereExpVector, reflect_val, smul_neg, add_comm]

noncomputable def sphericalExpFamily {d : Nat} (v : UnitSphere d → Weight d)
    (htan : ∀ w, inner Real w.val (v w) = 0) (t : Real) (w : UnitSphere d) : UnitSphere d :=
  sphericalExp w (t • v w) (by rw [inner_smul_right, htan, mul_zero])

theorem sphericalExpFamily_continuous {d : Nat} (v : UnitSphere d → Weight d)
    (htan : ∀ w, inner Real w.val (v w) = 0) (hv : Continuous v) :
    Continuous (fun z : Real × UnitSphere d => sphericalExpFamily v htan z.1 z.2) := by
  have hc : Continuous (fun z : Real × UnitSphere d => sphereExpVector z.2 (z.1 • v z.2)) := by
    unfold sphereExpVector
    fun_prop
  exact hc.subtype_mk (fun z => (sphericalExpFamily v htan z.1 z.2).property)

@[simp] theorem sphericalExpFamily_zero {d : Nat} (v : UnitSphere d → Weight d)
    (htan : ∀ w, inner Real w.val (v w) = 0) (w : UnitSphere d) :
    sphericalExpFamily v htan 0 w = w := by
  apply Subtype.ext
  simp [sphericalExpFamily]

/-- Actual spherical EXP perturbations satisfy the source fixed-assignment formula
on a common open parameter neighborhood, with no extra cap-preservation premise. -/
theorem fixed_assignment_sphericalExp {d : Nat} (a : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (h : TwoCapClass a r mu)
    (v : UnitSphere d → Weight d) (htan : ∀ w, inner Real w.val (v w) = 0)
    (hv : Continuous v) :
    ∀ᶠ t in 𝓝 (0 : Real),
      TwoCapClass a r (mu.map (sphericalExpFamily v htan t)) ∧
      Integrable (fun w => assignedCost a (sphericalExpFamily v htan t w)) mu ∧
      sphericalWassersteinSq (mu.map (sphericalExpFamily v htan t)) (antipodalMeasure a) =
        2 * ∫ w, assignedCost a (sphericalExpFamily v htan t w) ∂mu :=
  fixed_assignment_local_pushforward a r mu h (sphericalExpFamily v htan)
    (sphericalExpFamily_continuous v htan hv) (sphericalExpFamily_zero v htan)

end PaperFormalization.MatrixFactorization
