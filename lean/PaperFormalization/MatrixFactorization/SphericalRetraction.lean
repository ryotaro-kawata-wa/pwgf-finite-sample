import PaperFormalization.MatrixFactorization.TransverseObjectiveExpansion
/-! # MF08: the literal normalized retraction and its EXP comparison

The vector is (w+t*v)/norm(w+t*v), including zero velocity and signed time.
Tangency proves the denominator never vanishes. The first and ordinary second
ambient derivatives agree with EXP at zero, and their difference is o(t^2).
The induced maps retain the original cap class and optimal transport formula
on a common neighborhood. This pointwise comparison is not yet a theorem
identifying all integrated fitting and regularizer second variations.
-/
open MeasureTheory Set Filter Asymptotics
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def retractionScale (q t : Real) : Real := (1+t^2*q)^(-1/2 : Real)
noncomputable def retractionScaleFirst (q t : Real) : Real := -q*t*(1+t^2*q)^(-3/2 : Real)

theorem retractionScale_hasDerivAt {q : Real} (hq : 0 ≤ q) (t : Real) :
    HasDerivAt (retractionScale q) (retractionScaleFirst q t) t := by
  have hx : 0 < 1+t^2*q := by positivity
  have hd := ((((hasDerivAt_id t).pow 2).mul_const q).const_add 1).rpow_const
    (p := (-1/2 : Real)) (Or.inl hx.ne')
  apply hd.congr_deriv
  have hexp : (-1/2 : Real)-1 = -3/2 := by norm_num
  rw [hexp]
  simp only [retractionScaleFirst, Pi.pow_apply, id_eq, Nat.cast_ofNat,
    show (2 : Nat)-1 = 1 from rfl, pow_one, mul_one]
  ring

@[simp] theorem retractionScale_zero (q : Real) : retractionScale q 0 = 1 := by
  simp [retractionScale]

@[simp] theorem retractionScaleFirst_zero (q : Real) : retractionScaleFirst q 0 = 0 := by
  simp [retractionScaleFirst]

theorem retractionScaleFirst_hasDerivAt_zero (q : Real) :
    HasDerivAt (retractionScaleFirst q) (-q) 0 := by
  have hl := (hasDerivAt_id (0 : Real)).const_mul (-q)
  have hr := ((((hasDerivAt_id (0 : Real)).pow 2).mul_const q).const_add 1).rpow_const
    (p := (-3/2 : Real)) (Or.inl (by norm_num))
  apply (hl.mul hr).congr_deriv
  simp

noncomputable def sphericalRetractVector {d : Nat} (w : UnitSphere d) (v : Weight d) (t : Real) : Weight d :=
  (norm (w.val+t • v))⁻¹ • (w.val+t • v)

theorem sphericalRetract_denominator_sq {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t : Real) : norm (w.val+t • v)^2 = 1+t^2*norm v^2 := by
  simp [norm_add_sq_real, norm_smul, inner_smul_right, hv, mul_pow, sq_abs]

theorem sphericalRetractVector_scale {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t : Real) :
    sphericalRetractVector w v t = retractionScale (norm v^2) t • (w.val+t • v) := by
  have hn : norm (w.val+t • v) = Real.sqrt (1+t^2*norm v^2) := by
    rw [← sphericalRetract_denominator_sq w v hv t, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [sphericalRetractVector, hn, Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity)]
  norm_num [retractionScale]

noncomputable def sphericalRetractVelocity {d : Nat} (w : UnitSphere d) (v : Weight d) (t : Real) : Weight d :=
  retractionScaleFirst (norm v^2) t • (w.val+t • v) + retractionScale (norm v^2) t • v

theorem sphericalRetractVector_hasDerivAt {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t : Real) :
    HasDerivAt (sphericalRetractVector w v) (sphericalRetractVelocity w v t) t := by
  have he : sphericalRetractVector w v = fun s => retractionScale (norm v^2) s • (w.val+s • v) :=
    funext (sphericalRetractVector_scale w v hv)
  rw [he]
  apply ((retractionScale_hasDerivAt (sq_nonneg (norm v)) t).smul
    ((hasDerivAt_id t).smul_const v |>.const_add w.val)).congr_deriv
  simp only [sphericalRetractVelocity, id_eq, one_smul, add_comm]

@[simp] theorem sphericalRetractVector_zero {d : Nat} (w : UnitSphere d) (v : Weight d) :
    sphericalRetractVector w v 0 = w.val := by simp [sphericalRetractVector]

@[simp] theorem sphericalRetractVelocity_zero {d : Nat} (w : UnitSphere d) (v : Weight d) :
    sphericalRetractVelocity w v 0 = v := by simp [sphericalRetractVelocity]

theorem sphericalRetractVelocity_hasDerivAt_zero {d : Nat} (w : UnitSphere d) (v : Weight d) :
    HasDerivAt (sphericalRetractVelocity w v) (-(norm v^2) • w.val) 0 := by
  have hbase : HasDerivAt (fun s : Real => w.val+s • v) v 0 := by
    apply ((hasDerivAt_id (0 : Real)).smul_const v |>.const_add w.val).congr_deriv
    exact one_smul Real v
  have hd := ((retractionScaleFirst_hasDerivAt_zero (norm v^2)).smul hbase).add
    ((retractionScale_hasDerivAt (sq_nonneg (norm v)) 0).smul_const v)
  apply hd.congr_deriv
  simp

theorem sphericalRetractVector_norm {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t : Real) : norm (sphericalRetractVector w v t) = 1 := by
  have hs := sphericalRetract_denominator_sq w v hv t
  have hn : norm (w.val+t • v) ≠ 0 := by
    intro hz
    rw [hz] at hs
    nlinarith [mul_nonneg (sq_nonneg t) (sq_nonneg (norm v))]
  rw [sphericalRetractVector, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hn]

noncomputable def sphericalRetract {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t : Real) : UnitSphere d :=
  ⟨sphericalRetractVector w v t, by
    simpa only [Metric.mem_sphere, dist_zero_right] using sphericalRetractVector_norm w v hv t⟩

@[simp] theorem sphericalRetract_zero {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) : sphericalRetract w v hv 0 = w := by
  apply Subtype.ext
  exact sphericalRetractVector_zero w v

theorem sphericalRetract_second_jet {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) :
    HasDerivAt (sphericalRetractVector w v) v 0 ∧
    HasDerivAt (deriv (sphericalRetractVector w v)) (-(norm v^2) • w.val) 0 := by
  have he : deriv (sphericalRetractVector w v) = sphericalRetractVelocity w v := by
    funext t
    exact (sphericalRetractVector_hasDerivAt w v hv t).deriv
  rw [he]
  exact ⟨(sphericalRetractVector_hasDerivAt w v hv 0).congr_deriv (sphericalRetractVelocity_zero w v),
    sphericalRetractVelocity_hasDerivAt_zero w v⟩

theorem sphericalRetract_exp_littleO {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) :
    (fun t => sphericalRetractVector w v t-sphereExpVector w (t • v)) =o[𝓝 (0 : Real)]
      (fun t => t^2) := by
  have hd : HasDerivAt (fun t => sphericalRetractVelocity w v t-sphereExpVelocity w v t) 0 0 := by
    apply ((sphericalRetractVelocity_hasDerivAt_zero w v).sub (sphereExpVelocity_hasDerivAt w v 0)).congr_deriv
    simp
  have hzero : sphericalRetractVelocity w v 0-sphereExpVelocity w v 0 = 0 := by
    simp [sphereExpVelocity]
  have hsmall : (fun t => sphericalRetractVelocity w v t-sphereExpVelocity w v t) =o[𝓝 (0 : Real)]
      (fun t => t) := by
    simpa only [hzero, sub_zero, smul_zero] using hd.isLittleO
  have h := (convex_univ : Convex Real (Set.univ : Set Real)).isLittleO_pow_succ_real
    (Set.mem_univ (0 : Real))
    (fun t _ => ((sphericalRetractVector_hasDerivAt w v hv t).sub
      (sphereExpVector_hasDerivAt w v t)).hasDerivWithinAt)
    (n := 1) (by simpa only [nhdsWithin_univ, sub_zero, pow_one] using hsmall)
  simpa only [Pi.sub_apply, nhdsWithin_univ, sphericalRetractVector_zero, zero_smul, sphereExpVector_zero,
    sub_self, sub_zero] using h

noncomputable def sphericalRetractFamily {d : Nat} (v : UnitSphere d → Weight d)
    (hv : ∀ w, inner Real w.val (v w) = 0) (t : Real) (w : UnitSphere d) : UnitSphere d :=
  sphericalRetract w (v w) (hv w) t

theorem sphericalRetractFamily_continuous {d : Nat} (v : UnitSphere d → Weight d)
    (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) :
    Continuous (fun p : Real × UnitSphere d => sphericalRetractFamily v hv p.1 p.2) := by
  have hb : Continuous (fun p : Real × UnitSphere d => p.2.val+p.1 • v p.2) := by fun_prop
  have hn (p : Real × UnitSphere d) : norm (p.2.val+p.1 • v p.2) ≠ 0 := by
    have hs := sphericalRetract_denominator_sq p.2 (v p.2) (hv p.2) p.1
    intro hz
    rw [hz] at hs
    nlinarith [mul_nonneg (sq_nonneg p.1) (sq_nonneg (norm (v p.2)))]
  exact ((hb.norm.inv₀ hn).smul hb).subtype_mk _

@[simp] theorem sphericalRetractFamily_zero {d : Nat} (v : UnitSphere d → Weight d)
    (hv : ∀ w, inner Real w.val (v w) = 0) (w : UnitSphere d) :
    sphericalRetractFamily v hv 0 w = w := sphericalRetract_zero w (v w) (hv w)

theorem fixed_assignment_sphericalRetract {d : Nat} (a : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (hcap : TwoCapClass a r mu)
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) :
    ∀ᶠ t in 𝓝 (0 : Real),
      TwoCapClass a r (mu.map (sphericalRetractFamily v hv t)) ∧
      Integrable (fun w => assignedCost a (sphericalRetractFamily v hv t w)) mu ∧
      sphericalWassersteinSq (mu.map (sphericalRetractFamily v hv t)) (antipodalMeasure a) =
        2*∫ w, assignedCost a (sphericalRetractFamily v hv t w) ∂mu :=
  fixed_assignment_local_pushforward a r mu hcap (sphericalRetractFamily v hv)
    (sphericalRetractFamily_continuous v hv hc) (sphericalRetractFamily_zero v hv)

end PaperFormalization.MatrixFactorization
