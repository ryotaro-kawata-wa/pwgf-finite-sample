import PaperFormalization.MatrixFactorization.SphericalRetraction
import Mathlib.Analysis.Calculus.DSlope

/-! # Exact signed-time change for the original normalized retraction

The zero-speed branch is the identity time parameter. Every nonzero tangent
speed uses the actual arctangent, and the resulting sphere map agrees exactly
with EXP. All derivative formulas extend through zero speed without a premise.
-/
open MeasureTheory Set Filter Asymptotics
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def retractionTime (speed t : Real) : Real :=
  if speed = 0 then t else Real.arctan (t*speed)/speed

@[simp] theorem retractionTime_zero (speed : Real) : retractionTime speed 0 = 0 := by
  simp [retractionTime]

@[simp] theorem retractionTime_zero_speed (t : Real) : retractionTime 0 t = t := by
  simp [retractionTime]

theorem retractionTime_hasDerivAt (speed t : Real) :
    HasDerivAt (retractionTime speed) (1/(1+t^2*speed^2)) t := by
  by_cases hs : speed = 0
  · subst speed
    have he : retractionTime 0 = id := funext retractionTime_zero_speed
    simpa only [he, pow_two, mul_zero, add_zero, div_one] using hasDerivAt_id t
  · have he : retractionTime speed = fun u => Real.arctan (u*speed)/speed := by
      funext u
      simp only [retractionTime, if_neg hs]
    rw [he]
    apply (((hasDerivAt_id t).mul_const speed).arctan.div_const speed).congr_deriv
    simp only [id_eq, one_mul]
    field_simp

theorem retractionTime_first_hasDerivAt (speed t : Real) :
    HasDerivAt (fun u => 1/(1+u^2*speed^2))
      (-2*t*speed^2/(1+t^2*speed^2)^2) t := by
  have hD : 0 < 1+t^2*speed^2 := by positivity
  have hd := ((((hasDerivAt_id t).pow 2).mul_const (speed^2)).const_add 1).inv hD.ne'
  simp only [one_div]
  apply hd.congr_deriv
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  ring

theorem retractionTime_second_hasDerivAt (speed t : Real) :
    HasDerivAt (deriv (retractionTime speed))
      (-2*t*speed^2/(1+t^2*speed^2)^2) t := by
  have he : deriv (retractionTime speed) = fun u => 1/(1+u^2*speed^2) :=
    funext (fun u => (retractionTime_hasDerivAt speed u).deriv)
  rw [he]
  exact retractionTime_first_hasDerivAt speed t

theorem retractionTime_first_zero (speed : Real) : HasDerivAt (retractionTime speed) 1 0 := by
  simpa using retractionTime_hasDerivAt speed 0

theorem retractionTime_second_zero (speed : Real) : HasDerivAt (deriv (retractionTime speed)) 0 0 := by
  simpa using retractionTime_second_hasDerivAt speed 0

/-- The identity is literal and valid for all signed times and zero velocity. -/
theorem sphericalRetract_exp_time {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t : Real) :
    sphericalRetractVector w v t = sphereExpVector w (retractionTime (norm v) t • v) := by
  by_cases hv0 : v = 0
  · subst v
    simp [sphericalRetractVector, retractionTime]
  · have hn0 : norm v ≠ 0 := norm_ne_zero_iff.mpr hv0
    have hn : norm (w.val+t • v) = Real.sqrt (1+(t*norm v)^2) := by
      have hs := sphericalRetract_denominator_sq w v hv t
      rw [mul_pow]
      rw [← hs, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [sphericalRetractVector, hn, sphereExpVector_scaled w v hv0,
      retractionTime, if_neg hn0]
    rw [div_mul_cancel₀ _ hn0, Real.cos_arctan, Real.sin_arctan]
    have he : ((t*norm v)/Real.sqrt (1+(t*norm v)^2))/norm v =
        t / Real.sqrt (1+(t*norm v)^2) := by
      field_simp
    rw [he]
    simp only [smul_add, smul_smul, div_eq_mul_inv, one_mul]
    module

/-- The time derivative never increases the absolute EXP speed. -/
theorem retractionTime_first_abs_le (speed t : Real) :
    abs (1/(1+t^2*speed^2)) ≤ 1 := by
  have hD : 1 ≤ 1+t^2*speed^2 := by
    nlinarith [mul_nonneg (sq_nonneg t) (sq_nonneg speed)]
  rw [abs_of_nonneg (by positivity)]
  exact (div_le_iff₀ (by linarith : 0 < 1+t^2*speed^2)).mpr (by linarith)

/-- This bound retains the factor of time used in local integral domination. -/
theorem retractionTime_second_abs_le (speed t : Real) :
    abs (-2*t*speed^2/(1+t^2*speed^2)^2) ≤ 2*abs t*speed^2 := by
  have hD : 1 ≤ 1+t^2*speed^2 := by
    nlinarith [mul_nonneg (sq_nonneg t) (sq_nonneg speed)]
  simp only [abs_div, abs_mul, abs_pow, sq_abs]
  norm_num
  exact div_le_self (by positivity) (by nlinarith)

/-- Every signed normalized time lies within the corresponding EXP interval. -/
theorem retractionTime_abs_le (speed t : Real) : abs (retractionTime speed t) ≤ abs t := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x (_ : x ∈ (Set.univ : Set Real)) => (retractionTime_hasDerivAt speed x).hasDerivWithinAt)
    (fun x (_ : x ∈ (Set.univ : Set Real)) => by
      simpa only [Real.norm_eq_abs] using retractionTime_first_abs_le speed x)
    (convex_univ : Convex Real (Set.univ : Set Real)) (Set.mem_univ (0 : Real)) (Set.mem_univ t)
  simpa only [retractionTime_zero, sub_zero, one_mul, Real.norm_eq_abs] using hh

/-- The removable zero-speed quotient is an existing differentiated slope. -/
theorem retractionTime_eq_dslope (speed t : Real) :
    retractionTime speed t = t * dslope Real.arctan 0 (t*speed) := by
  by_cases hs : speed = 0
  · subst speed
    simp [retractionTime, Real.deriv_arctan]
  · by_cases ht : t = 0
    · subst t
      simp
    · rw [retractionTime, if_neg hs, dslope_of_ne _ (mul_ne_zero ht hs)]
      simp only [slope, sub_zero, Real.arctan_zero, smul_eq_mul, vsub_eq_sub]
      field_simp

/-- Joint continuity includes vanishing speed, proved via the true derivative
of arctangent rather than by treating the quotient as nonsingular there. -/
theorem retractionTime_continuous :
    Continuous (fun p : Real × Real => retractionTime p.1 p.2) := by
  have hds : Continuous (dslope Real.arctan (0 : Real)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x = 0
    · subst x
      exact continuousAt_dslope_same.mpr (Real.differentiableAt_arctan 0)
    · exact (continuousAt_dslope_of_ne hx).mpr Real.continuous_arctan.continuousAt
  simp_rw [retractionTime_eq_dslope]
  exact continuous_snd.mul (hds.comp (continuous_snd.mul continuous_fst))

/-- The signed angle identity also holds at zero speed. -/
theorem retractionTime_mul_speed (speed t : Real) :
    retractionTime speed t * speed = Real.arctan (t*speed) := by
  by_cases hs : speed = 0
  · simp [hs]
  · simp only [retractionTime, if_neg hs, div_mul_cancel₀ _ hs]

/-- Normalization stays inside the open hemisphere of its starting point at
all finite signed times. This bound is for the actual angular displacement. -/
theorem retractionTime_smul_norm {d : Nat} (v : Weight d) (t : Real) :
    norm (retractionTime (norm v) t • v) = abs (Real.arctan (t*norm v)) := by
  rw [norm_smul, Real.norm_eq_abs, ← abs_of_nonneg (norm_nonneg v), ← abs_mul,
    abs_of_nonneg (norm_nonneg v), retractionTime_mul_speed]

/-- The original retraction has its exact spherical, rather than chordal,
displacement evaluated by the arctangent. -/
theorem sphericalDistance_retract {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t : Real) :
    sphericalDistance w (sphericalRetract w v hv t) = abs (Real.arctan (t*norm v)) := by
  have htangent : inner Real w.val (retractionTime (norm v) t • v) = 0 := by
    rw [real_inner_smul_right, hv, mul_zero]
  have he : sphericalRetract w v hv t =
      sphericalExp w (retractionTime (norm v) t • v) htangent := by
    apply Subtype.ext
    exact sphericalRetract_exp_time w v hv t
  have hshort : norm (retractionTime (norm v) t • v) < Real.pi := by
    rw [retractionTime_smul_norm]
    have hb : abs (Real.arctan (t*norm v)) < Real.pi/2 :=
      abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
    linarith [Real.pi_pos]
  rw [he, sphericalDistance_exp _ _ _ hshort, retractionTime_smul_norm]

theorem sphericalDistance_retract_le {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t : Real) :
    sphericalDistance w (sphericalRetract w v hv t) ≤ abs t * norm v := by
  rw [sphericalDistance_retract, ← retractionTime_smul_norm, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (retractionTime_abs_le (norm v) t) (norm_nonneg v)

end PaperFormalization.MatrixFactorization
