import PaperFormalization.MatrixFactorization.TeacherNeighborhoodGeometry
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! # The actual spherical cost along arbitrary differentiable curves at its pole

A global comparison with chord length proves the derivative at the pole.
The curve is not assumed to be an exponential or normalized retraction path.
-/
open MeasureTheory Set Filter Asymptotics
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The angular squared distance admits a global chordal upper comparison,
including the antipode. The angular transport metric itself is unchanged. -/
theorem sphericalDistance_sq_le_chord_sq {d : Nat} (w y : UnitSphere d) :
    sphericalDistance w y ^ 2 ≤ Real.pi^2/4 * norm (w.val-y.val)^2 := by
  let r := sphericalDistance w y
  have hr : 0 ≤ r := sphericalDistance_nonneg w y
  have hrpi : r ≤ Real.pi := sphericalDistance_le_pi w y
  have hj0 : r/Real.pi ≤ Real.sin (r/2) := by
    convert Real.mul_le_sin (by positivity : 0 ≤ r/2) (by linarith : r/2 ≤ Real.pi/2) using 1
    ring
  have hj : r ≤ Real.sin (r/2)*Real.pi := (div_le_iff₀ Real.pi_pos).mp hj0
  have hsq := pow_le_pow_left₀ hr hj 2
  have ht := Real.sin_sq_eq_half_sub (r/2)
  have hn := norm_sub_sq_real w.val y.val
  have hc : Real.cos r = inner Real w.val y.val := cos_sphericalDistance w y
  have he : norm (w.val-y.val)^2 = 4*Real.sin (r/2)^2 := by
    rw [show 2*(r/2) = r by ring] at ht
    simp only [unitSphere_norm, one_pow] at hn
    nlinarith
  change r^2 ≤ _
  rw [he]
  nlinarith [hsq]

/-- The original half squared angular cost is quadratically small in chord length. -/
theorem poleCost_le_chord_sq {d : Nat} (y w : UnitSphere d) :
    poleCost y w ≤ Real.pi^2/8 * norm (w.val-y.val)^2 := by
  have hb := sphericalDistance_sq_le_chord_sq w y
  unfold poleCost
  nlinarith

/-- Every ambient differentiable sphere curve has zero cost derivative when it
passes through the pole, independently of its parametrization. -/
theorem poleCost_curve_hasDerivAt_at_pole {d : Nat} (y : UnitSphere d)
    (w : Real → UnitSphere d) (v : Weight d) (t : Real)
    (hw : HasDerivAt (fun s => (w s).val) v t) (hy : w t = y) :
    HasDerivAt (fun s => poleCost y (w s)) 0 t := by
  have hbig := hw.isBigO_sub.norm_left
  have hlim : Tendsto (fun s => norm ((w s).val-(w t).val)) (𝓝 t) (𝓝 0) := by
    have hc : ContinuousAt (fun s => norm ((w s).val-(w t).val)) t :=
      (hw.continuousAt.sub continuousAt_const).norm
    simpa only [sub_self, norm_zero] using hc.tendsto
  have hlittle : (fun s => norm ((w s).val-(w t).val)) =o[𝓝 t] (fun _ => (1 : Real)) :=
    (isLittleO_one_iff Real).mpr hlim
  have hsq : (fun s => norm ((w s).val-(w t).val)^2) =o[𝓝 t] (fun s => s-t) := by
    simpa only [one_mul, sq] using hlittle.mul_isBigO hbig
  have hbound : (fun s => poleCost y (w s)) =O[𝓝 t]
      (fun s => norm ((w s).val-(w t).val)^2) := by
    apply isBigO_of_le' (c := Real.pi^2/8)
    intro s
    rw [hy, Real.norm_eq_abs, abs_of_nonneg (by unfold poleCost; positivity),
      Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact poleCost_le_chord_sq y (w s)
  apply HasDerivAt.of_isLittleO
  simpa only [hy, poleCost_self, sub_zero, smul_zero] using hbound.trans_isLittleO hsq

end PaperFormalization.MatrixFactorization
