import PaperFormalization.MatrixFactorization.SphericalRetraction
/-! # MF08: exact center reparameterization of the normalized path

For a unit source direction, both antipodal velocities have norm one-half.
Their normalized retractions equal EXP at time 2*arctan(t/2), for every signed
time. The equality below is an equality of the original pushed measures,
so it can be used directly for the full Gaussian and transport objective.
-/
open MeasureTheory Set Filter Asymptotics
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def halfSpeedTime (t : Real) : Real := 2*Real.arctan (t/2)

@[simp] theorem halfSpeedTime_zero : halfSpeedTime 0 = 0 := by simp [halfSpeedTime]

theorem halfSpeedTime_hasDerivAt (t : Real) :
    HasDerivAt halfSpeedTime (1/(1+(t/2)^2)) t := by
  apply ((((hasDerivAt_id t).div_const 2).arctan).const_mul 2).congr_deriv
  dsimp only [id_eq]
  ring

theorem halfSpeedTime_first_zero : HasDerivAt halfSpeedTime 1 0 := by
  have hd := halfSpeedTime_hasDerivAt 0
  norm_num at hd
  exact hd

theorem halfSpeedTime_second_zero : HasDerivAt (deriv halfSpeedTime) 0 0 := by
  have he : deriv halfSpeedTime = fun t => 1/(1+(t/2)^2) :=
    funext (fun t => (halfSpeedTime_hasDerivAt t).deriv)
  rw [he]
  simp only [one_div]
  have hd := ((((hasDerivAt_id (0 : Real)).div_const 2).pow 2).const_add 1).inv (by norm_num)
  apply hd.congr_deriv
  norm_num

theorem sphericalRetract_halfSpeed_exp {d : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (hspeed : norm v = 1/2) (t : Real) :
    sphericalRetractVector w v t = sphereExpVector w (halfSpeedTime t • v) := by
  have hn : norm (w.val+t • v) = Real.sqrt (1+(t/2)^2) := by
    have hsq := sphericalRetract_denominator_sq w v hv t
    rw [hspeed] at hsq
    have hsquare : 1+t^2*(1/2 : Real)^2 = 1+(t/2)^2 := by ring
    rw [hsquare] at hsq
    rw [← hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hvn : v ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hspeed
    norm_num at hspeed
  rw [sphericalRetractVector, hn, sphereExpVector_scaled w v hvn, hspeed, halfSpeedTime]
  have he : (2*Real.arctan (t/2))*(1/2 : Real) = Real.arctan (t/2) := by ring
  rw [he, Real.cos_arctan, Real.sin_arctan]
  simp only [smul_add, smul_smul, div_eq_mul_inv, one_mul]
  module

theorem transverseCenter_retract_map_eq_exp {d : Nat} (pole : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (s : Weight d) (hs : inner Real pole.val s = 0)
    (hunit : norm s = 1) (i : Fin 2) (t : Real) :
    let P := transverseCenterVariation pole r hr hrpi s
    (P.measure i).map (sphericalRetractFamily (P.velocity i) (P.tangent i) t) =
      (P.measure i).map (sphericalExpFamily (P.velocity i) (P.tangent i) (halfSpeedTime t)) := by
  apply Measure.map_congr
  filter_upwards [antipodalMeasure_ae_poles pole] with w hw
  have hn : norm (transverseHalfField s w) = 1/2 := by
    rcases hw with hw | hw
    · rw [hw, (transverseHalfField_at_pole pole s hs).1]
      norm_num [norm_smul, hunit]
    · rw [hw, (transverseHalfField_at_pole pole s hs).2]
      norm_num [norm_smul, hunit]
  apply Subtype.ext
  exact sphericalRetract_halfSpeed_exp w (transverseHalfField s w) (transverseHalfField_tangent s w) hn t

end PaperFormalization.MatrixFactorization
