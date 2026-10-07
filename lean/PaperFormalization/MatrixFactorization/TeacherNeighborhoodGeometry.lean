import PaperFormalization.MatrixFactorization.SphericalContraction
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Angular transport controls for the teacher neighborhood

These bounds keep the spherical angle distinct from the inherited chordal
metric. The assigned-pole cost is controlled globally, including opposite
caps, without assuming that a transport plan preserves its cap labels.
-/
open MeasureTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

theorem sphericalDistance_triangle {d : Nat} (x y z : UnitSphere d) :
    sphericalDistance x z ≤ sphericalDistance x y + sphericalDistance y z := by
  simp only [sphericalDistance_eq_angle]
  exact InnerProductGeometry.angle_le_angle_add_angle _ _ _

/-- Chord length is bounded by actual angular distance, with no replacement
of the metric used in the original transport cost. -/
theorem unitSphere_chord_le_sphericalDistance {d : Nat} (w y : UnitSphere d) :
    norm (w.val-y.val) ≤ sphericalDistance w y := by
  have hn := norm_sub_sq_real w.val y.val
  simp only [unitSphere_norm, one_pow, one_add_one_eq_two] at hn
  have hc := Real.one_sub_sq_div_two_le_cos (x := sphericalDistance w y)
  rw [cos_sphericalDistance] at hc
  nlinarith [norm_nonneg (w.val-y.val), sphericalDistance_nonneg w y]

theorem assignedPole_distance_triangle {d : Nat} (a w y : UnitSphere d) :
    sphericalDistance w (assignedPole a w) ≤
      sphericalDistance w y + sphericalDistance y (assignedPole a y) := by
  have hp : sphericalDistance w (assignedPole a w) ≤ sphericalDistance w (assignedPole a y) := by
    rw [assignedPole_distance]
    rcases assignedPole_mem a y with hy | hy
    · rw [hy]
      exact min_le_left _ _
    · rw [hy]
      exact min_le_right _ _
  exact hp.trans (sphericalDistance_triangle w y (assignedPole a y))

/-- Distance to the antipodal target set is one-Lipschitz for angular distance. -/
theorem assignedPole_distance_sub_abs_le {d : Nat} (a w y : UnitSphere d) :
    abs (sphericalDistance w (assignedPole a w)-sphericalDistance y (assignedPole a y)) ≤
      sphericalDistance w y := by
  have hw := assignedPole_distance_triangle a w y
  have hy := assignedPole_distance_triangle a y w
  rw [sphericalDistance_comm y w] at hy
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A global angular Lipschitz constant for the actual half-squared cost. -/
theorem assignedCost_sub_abs_le {d : Nat} (a w y : UnitSphere d) :
    abs (assignedCost a w-assignedCost a y) ≤ Real.pi*sphericalDistance w y := by
  let x := sphericalDistance w (assignedPole a w)
  let z := sphericalDistance y (assignedPole a y)
  have hx : 0 ≤ x := sphericalDistance_nonneg _ _
  have hz : 0 ≤ z := sphericalDistance_nonneg _ _
  have hxpi : x ≤ Real.pi := sphericalDistance_le_pi _ _
  have hzpi : z ≤ Real.pi := sphericalDistance_le_pi _ _
  have hd : abs (x-z) ≤ sphericalDistance w y := assignedPole_distance_sub_abs_le a w y
  have hs : abs (x^2-z^2) ≤ sphericalDistance w y * (2*Real.pi) := by
    rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg hx hz)]
    have hb := mul_le_mul (show x+z ≤ 2*Real.pi by linarith) hd
      (abs_nonneg (x-z)) (by positivity : 0 ≤ 2*Real.pi)
    simpa only [mul_comm] using hb
  change abs (x^2/2-z^2/2) ≤ _
  rw [← sub_div, abs_div]
  norm_num
  nlinarith

end PaperFormalization.MatrixFactorization
