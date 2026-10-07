import PaperFormalization.MatrixFactorization.SphericalCurveCostAtPole

/-! # MF23: global two-atom transport potentials

Execution records: `MF23_VALIDATION.md`.

These are genuine half-squared angular costs on the
whole sphere, not the cap-only assigned-pole gradient extended by fiat.
A scalar dual weight is normalized to have target average zero. The two-atom
c-transform is their minimum. No optimality or differentiability of this
minimum is assumed here; in particular it may be nonsmooth at a tie.
-/
open MeasureTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Reverse triangle inequality for the actual spherical angle. -/
theorem poleDistance_sub_abs_le {d : Nat} (a x y : UnitSphere d) :
    |sphericalDistance x a - sphericalDistance y a| <= sphericalDistance x y := by
  have hx := sphericalDistance_triangle x y a
  have hy := sphericalDistance_triangle y x a
  rw [sphericalDistance_comm y x] at hy
  exact abs_le.mpr (And.intro (by linarith) (by linarith))

/-- This bound is global, including the pole and its antipode. -/
theorem poleCost_sub_abs_le {d : Nat} (a x y : UnitSphere d) :
    |poleCost a x - poleCost a y| <= Real.pi * sphericalDistance x y := by
  let r := sphericalDistance x a
  let s := sphericalDistance y a
  have hr : 0 <= r := sphericalDistance_nonneg x a
  have hs : 0 <= s := sphericalDistance_nonneg y a
  have hrp : r <= Real.pi := sphericalDistance_le_pi x a
  have hsp : s <= Real.pi := sphericalDistance_le_pi y a
  have hd : |r-s| <= sphericalDistance x y := poleDistance_sub_abs_le a x y
  have hsq : |r^2-s^2| <= (2*Real.pi)*sphericalDistance x y := by
    rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg hr hs)]
    exact mul_le_mul (by linarith : r+s <= 2*Real.pi) hd
      (abs_nonneg _) (by positivity)
  change |r^2/2-s^2/2| <= _
  rw [<- sub_div, abs_div]
  norm_num
  nlinarith

/-- The chordal topology is retained; this is only a comparison inequality. -/
theorem sphericalDistance_le_pi_half_chord {d : Nat} (x y : UnitSphere d) :
    sphericalDistance x y <= (Real.pi/2)*norm (x.val-y.val) := by
  have h := sphericalDistance_sq_le_chord_sq x y
  apply (sq_le_sq₀ (sphericalDistance_nonneg x y) (by positivity)).mp
  nlinarith

/-- A useful global chordal Lipschitz estimate, not a new transport metric. -/
theorem poleCost_sub_abs_le_chord {d : Nat} (a x y : UnitSphere d) :
    |poleCost a x-poleCost a y| <= (Real.pi^2/2)*norm (x.val-y.val) := by
  calc
    _ <= Real.pi*sphericalDistance x y := poleCost_sub_abs_le a x y
    _ <= Real.pi*((Real.pi/2)*norm (x.val-y.val)) :=
      mul_le_mul_of_nonneg_left (sphericalDistance_le_pi_half_chord x y) Real.pi_pos.le
    _ = _ := by ring

/-- Normalized c-transform for the actual antipodal two-atom target.
The offsets at the target atoms are b and -b. -/
noncomputable def antipodalPotential {d : Nat} (a : UnitSphere d) (b : Real)
    (w : UnitSphere d) : Real :=
  min (poleCost a w-b) (poleCost (reflect a) w+b)

theorem antipodalPotential_continuous {d : Nat} (a : UnitSphere d) (b : Real) :
    Continuous (antipodalPotential a b) :=
  ((poleCost_continuous a).sub continuous_const).min
    ((poleCost_continuous (reflect a)).add continuous_const)

theorem antipodalPotential_integrable {d : Nat} (a : UnitSphere d) (b : Real)
    (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu] :
    Integrable (antipodalPotential a b) mu :=
  sphere_integrable mu _ (antipodalPotential_continuous a b)

theorem antipodalPotential_le_positive {d : Nat} (a w : UnitSphere d) (b : Real) :
    antipodalPotential a b w <= poleCost a w-b := min_le_left _ _

theorem antipodalPotential_le_negative {d : Nat} (a w : UnitSphere d) (b : Real) :
    antipodalPotential a b w <= poleCost (reflect a) w+b := min_le_right _ _

/-- The dual weight never enters the spatial Lipschitz constant. -/
theorem antipodalPotential_sub_abs_le {d : Nat} (a : UnitSphere d) (b : Real)
    (x y : UnitSphere d) :
    |antipodalPotential a b x-antipodalPotential a b y| <=
      Real.pi*sphericalDistance x y := by
  have one (x y : UnitSphere d) : antipodalPotential a b x <=
      antipodalPotential a b y + Real.pi*sphericalDistance x y := by
    have hp := (abs_le.mp (poleCost_sub_abs_le a x y)).2
    have hn := (abs_le.mp (poleCost_sub_abs_le (reflect a) x y)).2
    change min _ _ <= min _ _ + _
    rcases le_total (poleCost a y-b) (poleCost (reflect a) y+b) with h | h
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans (by linarith)
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans (by linarith)
  have hx := one x y
  have hy := one y x
  rw [sphericalDistance_comm y x] at hy
  exact abs_le.mpr (And.intro (by linarith) (by linarith))

theorem antipodalPotential_sub_abs_le_chord {d : Nat} (a : UnitSphere d) (b : Real)
    (x y : UnitSphere d) :
    |antipodalPotential a b x-antipodalPotential a b y| <=
      (Real.pi^2/2)*norm (x.val-y.val) := by
  calc
    _ <= Real.pi*sphericalDistance x y := antipodalPotential_sub_abs_le a b x y
    _ <= Real.pi*((Real.pi/2)*norm (x.val-y.val)) :=
      mul_le_mul_of_nonneg_left (sphericalDistance_le_pi_half_chord x y) Real.pi_pos.le
    _ = _ := by ring

/-- Zero dual weight is the existing nearest-pole half cost, at every point. -/
@[simp] theorem antipodalPotential_zero {d : Nat} (a w : UnitSphere d) :
    antipodalPotential a 0 w = assignedCost a w := by
  have hx := sphericalDistance_nonneg w a
  have hy := sphericalDistance_nonneg w (reflect a)
  unfold antipodalPotential poleCost assignedCost
  rw [sub_zero, add_zero, assignedPole_distance]
  rcases le_total (sphericalDistance w a) (sphericalDistance w (reflect a)) with h | h
  · rw [min_eq_left h, min_eq_left (by nlinarith)]
  · rw [min_eq_right h, min_eq_right (by nlinarith)]

/-- Reflection changes only the normalized dual weight's sign. -/
theorem antipodalPotential_reflect {d : Nat} (a w : UnitSphere d) (b : Real) :
    antipodalPotential a b (reflect w) = antipodalPotential a (-b) w := by
  have hp : poleCost a (reflect w) = poleCost (reflect a) w := by
    unfold poleCost
    rw [<- sphericalDistance_reflect_reflect w (reflect a), reflect_reflect]
  have hn : poleCost (reflect a) (reflect w) = poleCost a w := by
    simp only [poleCost, sphericalDistance_reflect_reflect]
  simp only [antipodalPotential, hp, hn, sub_eq_add_neg, neg_neg, min_comm]

end PaperFormalization.MatrixFactorization
