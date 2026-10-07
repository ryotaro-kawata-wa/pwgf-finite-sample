import PaperFormalization.MatrixFactorization.SphereMoments

/-! # MF02a: spherical distance and the nearest antipodal pole

The inherited metric on UnitSphere is
chordal; it is NOT replaced by a global instance. The cost below uses exactly
arccos(inner x y), identified with mathlib's angle for unit vectors.

The assigned map is total, with an arbitrary positive-pole tie convention at
the equator. Reflection equivariance is only claimed off that tie, in the two
strict caps. No optimal-transport conclusion is assumed here.
-/
open MeasureTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

@[simp] theorem unitSphere_norm {d : Nat} (w : UnitSphere d) : ‖w.val‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using w.property

theorem unitSphere_ne_zero {d : Nat} (w : UnitSphere d) : w.val ≠ 0 := by
  intro h
  have hn := unitSphere_norm w
  rw [h, norm_zero] at hn
  norm_num at hn

noncomputable def sphericalDistance {d : Nat} (x y : UnitSphere d) : Real :=
  Real.arccos (inner Real x.val y.val)

theorem sphericalDistance_eq_angle {d : Nat} (x y : UnitSphere d) :
    sphericalDistance x y = InnerProductGeometry.angle x.val y.val := by
  simp [sphericalDistance, InnerProductGeometry.angle]

theorem sphericalDistance_continuous (d : Nat) :
    Continuous (fun z : UnitSphere d × UnitSphere d => sphericalDistance z.1 z.2) := by
  unfold sphericalDistance
  fun_prop

theorem sphericalDistance_nonneg {d : Nat} (x y : UnitSphere d) :
    0 ≤ sphericalDistance x y := Real.arccos_nonneg _

theorem sphericalDistance_le_pi {d : Nat} (x y : UnitSphere d) :
    sphericalDistance x y ≤ Real.pi := Real.arccos_le_pi _

theorem sphericalDistance_comm {d : Nat} (x y : UnitSphere d) :
    sphericalDistance x y = sphericalDistance y x := by
  simp only [sphericalDistance, real_inner_comm]

@[simp] theorem sphericalDistance_self {d : Nat} (x : UnitSphere d) :
    sphericalDistance x x = 0 := by
  rw [sphericalDistance_eq_angle]
  exact InnerProductGeometry.angle_self (unitSphere_ne_zero x)

theorem sphericalDistance_eq_zero_iff {d : Nat} (x y : UnitSphere d) :
    sphericalDistance x y = 0 ↔ x = y := by
  constructor
  · intro h
    apply Subtype.ext
    apply InnerProductGeometry.eq_of_angle_eq_zero_of_norm_eq
    · rwa [← sphericalDistance_eq_angle]
    · simp
  · rintro rfl
    exact sphericalDistance_self x

@[simp] theorem sphericalDistance_reflect_right {d : Nat} (x y : UnitSphere d) :
    sphericalDistance x (reflect y) = Real.pi - sphericalDistance x y := by
  simp only [sphericalDistance_eq_angle, reflect_val,
    InnerProductGeometry.angle_neg_right]

@[simp] theorem sphericalDistance_reflect_reflect {d : Nat} (x y : UnitSphere d) :
    sphericalDistance (reflect x) (reflect y) = sphericalDistance x y := by
  simp only [sphericalDistance_eq_angle, reflect_val,
    InnerProductGeometry.angle_neg_neg]

@[simp] theorem sphericalDistance_antipode {d : Nat} (a : UnitSphere d) :
    sphericalDistance a (reflect a) = Real.pi := by simp

theorem unitSphere_ne_reflect {d : Nat} (a : UnitSphere d) : a ≠ reflect a := by
  intro h
  have hd := sphericalDistance_antipode a
  rw [← h, sphericalDistance_self] at hd
  exact Real.pi_pos.ne' hd.symm

/-- The open cap is defined with angular, not chordal, radius. -/
def sphericalCap {d : Nat} (a : UnitSphere d) (r : Real) : Set (UnitSphere d) :=
  {w | sphericalDistance w a < r}

theorem sphericalCap_isOpen {d : Nat} (a : UnitSphere d) (r : Real) :
    IsOpen (sphericalCap a r) := by
  change IsOpen {w : UnitSphere d | sphericalDistance w a < r}
  have hc : Continuous (fun w : UnitSphere d => sphericalDistance w a) := by
    unfold sphericalDistance
    fun_prop
  exact isOpen_lt hc continuous_const

theorem sphericalCap_disjoint {d : Nat} (a : UnitSphere d) (r : Real)
    (hr : r < Real.pi / 2) : Disjoint (sphericalCap a r) (sphericalCap (reflect a) r) := by
  apply Set.disjoint_left.mpr
  intro w hw hp
  change sphericalDistance w a < r at hw
  change sphericalDistance w (reflect a) < r at hp
  rw [sphericalDistance_reflect_right] at hp
  linarith

theorem sphericalCap_pole_mem {d : Nat} (a : UnitSphere d) (r : Real)
    (hr : 0 < r) : a ∈ sphericalCap a r := by
  simpa only [sphericalCap, Set.mem_setOf_eq, sphericalDistance_self] using hr

@[simp] theorem sphericalCap_reflect_mem {d : Nat} (a w : UnitSphere d) (r : Real) :
    reflect w ∈ sphericalCap (reflect a) r ↔ w ∈ sphericalCap a r := by
  simp only [sphericalCap, Set.mem_setOf_eq, sphericalDistance_reflect_reflect]

/-- Ties occur only away from either allowed strict cap. -/
noncomputable def assignedPole {d : Nat} (a w : UnitSphere d) : UnitSphere d :=
  if sphericalDistance w a ≤ sphericalDistance w (reflect a) then a else reflect a

theorem assignedPole_measurable {d : Nat} (a : UnitSphere d) : Measurable (assignedPole a) := by
  unfold assignedPole
  apply Measurable.ite
    (measurableSet_le
      (((sphericalDistance_continuous d).comp (continuous_id.prodMk continuous_const)).measurable)
      (((sphericalDistance_continuous d).comp (continuous_id.prodMk continuous_const)).measurable))
    measurable_const measurable_const

theorem assignedPole_mem {d : Nat} (a w : UnitSphere d) :
    assignedPole a w = a ∨ assignedPole a w = reflect a := by
  unfold assignedPole
  split_ifs <;> simp

theorem assignedPole_positive {d : Nat} (a : UnitSphere d) (r : Real)
    (hr : r < Real.pi / 2) {w : UnitSphere d} (hw : w ∈ sphericalCap a r) :
    assignedPole a w = a := by
  apply if_pos
  change sphericalDistance w a < r at hw
  rw [sphericalDistance_reflect_right]
  linarith

theorem assignedPole_negative {d : Nat} (a : UnitSphere d) (r : Real)
    (hr : r < Real.pi / 2) {w : UnitSphere d} (hw : w ∈ sphericalCap (reflect a) r) :
    assignedPole a w = reflect a := by
  apply if_neg
  change sphericalDistance w (reflect a) < r at hw
  rw [sphericalDistance_reflect_right] at hw ⊢
  linarith

theorem assignedPole_distance {d : Nat} (a w : UnitSphere d) :
    sphericalDistance w (assignedPole a w) =
      min (sphericalDistance w a) (sphericalDistance w (reflect a)) := by
  unfold assignedPole
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_not_ge h)).symm

/-- Half the squared spherical cost, with its continuous min-form exposed. -/
noncomputable def assignedCost {d : Nat} (a w : UnitSphere d) : Real :=
  (sphericalDistance w (assignedPole a w)) ^ 2 / 2

theorem assignedCost_continuous {d : Nat} (a : UnitSphere d) : Continuous (assignedCost a) := by
  change Continuous (fun w : UnitSphere d => assignedCost a w)
  simp only [assignedCost, assignedPole_distance]
  exact ((((sphericalDistance_continuous d).comp (continuous_id.prodMk continuous_const)).min
    ((sphericalDistance_continuous d).comp (continuous_id.prodMk continuous_const))).pow 2).div_const 2

theorem assignedCost_nonneg {d : Nat} (a w : UnitSphere d) : 0 ≤ assignedCost a w := by
  unfold assignedCost
  positivity

theorem assignedCost_integrable {d : Nat} (a : UnitSphere d)
    (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu] : Integrable (assignedCost a) mu :=
  sphere_integrable mu _ (assignedCost_continuous a)

/-- Pointwise bound valid even outside the caps; no transport plan is assumed. -/
theorem assignedCost_le_pole_cost {d : Nat} (a w y : UnitSphere d)
    (hy : y = a ∨ y = reflect a) : 2 * assignedCost a w ≤ (sphericalDistance w y)^2 := by
  have h0 := sphericalDistance_nonneg w (assignedPole a w)
  have hle : sphericalDistance w (assignedPole a w) ≤ sphericalDistance w y := by
    rw [assignedPole_distance]
    rcases hy with rfl | rfl
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hs := pow_le_pow_left₀ h0 hle 2
  dsimp [assignedCost]
  nlinarith

end PaperFormalization.MatrixFactorization
