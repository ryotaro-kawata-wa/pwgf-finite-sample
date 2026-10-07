import PaperFormalization.MatrixFactorization.AntipodalPotentialDuality
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! # MF23: bounded dual gradients and their local identification

Execution records: `MF23_VALIDATION.md`.

A spherical differential is stated on the actual EXP
curves. Differentiability of the minimum at a tie is not fabricated. Whenever
such a differential exists, its norm is bounded globally. For a dual optimum
on the cap class, complementary slackness identifies it with the already
verified assigned-cost gradient on the entire original closed support.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Intrinsic first differential expressed in the existing EXP coordinates.
This is a definition of a pointwise differential, not an existence assertion. -/
def HasSpherePotentialGradient {d : Nat} (f : UnitSphere d -> Real)
    (w : UnitSphere d) (g : Weight d) : Prop :=
  inner Real w.val g = 0 ∧
    ∀ (v : Weight d) (hv : inner Real w.val v = 0),
      HasDerivAt (fun t => f (geodesicPoint w v hv t)) (inner Real g v) 0

theorem HasSpherePotentialGradient.unique {d : Nat} {f : UnitSphere d -> Real}
    {w : UnitSphere d} {g k : Weight d}
    (hg : HasSpherePotentialGradient f w g) (hk : HasSpherePotentialGradient f w k) : g = k := by
  let v := g-k
  have hv : inner Real w.val v = 0 := by simp [v, inner_sub_right, hg.1, hk.1]
  have he := (hg.2 v hv).unique (hk.2 v hv)
  have hzero : norm (g-k)^2 = 0 := by
    have hself : inner Real (g-k) (g-k) = 0 := by
      rw [inner_sub_left]
      exact sub_eq_zero.mpr he
    simpa only [real_inner_self_eq_norm_sq] using hself
  have hn : norm (g-k) = 0 := by nlinarith [norm_nonneg (g-k)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- Every differentiable normalized two-atom potential has gradient norm at
most pi. The estimate is independent of the law, dual weight, and cap data. -/
theorem antipodalPotential_gradient_norm_le {d : Nat} (a w : UnitSphere d) (b : Real)
    (g : Weight d) (hg : HasSpherePotentialGradient (antipodalPotential a b) w g) :
    norm g <= Real.pi := by
  have hshort : ∀ᶠ t : Real in nhds 0, norm (t • g) < Real.pi := by
    have hc : Continuous (fun t : Real => norm (t • g)) := by fun_prop
    exact hc.continuousAt.eventually (gt_mem_nhds (by simpa using Real.pi_pos))
  have hlip : ∀ᶠ t : Real in nhds 0,
      norm (antipodalPotential a b (geodesicPoint w g hg.1 t) -
        antipodalPotential a b (geodesicPoint w g hg.1 0)) <=
      (Real.pi*norm g)*norm (t-0) := by
    filter_upwards [hshort] with t ht
    have hd : sphericalDistance w (geodesicPoint w g hg.1 t) = norm (t • g) :=
      sphericalDistance_exp w (t • g) _ ht
    have hb := antipodalPotential_sub_abs_le a b (geodesicPoint w g hg.1 t) w
    rw [sphericalDistance_comm (geodesicPoint w g hg.1 t) w, hd] at hb
    simpa only [geodesicPoint_zero, Real.norm_eq_abs, sub_zero, norm_smul,
      mul_assoc, mul_comm, mul_left_comm] using hb
  have hd := hg.2 g hg.1
  have hbound := hd.le_of_lip' (by positivity : 0 <= Real.pi*norm g) hlip
  rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)] at hbound
  nlinarith [norm_nonneg g, Real.pi_pos]

/-- An upper touching differentiable function has the same differential.
No uniqueness of optimal couplings or dual potentials is used. -/
theorem spherePotential_gradient_of_contact {d : Nat} (f : UnitSphere d -> Real)
    (w y : UnitSphere d) (c : Real) (g : Weight d)
    (hg : HasSpherePotentialGradient f w g)
    (hs : sphericalDistance w y < Real.pi)
    (hupper : ∀ x, f x <= poleCost y x-c)
    (hcontact : f w = poleCost y w-c) : g = poleGradient y w := by
  have he (v : Weight d) (hv : inner Real w.val v = 0) :
      inner Real g v = inner Real (poleGradient y w) v := by
    let F := fun t => poleCost y (geodesicPoint w v hv t)-c-f (geodesicPoint w v hv t)
    have hF0 : F 0 = 0 := by simp only [F, geodesicPoint_zero, hcontact]; ring
    have hmin : IsLocalMin F 0 := by
      apply Eventually.of_forall
      intro t
      rw [hF0]
      dsimp [F]
      linarith [hupper (geodesicPoint w v hv t)]
    have hd := ((poleCost_hasDerivAt_zero y w v hv hs).sub_const c).sub (hg.2 v hv)
    have hz := hmin.hasDerivAt_eq_zero hd
    change inner Real (poleGradient y w) v-inner Real g v = 0 at hz
    linarith
  let v := g-poleGradient y w
  have hv : inner Real w.val v = 0 := by
    simp only [v, inner_sub_right, hg.1, poleGradient_tangent, sub_self]
  have hz : inner Real v v = 0 := by
    dsimp only [v]
    rw [inner_sub_left]
    exact sub_eq_zero.mpr (he v hv)
  have hn : norm v = 0 := by
    rw [real_inner_self_eq_norm_sq] at hz
    nlinarith [norm_nonneg v]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- Local field agreement is a theorem about the actual optimal dual value.
It is not a new assumption that the global field is the assigned field. -/
theorem antipodalPotential_gradient_eq_assigned {d : Nat} (a : UnitSphere d)
    (r b : Real) (mu : Measure (UnitSphere d)) (hc : TwoCapClass a r mu)
    (ho : AntipodalPotentialOptimal a mu b) {w : UnitSphere d} (hw : w ∈ mu.support)
    (g : Weight d) (hg : HasSpherePotentialGradient (antipodalPotential a b) w g) :
    g = assignedGradient a w := by
  apply spherePotential_gradient_of_contact (antipodalPotential a b) w (assignedPole a w)
    (antipodalOffset a b (assignedPole a w)) g hg
  · have hd := assignedPole_distance_lt_cap a r hc.radius_lt (hc.support_subset hw)
    linarith [hc.radius_lt, Real.pi_pos]
  · intro x
    have hf := antipodalPotential_feasible a x (assignedPole a w) b (assignedPole_mem a w)
    linarith
  · exact antipodalPotential_contact_on_support a r b mu hc ho hw

end PaperFormalization.MatrixFactorization
