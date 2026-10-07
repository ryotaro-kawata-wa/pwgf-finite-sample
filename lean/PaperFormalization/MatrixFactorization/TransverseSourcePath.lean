import PaperFormalization.MatrixFactorization.TransverseRetractionObjective
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # MF09: admissibility and metric order of the actual transverse source path

The half-projected field has a smooth ambient extension. Its normalized
pushforwards start at the antipodal law, have equal marginals, and preserve the
original cap class on a common signed neighborhood. The actual regularizer
has the printed O(|t|^p) bound as well as the existing o(t^2) conclusion.
-/
open MeasureTheory Set Filter Asymptotics
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def transverseHalfFieldAmbient {d : Nat} (s w : Weight d) : Weight d :=
  (1/2 : Real) • (s - inner Real w s • w)

theorem transverseHalfFieldAmbient_contDiff {d : Nat} (s : Weight d) :
    ContDiff Real ⊤ (transverseHalfFieldAmbient s) := by
  unfold transverseHalfFieldAmbient
  have hi : ContDiff Real ⊤ (fun w : Weight d => inner Real w s) :=
    contDiff_id.inner Real contDiff_const
  have hc : ContDiff Real ⊤ (fun _ : Weight d => (1/2 : Real)) := contDiff_const
  have hs : ContDiff Real ⊤ (fun _ : Weight d => s) := contDiff_const
  exact hc.smul (hs.sub (hi.smul contDiff_id))

theorem transverseHalfFieldAmbient_restrict {d : Nat} (s : Weight d) (w : UnitSphere d) :
    transverseHalfFieldAmbient s w.val = transverseHalfField s w := rfl

theorem transverseCenter_retract_same_density {d : Nat} (pole : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (s : Weight d) (t : Real) :
    let P := transverseCenterVariation pole r hr hrpi s
    (P.measure 1).map (sphericalRetractFamily (P.velocity 1) (P.tangent 1) t) =
      (P.measure 0).map (sphericalRetractFamily (P.velocity 0) (P.tangent 0) t) := rfl

theorem transverseCenter_retract_initial {d : Nat} (pole : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (s : Weight d) (i : Fin 2) :
    let P := transverseCenterVariation pole r hr hrpi s
    (P.measure i).map (sphericalRetractFamily (P.velocity i) (P.tangent i) 0) =
      antipodalMeasure pole := by
  have he : sphericalRetractFamily (transverseHalfField s) (transverseHalfField_tangent s) 0 = id :=
    funext (sphericalRetractFamily_zero _ _)
  change (antipodalMeasure pole).map
    (sphericalRetractFamily (transverseHalfField s) (transverseHalfField_tangent s) 0) = _
  rw [he, Measure.map_id]

theorem transverseCenter_retract_caps_near {d : Nat} (pole : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (s : Weight d) :
    let P := transverseCenterVariation pole r hr hrpi s
    ∀ᶠ t in 𝓝 (0 : Real), ∀ i : Fin 2,
      TwoCapClass pole r ((P.measure i).map (sphericalRetractFamily (P.velocity i) (P.tangent i) t)) := by
  have ht := fixed_assignment_sphericalRetract pole r (antipodalMeasure pole)
    (antipodalMeasure_twoCap pole hr hrpi) (transverseHalfField s)
    (transverseHalfField_tangent s) (transverseHalfField_continuous s)
  filter_upwards [ht] with t ht i
  exact ht.1

/-- The exact time change is globally no faster than its unit derivative at zero. -/
theorem halfSpeedTime_abs_le (t : Real) : |halfSpeedTime t| ≤ |t| := by
  have hb (x : Real) : norm (1/(1+(x/2)^2) : Real) ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact (div_le_one (by positivity)).mpr (by nlinarith [sq_nonneg (x/2)])
  have h := (convex_univ : Convex Real (Set.univ : Set Real)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (halfSpeedTime_hasDerivAt x).hasDerivWithinAt) (fun x _ => hb x)
    (Set.mem_univ (0 : Real)) (Set.mem_univ t)
  simpa only [halfSpeedTime_zero, sub_zero, one_mul, Real.norm_eq_abs] using h

/-- The regularizer is the actual transport functional on the normalized maps,
with arbitrary real exponent p>2 and both signs of time. -/
theorem transverse_retracted_regularizer_bigO {d : Nat} (pole : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (s : Weight d) (hs : inner Real pole.val s = 0)
    (hunit : norm s = 1) (lambda p : Real) (hp : 2 < p) :
    variationRetractedRegularizer (transverseCenterVariation pole r hr hrpi s) lambda p =O[𝓝 (0 : Real)]
      (fun t => |t|^p) := by
  apply IsBigO.of_bound |lambda/p*(1/2 : Real)^(p/2)|
  filter_upwards [transverse_retracted_regularizer_formula pole r hr hrpi s hs hunit lambda p] with t ht
  rw [ht, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (abs_nonneg _) (halfSpeedTime_abs_le t) (by linarith)) (abs_nonneg _)

end PaperFormalization.MatrixFactorization
