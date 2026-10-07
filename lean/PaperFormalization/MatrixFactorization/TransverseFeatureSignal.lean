import PaperFormalization.MatrixFactorization.TransverseCenterGeometry
/-! # MF07: the actual first transverse feature and teacher signal

The derivative of the original odd activation is proved even. Evaluation of
both half-mass atoms then keeps the field's one-half normalization explicitly.
The visibility signal here is the original Gaussian squared pairing, without
assuming that a nonempty activation makes that signal positive.
-/
open MeasureTheory ProbabilityTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

theorem finiteHermiteActivationJet_one_even {h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (x : Real) :
    finiteHermiteActivationJet 1 O a (-x) = finiteHermiteActivationJet 1 O a x := by
  have hd (s : Real) : HasDerivAt (finiteHermiteActivation O a) (finiteHermiteActivationJet 1 O a s) s := by
    have he : finiteHermiteActivationJet 0 O a = finiteHermiteActivation O a :=
      funext (finiteHermiteActivationJet_zero O a)
    rw [← he]
    exact finiteHermiteActivationJet_hasDerivAt 0 O a s
  have hneg : HasDerivAt (fun t => finiteHermiteActivation O a (-t))
      (-finiteHermiteActivationJet 1 O a (-x)) x := by
    apply ((hd (-x)).scomp x (hasDerivAt_neg x)).congr_deriv
    exact neg_one_smul Real _
  have hodd : HasDerivAt (fun t => finiteHermiteActivation O a (-t))
      (-finiteHermiteActivationJet 1 O a x) x :=
    (hd x).neg.congr_of_eventuallyEq (Filter.Eventually.of_forall (finiteHermiteActivation_odd O a hO))
  exact neg_inj.mp (hneg.unique hodd)

noncomputable def transverseFeature {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (pole : UnitSphere d) (s z : Weight d) : Weight h :=
  ((1/2 : Real)*inner Real s z) • finiteHermiteActivationJet 1 O a (inner Real pole.val z)

/-- Both original atoms and their half masses are evaluated, including the
even scalar activation derivative and the source field's factor one-half. -/
theorem transverseCenterVariation_featureFirst {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (pole : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (s : Weight d) (hs : inner Real pole.val s = 0)
    (i : Fin 2) (z : Weight d) :
    variationFeatureFirst O a (transverseCenterVariation pole r hr hrpi s) i 0 z =
      transverseFeature O a pole s z := by
  have hc : Continuous (fun w : UnitSphere d =>
      sphericalFeatureFirst 0 O a w (transverseHalfField s w) (transverseHalfField_tangent s w) z 0) :=
    (sphericalFeatureFirst_continuous 0 O a (transverseHalfField s) (transverseHalfField_tangent s)
      (transverseHalfField_continuous s)).comp (f := fun w => ((0,z),w)) (by fun_prop)
  change (∫ w, sphericalFeatureFirst 0 O a w (transverseHalfField s w)
    (transverseHalfField_tangent s w) z 0 ∂antipodalMeasure pole) = _
  rw [integral_antipodalMeasure pole _ hc]
  have ha := transverseHalfField_at_pole pole s hs
  simp only [sphericalFeatureFirst_at_zero, ha.1, ha.2, reflect_val, inner_neg_left,
    zero_add, finiteHermiteActivationJet_one_even O a hO, real_inner_smul_left, transverseFeature]
  module

noncomputable def transverseTeacherSignal {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (pole : UnitSphere d) (s : Weight d) (teacher : Measure (UnitSphere d)) : Real :=
  ∫ z, (inner Real (meanFeature (finiteHermiteActivation O a) teacher z)
    (transverseFeature O a pole s z))^2 ∂stdGaussian (Weight d)

theorem transverseTeacherSignal_nonneg {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (pole : UnitSphere d) (s : Weight d) (teacher : Measure (UnitSphere d)) :
    0 ≤ transverseTeacherSignal O a pole s teacher := integral_nonneg (fun z => sq_nonneg _)

theorem transverseCenterVariation_pairing {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (pole : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (s : Weight d) (hs : inner Real pole.val s = 0)
    (teacher : Measure (UnitSphere d)) (z : Weight d) :
    centerFittingPairing O a (transverseCenterVariation pole r hr hrpi s) teacher teacher z =
      (inner Real (meanFeature (finiteHermiteActivation O a) teacher z)
        (transverseFeature O a pole s z))^2 := by
  rw [center_same_velocity_pairing O a _ (transverseCenterVariation_transport_zero pole r hr hrpi s) rfl,
    transverseCenterVariation_featureFirst O a hO pole r hr hrpi s hs]

/-- The signal is a genuine Gaussian integral; no integrability premise is added. -/
theorem transverseTeacherSignal_integrable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (pole : UnitSphere d)
    (s : Weight d) (hs : inner Real pole.val s = 0) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] :
    Integrable (fun z => (inner Real (meanFeature (finiteHermiteActivation O a) teacher z)
      (transverseFeature O a pole s z))^2) (stdGaussian (Weight d)) := by
  have hr : 0 < Real.pi/4 := by linarith [Real.pi_pos]
  have hrpi : Real.pi/4 < Real.pi/2 := by linarith [Real.pi_pos]
  have hi := centerFittingPairing_integrable O a hO
    (transverseCenterVariation pole (Real.pi/4) hr hrpi s)
    (transverseCenterVariation_transport_zero pole (Real.pi/4) hr hrpi s) teacher teacher
  exact hi.congr (Filter.Eventually.of_forall
    (transverseCenterVariation_pairing O a hO pole (Real.pi/4) hr hrpi s hs teacher))

/-- Exact first and second derivatives for the constructed same-density EXP path. -/
theorem transverse_center_objective_variations {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (pole : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (s : Weight d) (hs : inner Real pole.val s = 0)
    (lambda p : Real) (hp : 2 < p) (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    let P := transverseCenterVariation pole r hr hrpi s
    HasDerivAt (variationObjective O a P lambda p teacher teacher) 0 0 ∧
    HasDerivAt (deriv (variationObjective O a P lambda p teacher teacher))
      (-2*transverseTeacherSignal O a pole s teacher) 0 := by
  have hd := spherical_objective_center_variations O a hO
    (transverseCenterVariation pole r hr hrpi s) lambda p hp
    (transverseCenterVariation_transport_zero pole r hr hrpi s) teacher teacher
  refine ⟨hd.1, hd.2.congr_deriv ?_⟩
  simp only [transverseCenterVariation_pairing O a hO pole r hr hrpi s hs, transverseTeacherSignal]

/-- Conditional strict curvature: the teacher-imbalance-to-positive-signal
construction is deliberately not assumed proved by this calculus implication. -/
theorem transverse_center_negative_curvature {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (pole : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (s : Weight d) (hs : inner Real pole.val s = 0)
    (lambda p : Real) (hp : 2 < p) (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (hvisible : 0 < transverseTeacherSignal O a pole s teacher) :
    let P := transverseCenterVariation pole r hr hrpi s
    deriv (deriv (variationObjective O a P lambda p teacher teacher)) 0 < 0 := by
  dsimp only
  rw [(transverse_center_objective_variations O a hO pole r hr hrpi s hs lambda p hp teacher).2.deriv]
  linarith

end PaperFormalization.MatrixFactorization
