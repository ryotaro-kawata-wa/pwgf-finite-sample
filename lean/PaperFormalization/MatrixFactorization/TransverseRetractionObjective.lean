import PaperFormalization.MatrixFactorization.TransverseRetractionTime

/-! # MF08: the manuscript's normalized center path and full objective

The two normalized pushed measures equal the EXP pushed measures at the same
explicit time change. Thus the entire original objective, including its true
Gaussian fit and optimal-transport regularizer, is identified before any
derivative is transferred. No integral of a pointwise remainder is assumed.
Strict escape still requires the unproved teacher-imbalance-to-signal bridge.
-/
open MeasureTheory Set Filter Asymptotics
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def variationRetractedObjective {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (lambda p : Real)
    (teacher1 teacher2 : Measure (UnitSphere d)) (t : Real) : Real :=
  modelObjective O a P.pole lambda p
    ((P.measure 0).map (sphericalRetractFamily (P.velocity 0) (P.tangent 0) t))
    ((P.measure 1).map (sphericalRetractFamily (P.velocity 1) (P.tangent 1) t)) teacher1 teacher2

theorem transverse_retracted_objective_eq_exp {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (r : Real) (hr : 0 < r) (hrpi : r < Real.pi/2)
    (s : Weight d) (hs : inner Real pole.val s = 0) (hunit : norm s = 1)
    (lambda p : Real) (teacher1 teacher2 : Measure (UnitSphere d)) (t : Real) :
    let P := transverseCenterVariation pole r hr hrpi s
    variationRetractedObjective O a P lambda p teacher1 teacher2 t =
      variationObjective O a P lambda p teacher1 teacher2 (halfSpeedTime t) := by
  dsimp only [variationRetractedObjective, variationObjective]
  rw [transverseCenter_retract_map_eq_exp pole r hr hrpi s hs hunit 0 t,
    transverseCenter_retract_map_eq_exp pole r hr hrpi s hs hunit 1 t]

/-- A calculus adapter for a time change with first jet one and second jet zero. -/
theorem second_derivative_comp_zero (F g : Real → Real) (d2 : Real) (hg0 : g 0 = 0)
    (hF1 : HasDerivAt F 0 0) (hF2 : HasDerivAt (deriv F) d2 0)
    (hFnear : ∀ᶠ t in 𝓝 (0 : Real), DifferentiableAt Real F t)
    (hg1 : HasDerivAt g 1 0) (hg2 : HasDerivAt (deriv g) 0 0)
    (hgnear : ∀ᶠ t in 𝓝 (0 : Real), DifferentiableAt Real g t) :
    HasDerivAt (fun t => F (g t)) 0 0 ∧
    HasDerivAt (deriv (fun t => F (g t))) d2 0 := by
  have hF1g : HasDerivAt F 0 (g 0) := by simpa only [hg0] using hF1
  have hF2g : HasDerivAt (deriv F) d2 (g 0) := by simpa only [hg0] using hF2
  have hgt : Tendsto g (𝓝 (0 : Real)) (𝓝 (0 : Real)) := by
    simpa only [hg0] using hg1.continuousAt.tendsto
  have he : deriv (fun t => F (g t)) =ᶠ[𝓝 (0 : Real)]
      (fun t => deriv F (g t)*deriv g t) := by
    filter_upwards [hgt.eventually hFnear, hgnear] with t hFt hgt
    exact (hFt.hasDerivAt.comp t hgt.hasDerivAt).deriv
  constructor
  · exact (hF1g.comp 0 hg1).congr_deriv (by ring)
  · have hd := (hF2g.comp 0 hg1).mul hg2
    have hd' := hd.congr_deriv (show d2*1*deriv g 0+deriv F (g 0)*0 = d2 by rw [hg1.deriv]; ring)
    exact hd'.congr_of_eventuallyEq he

theorem transverse_retracted_objective_variations {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (pole : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (s : Weight d) (hs : inner Real pole.val s = 0)
    (hunit : norm s = 1) (lambda p : Real) (hp : 2 < p)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    let P := transverseCenterVariation pole r hr hrpi s
    HasDerivAt (variationRetractedObjective O a P lambda p teacher teacher) 0 0 ∧
    HasDerivAt (deriv (variationRetractedObjective O a P lambda p teacher teacher))
      (-2*transverseTeacherSignal O a pole s teacher) 0 := by
  dsimp only
  let P := transverseCenterVariation pole r hr hrpi s
  have he : variationRetractedObjective O a P lambda p teacher teacher =
      (fun t => variationObjective O a P lambda p teacher teacher (halfSpeedTime t)) :=
    funext (transverse_retracted_objective_eq_exp O a pole r hr hrpi s hs hunit lambda p teacher teacher)
  rw [he]
  have hd := transverse_center_objective_variations O a hO pole r hr hrpi s hs lambda p hp teacher
  exact second_derivative_comp_zero _ _ _ halfSpeedTime_zero hd.1 hd.2
    (variationObjective_differentiable_near O a P lambda p hp teacher teacher)
    halfSpeedTime_first_zero halfSpeedTime_second_zero
    (Eventually.of_forall (fun t => (halfSpeedTime_hasDerivAt t).differentiableAt))

theorem transverse_retracted_objective_differentiable_near {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (s : Weight d) (hs : inner Real pole.val s = 0)
    (hunit : norm s = 1) (lambda p : Real) (hp : 2 < p)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    let P := transverseCenterVariation pole r hr hrpi s
    ∀ᶠ t in 𝓝 (0 : Real), DifferentiableAt Real (variationRetractedObjective O a P lambda p teacher teacher) t := by
  dsimp only
  let P := transverseCenterVariation pole r hr hrpi s
  have he : variationRetractedObjective O a P lambda p teacher teacher =
      (fun t => variationObjective O a P lambda p teacher teacher (halfSpeedTime t)) :=
    funext (transverse_retracted_objective_eq_exp O a pole r hr hrpi s hs hunit lambda p teacher teacher)
  rw [he]
  have ht : Tendsto halfSpeedTime (𝓝 (0 : Real)) (𝓝 (0 : Real)) := by
    simpa only [halfSpeedTime_zero] using halfSpeedTime_first_zero.continuousAt.tendsto
  filter_upwards [ht.eventually (variationObjective_differentiable_near O a P lambda p hp teacher teacher)] with t ht
  exact ht.comp t (halfSpeedTime_hasDerivAt t).differentiableAt

/-- The manuscript's normalized path has the same actual quadratic coefficient. -/
theorem transverse_retracted_objective_expansion {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (pole : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (s : Weight d) (hs : inner Real pole.val s = 0)
    (hunit : norm s = 1) (lambda p : Real) (hp : 2 < p)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    let P := transverseCenterVariation pole r hr hrpi s
    let F := variationRetractedObjective O a P lambda p teacher teacher
    (fun t => F t-F 0+transverseTeacherSignal O a pole s teacher*t^2) =o[𝓝 (0 : Real)] (fun t => t^2) := by
  let P := transverseCenterVariation pole r hr hrpi s
  let F := variationRetractedObjective O a P lambda p teacher teacher
  have hd := transverse_retracted_objective_variations O a hO pole r hr hrpi s hs hunit lambda p hp teacher
  have hi := peano_second_at_zero F (-2*transverseTeacherSignal O a pole s teacher) hd.1 hd.2
    (transverse_retracted_objective_differentiable_near O a pole r hr hrpi s hs hunit lambda p hp teacher)
  have he (t : Real) : F t-F 0-((-2*transverseTeacherSignal O a pole s teacher)/2)*t^2 =
      F t-F 0+transverseTeacherSignal O a pole s teacher*t^2 := by ring
  simpa only [he] using hi

/-- Strict local decrease for the actual normalized path, conditional only on
the separately stated positive-signal condition still to be derived from imbalance. -/
theorem transverse_retracted_strict_decrease {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (pole : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (s : Weight d) (hs : inner Real pole.val s = 0)
    (hunit : norm s = 1) (lambda p : Real) (hp : 2 < p)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (hvisible : 0 < transverseTeacherSignal O a pole s teacher) :
    let P := transverseCenterVariation pole r hr hrpi s
    let F := variationRetractedObjective O a P lambda p teacher teacher
    ∀ᶠ t in 𝓝 (0 : Real), t ≠ 0 →
      F t ≤ F 0-(transverseTeacherSignal O a pole s teacher/2)*t^2 ∧ F t < F 0 := by
  let P := transverseCenterVariation pole r hr hrpi s
  let F := variationRetractedObjective O a P lambda p teacher teacher
  have hi := transverse_retracted_objective_expansion O a hO pole r hr hrpi s hs hunit lambda p hp teacher
  have hb := hi.bound (half_pos hvisible)
  filter_upwards [hb] with t ht hne
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] at ht
  have he := (le_abs_self (F t-F 0+transverseTeacherSignal O a pole s teacher*t^2)).trans ht
  have hpos : 0 < (transverseTeacherSignal O a pole s teacher/2)*t^2 :=
    mul_pos (half_pos hvisible) (sq_pos_of_ne_zero hne)
  exact ⟨by linarith, by linarith⟩

noncomputable def variationRetractedRegularizer {d : Nat} (P : SphericalVariation d)
    (lambda p : Real) (t : Real) : Real :=
  metricRegularizer P.pole lambda p
    ((P.measure 0).map (sphericalRetractFamily (P.velocity 0) (P.tangent 0) t))
    ((P.measure 1).map (sphericalRetractFamily (P.velocity 1) (P.tangent 1) t))

theorem transverse_retracted_regularizer_eq_exp {d : Nat} (pole : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (s : Weight d) (hs : inner Real pole.val s = 0)
    (hunit : norm s = 1) (lambda p t : Real) :
    let P := transverseCenterVariation pole r hr hrpi s
    variationRetractedRegularizer P lambda p t = variationRegularizer P lambda p (halfSpeedTime t) := by
  dsimp only [variationRetractedRegularizer]
  rw [transverseCenter_retract_map_eq_exp pole r hr hrpi s hs hunit 0 t,
    transverseCenter_retract_map_eq_exp pole r hr hrpi s hs hunit 1 t]
  rfl

/-- This is the actual metric term on the normalized pushed measures. -/
theorem transverse_retracted_regularizer_formula {d : Nat} (pole : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (s : Weight d) (hs : inner Real pole.val s = 0)
    (hunit : norm s = 1) (lambda p : Real) :
    variationRetractedRegularizer (transverseCenterVariation pole r hr hrpi s) lambda p =ᶠ[𝓝 (0 : Real)]
      (fun t => (lambda/p*(1/2 : Real)^(p/2))*|halfSpeedTime t|^p) := by
  have ht : Tendsto halfSpeedTime (𝓝 (0 : Real)) (𝓝 (0 : Real)) := by
    simpa only [halfSpeedTime_zero] using halfSpeedTime_first_zero.continuousAt.tendsto
  filter_upwards [ht.eventually (transverseCenterVariation_regularizer_formula pole r hr hrpi s hs lambda p)] with t he
  rw [transverse_retracted_regularizer_eq_exp pole r hr hrpi s hs hunit lambda p t, he, hunit]
  norm_num

theorem transverse_retracted_regularizer_littleO {d : Nat} (pole : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (s : Weight d) (hs : inner Real pole.val s = 0)
    (hunit : norm s = 1) (lambda p : Real) (hp : 2 < p) :
    variationRetractedRegularizer (transverseCenterVariation pole r hr hrpi s) lambda p =o[𝓝 (0 : Real)]
      (fun t => t^2) := by
  let P := transverseCenterVariation pole r hr hrpi s
  let F := variationRegularizer P lambda p
  have hz : variationTransport P 0 = 0 := transverseCenterVariation_transport_zero pole r hr hrpi s
  have hzero : F 0 = 0 := by
    simp only [F, variationRegularizer, hz, Real.zero_rpow (by linarith : p/2 ≠ 0), mul_zero]
  have he : variationRetractedRegularizer P lambda p = fun t => F (halfSpeedTime t) :=
    funext (transverse_retracted_regularizer_eq_exp pole r hr hrpi s hs hunit lambda p)
  rw [he]
  have hd := metricRegularizer_zero_variations P lambda p hp hz
  have hj := second_derivative_comp_zero F halfSpeedTime 0 halfSpeedTime_zero hd.1 hd.2
    (variationRegularizer_differentiable_near P lambda p hp)
    halfSpeedTime_first_zero halfSpeedTime_second_zero
    (Eventually.of_forall (fun t => (halfSpeedTime_hasDerivAt t).differentiableAt))
  have ht : Tendsto halfSpeedTime (𝓝 (0 : Real)) (𝓝 (0 : Real)) := by
    simpa only [halfSpeedTime_zero] using halfSpeedTime_first_zero.continuousAt.tendsto
  have hnear : ∀ᶠ t in 𝓝 (0 : Real), DifferentiableAt Real (fun t => F (halfSpeedTime t)) t := by
    filter_upwards [ht.eventually (variationRegularizer_differentiable_near P lambda p hp)] with t hFt
    exact hFt.comp t (halfSpeedTime_hasDerivAt t).differentiableAt
  have hi := peano_second_at_zero (fun t => F (halfSpeedTime t)) 0 hj.1 hj.2 hnear
  simpa only [halfSpeedTime_zero, hzero, zero_div, zero_mul, sub_zero] using hi

end PaperFormalization.MatrixFactorization
