import PaperFormalization.MatrixFactorization.SphericalCharacteristicJointContinuity
import PaperFormalization.MatrixFactorization.SphericalCharacteristicIntegratedEnergy
import PaperFormalization.MatrixFactorization.SphericalStationaryCharacteristics
import PaperFormalization.MatrixFactorization.SphericalCharacteristicIntegratedBounds


/-! These diagnostics use the original cap-interval solution and its original
support. They do not postulate global label continuity or a cap-free flow. -/
open MeasureTheory Set
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}

-- The zero-length interval does not require a derivative at its sole endpoint.
example (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial 0)
    [IsProbabilityMeasure teacher] (hp : 2 < p) (i : Fin 2)
    (w : UnitSphere d) (hw : w ∈ (initial i).support) :
    LipschitzOnWith (Real.nnabs (characteristicSpeedBound d O a radius lambda p))
      (fun t => (X.characteristic i t w).val) (Icc (0 : Real) 0) :=
  X.characteristic_val_lipschitzOnWith hp i w hw

-- The time constant is common to both factors and every original supported label.
example (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p) :
    ∀ (i : Fin 2) (w : UnitSphere d), w ∈ (initial i).support →
      ∀ s ∈ Icc (0 : Real) T, ∀ t ∈ Icc (0 : Real) T,
      norm ((X.characteristic i s w).val - (X.characteristic i t w).val) ≤
        characteristicSpeedBound d O a radius lambda p * |s-t| := by
  intro i w hw s hs t ht
  have hb := (X.characteristic_val_lipschitzOnWith hp i w hw).dist_le_mul s hs t ht
  simpa only [dist_eq_norm, Real.coe_nnabs,
    abs_of_pos (characteristicSpeedBound_pos d O a radius lambda p), Real.norm_eq_abs] using hb

-- Sphere-valued Lipschitz continuity uses the inherited chordal metric.
example (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p) (i : Fin 2)
    (w : UnitSphere d) (hw : w ∈ (initial i).support) :
    LipschitzOnWith (Real.nnabs (characteristicSpeedBound d O a radius lambda p))
      (fun t => X.characteristic i t w) (Icc (0 : Real) T) :=
  X.characteristic_lipschitzOnWith hp i w hw

-- The joint-continuity statement includes both closed time endpoints.
example (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p) (i : Fin 2)
    (w : UnitSphere d) (hw : w ∈ (initial i).support) :
    ContinuousWithinAt (fun tw : Real × UnitSphere d => X.characteristic i tw.1 tw.2)
      ((Icc (0 : Real) T) ×ˢ (initial i).support) (0,w) ∧
    ContinuousWithinAt (fun tw : Real × UnitSphere d => X.characteristic i tw.1 tw.2)
      ((Icc (0 : Real) T) ×ˢ (initial i).support) (T,w) := by
  have hc := X.characteristic_joint_continuousOn hp i
  exact ⟨hc (0,w) ⟨⟨le_rfl,X.time_nonneg⟩,hw⟩,
    hc (T,w) ⟨⟨X.time_nonneg,le_rfl⟩,hw⟩⟩

end PaperFormalization.MatrixFactorization


/-! Boundary diagnostics for the actual integrated time-energy identity. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization.MF17EnergyChecks
open PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}

-- 1. A zero time horizon has no accumulated dissipation and needs no endpoint derivative.
example (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial 0)
    [IsProbabilityMeasure teacher] (hp : 2 < p) :
    (∫ u in (0 : Real)..0, X.gradientEnergy u) = 0 := by
  simpa only [sub_self] using X.integrated_energy hp 0 0 le_rfl le_rfl le_rfl

-- 2. Every degenerate interior or endpoint subinterval is included.
example (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p) (s : Real) (hs : s ∈ Icc 0 T) :
    IntervalIntegrable X.gradientEnergy volume s s ∧
      (∫ u in s..s, X.gradientEnergy u) = 0 := by
  exact ⟨X.gradientEnergy_intervalIntegrable hp s s hs.1 le_rfl hs.2,
    by simpa only [sub_self] using X.integrated_energy hp s s hs.1 le_rfl hs.2⟩

-- 3. The exact identity uses neither branch invariance nor a small-distance assumption.
example (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p) (s t : Real)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    X.objective t+(∫ u in s..t, X.gradientEnergy u) = X.objective s := by
  rw [X.integrated_energy hp s t hs hst ht]
  ring

-- 4. The accumulated dissipation is nonnegative, consistently with objective monotonicity.
example (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p) (s t : Real)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    0 ≤ ∫ u in s..t, X.gradientEnergy u := by
  rw [X.integrated_energy hp s t hs hst ht]
  exact sub_nonneg.mpr ((X.objective_antitoneOn hp) ⟨hs,hst.trans ht⟩ ⟨hs.trans hst,ht⟩ hst)

-- 5. A noninteger exponent in the original local-attraction range is included.
example (X : SphericalCharacteristicSolution O a pole radius lambda (5/2 : Real) teacher initial T)
    [IsProbabilityMeasure teacher] :
    X.objective T+(∫ u in (0 : Real)..T, X.gradientEnergy u) = X.objective 0 :=
  X.integrated_energy_from_initial (by norm_num) T ⟨X.time_nonneg,le_rfl⟩

-- 6. Zero initial transport gives constant objective and zero dissipation;
-- its constant fitting value is not asserted to vanish.
example (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p) (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hz : productAntipodalTransportSq pole (initial 0) (initial 1) = 0)
    (t : Real) (ht : t ∈ Icc 0 T) :
    X.objective t = X.objective 0 ∧ (∫ u in (0 : Real)..t, X.gradientEnergy u) = 0 := by
  have hstat := spherical_characteristic_zero_transport_stationary hO hp X hunique hz
  have hzero : (0 : Real) ∈ Icc 0 T := ⟨le_rfl,X.time_nonneg⟩
  have he : X.objective t = X.objective 0 := by
    unfold SphericalCharacteristicSolution.objective
    rw [hstat 0 t ht,hstat 1 t ht,hstat 0 0 hzero,hstat 1 0 hzero]
  refine ⟨he,?_⟩
  rw [X.integrated_energy hp 0 t le_rfl ht.1 ht.2,he,sub_self]

end PaperFormalization.MatrixFactorization.MF17EnergyChecks


/-! Boundary diagnostics for quantitative integrals of actual transport. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization.MF17IntegratedBoundsChecks
open PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}

section Source
variable (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
  [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
  (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
  (hinitial : initial 1 = reflectedMeasure (initial 0))
  (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
  (hsmall0 : productAntipodalTransportSq pole (initial 0) (initial 1) ≤
    coarseRadialRadius lambda p (fittingCurvatureConstant d O a/64))

-- 1. The negative transport derivative is integrable on a zero-length interval,
-- and the quantitative estimate keeps its exact zero right-hand side.
example (s : Real) (hs : s ∈ Icc 0 T) :
    IntervalIntegrable (fun u => -deriv X.transport u) volume s s ∧
      lambda*(∫ u in s..s, (X.transport u)^(p/2)) ≤ 0 := by
  refine ⟨X.transport_deriv_intervalIntegrable hO hunique hinitial hl hp hp4 hsmall0
    s s hs.1 le_rfl hs.2,?_⟩
  simpa only [sub_self] using X.integrated_transport_decay hO hunique hinitial hl hp hp4 hsmall0
    s s hs.1 le_rfl hs.2

-- 2. The full horizon uses its actual initial and terminal laws and derived power integrability.
example : IntervalIntegrable (fun u => (X.transport u)^(p-1)) volume 0 T ∧
    (lambda^2/4)*(∫ u in (0 : Real)..T, (X.transport u)^(p-1)) ≤ X.objective 0-X.objective T ∧
    lambda*(∫ u in (0 : Real)..T, (X.transport u)^(p/2)) ≤ X.transport 0-X.transport T := by
  exact ⟨X.transport_rpow_intervalIntegrable (p-1) (by linarith) 0 T le_rfl X.time_nonneg le_rfl,
    X.integrated_gradientEnergy_lower hO hunique hinitial hl hp hp4 hsmall0
      0 T le_rfl X.time_nonneg le_rfl,
    X.integrated_transport_decay hO hunique hinitial hl hp hp4 hsmall0
      0 T le_rfl X.time_nonneg le_rfl⟩

-- 3. Zero initial transport forces zero accumulated transport power;
-- this does not assert that the stationary fitting objective is zero.
example (hz : productAntipodalTransportSq pole (initial 0) (initial 1) = 0)
    (t : Real) (ht : t ∈ Icc 0 T) :
    (∫ u in (0 : Real)..t, (X.transport u)^(p/2)) = 0 := by
  have hz0 : X.transport 0 = 0 := by rw [X.transport_initial,hz]
  have hzt := X.transport_zero_persists hO hunique hinitial hl hp hp4 hsmall0
    0 t ⟨le_rfl,X.time_nonneg⟩ ht ht.1 hz0
  have hb := X.integrated_transport_decay hO hunique hinitial hl hp hp4 hsmall0
    0 t le_rfl ht.1 ht.2
  rw [hz0,hzt,sub_self] at hb
  have hn : 0 ≤ ∫ u in (0 : Real)..t, (X.transport u)^(p/2) := by
    apply intervalIntegral.integral_nonneg ht.1
    intro u hu
    exact Real.rpow_nonneg (X.productTransport_nonneg u ⟨hu.1,hu.2.trans ht.2⟩) _
  nlinarith
end Source

-- 4. p=5/2 yields the literal real powers 3/2 and 5/4, with no integer truncation.
example (X : SphericalCharacteristicSolution O a pole radius lambda (5/2 : Real) teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda (5/2 : Real) teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0)) (hl : 0 < lambda)
    (hsmall0 : productAntipodalTransportSq pole (initial 0) (initial 1) ≤
      coarseRadialRadius lambda (5/2 : Real) (fittingCurvatureConstant d O a/64)) :
    (lambda^2/4)*(∫ u in (0 : Real)..T, (X.transport u)^(3/2 : Real)) ≤ X.objective 0-X.objective T ∧
    lambda*(∫ u in (0 : Real)..T, (X.transport u)^(5/4 : Real)) ≤ X.transport 0-X.transport T := by
  constructor
  · simpa only [show (5/2 : Real)-1 = 3/2 by norm_num] using
      X.integrated_gradientEnergy_lower hO hunique hinitial hl (by norm_num) (by norm_num)
        hsmall0 0 T le_rfl X.time_nonneg le_rfl
  · simpa only [show (5/2 : Real)/2 = 5/4 by norm_num] using
      X.integrated_transport_decay hO hunique hinitial hl (by norm_num) (by norm_num)
        hsmall0 0 T le_rfl X.time_nonneg le_rfl

end PaperFormalization.MatrixFactorization.MF17IntegratedBoundsChecks
