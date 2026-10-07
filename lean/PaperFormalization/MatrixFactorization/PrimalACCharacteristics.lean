import PaperFormalization.MatrixFactorization.CharacteristicIntegralBounds

/-! # MF25: primal AC characteristic data, without supportwise dual gradients

Verification status and conditional scope: see `MF25_VALIDATION.md`. The inputs below are an explicit analytic characteristic
class: literal pushed laws, Borel pullback velocities, locally absolutely
continuous paths almost everywhere in the ORIGINAL labels, their AE ODE, and
the FULL objective's primal first variation at almost every nonnegative time.

This file does not assert that the manuscript's continuity equation alone
provides these data. In particular AC is not inferred from mere continuity.
No cap membership, speed estimate, joint continuity, integral equation, or
uniqueness conclusion is installed as an input. Negative-time representatives
are unused by the mathematical conclusions.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

structure PrimalACCharacteristicData {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (lambda p : Real)
    (teacher : Measure (UnitSphere d)) (initial : Fin 2 → Measure (UnitSphere d)) where
  initial_probability : ∀ i, IsProbabilityMeasure (initial i)
  characteristic : Fin 2 → Real → UnitSphere d → UnitSphere d
  measurable_space : ∀ i t, Measurable (characteristic i t)
  continuous_space : ∀ i t, 0 ≤ t → ContinuousOn (characteristic i t) (initial i).support
  initial_map : ∀ i w, w ∈ (initial i).support → characteristic i 0 w = w
  gradient : Fin 2 → Real → UnitSphere d → Weight d
  measurable_pullback : ∀ i, Measurable (fun tw : Real × UnitSphere d =>
    gradient i tw.1 (characteristic i tw.1 tw.2))
  first_variation : ∀ᵐ t ∂volume.restrict (Ici (0 : Real)), ∀ i,
    HasSphereFirstVariation ((initial i).map (characteristic i t))
      (sourcePartialObjective O a pole lambda p
        (fun j => (initial j).map (characteristic j t)) teacher i) (gradient i t)
  path_ac : ∀ i s t, 0 ≤ s → 0 ≤ t → ∀ᵐ w ∂initial i,
    AbsolutelyContinuousOnInterval (fun r => (characteristic i r w).val) s t
  ode : ∀ i, ∀ᵐ w ∂initial i, ∀ᵐ t ∂volume.restrict (Ici (0 : Real)),
    HasDerivAt (fun r => (characteristic i r w).val)
      (-gradient i t (characteristic i t w)) t

variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

noncomputable def PrimalACCharacteristicData.measure
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (i : Fin 2) (t : Real) : Measure (UnitSphere d) :=
  (initial i).map (X.characteristic i t)

theorem PrimalACCharacteristicData.measure_probability
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (i : Fin 2) (t : Real) : IsProbabilityMeasure (X.measure i t) := by
  letI := X.initial_probability i
  exact Measure.isProbabilityMeasure_map (X.measurable_space i t).aemeasurable

@[simp] theorem PrimalACCharacteristicData.initial_law
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial) (i : Fin 2) :
    X.measure i 0 = initial i := by
  unfold PrimalACCharacteristicData.measure
  calc
    _ = (initial i).map id := by
      apply Measure.map_congr
      filter_upwards [Measure.support_mem_ae (μ := initial i)] with w hw
      exact X.initial_map i w hw
    _ = initial i := Measure.map_id

noncomputable def PrimalACCharacteristicData.pullbackGradient
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (i : Fin 2) (t : Real) (w : UnitSphere d) : Weight d :=
  X.gradient i t (X.characteristic i t w)

theorem PrimalACCharacteristicData.pullbackGradient_measurable_time
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (i : Fin 2) (w : UnitSphere d) : Measurable (fun t => X.pullbackGradient i t w) :=
  (X.measurable_pullback i).comp (measurable_id.prodMk measurable_const)

/-- The full first variation supplies the speed bound before a cap interval
has been obtained. Fubini is applied with its explicit Borel hypothesis. -/
theorem PrimalACCharacteristicData.speed_bound_ae
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p) (i : Fin 2) :
    ∀ᵐ w ∂initial i, ∀ᵐ t ∂volume.restrict (Ici (0 : Real)),
      norm (X.pullbackGradient i t w) ≤ primalObjectiveSpeedBound d O a lambda p :=
  source_primal_gradient_time_label_bound (volume.restrict (Ici (0 : Real)))
    O a pole lambda p hl hp initial X.initial_probability X.characteristic
    X.measurable_space teacher X.gradient X.measurable_pullback X.first_variation i

/-- True time integrability and the integral equation for each fixed time pair.
The label-exception set may depend on the pair. -/
theorem PrimalACCharacteristicData.integral_equation_ae
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (i : Fin 2) (s t : Real) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ∀ᵐ w ∂initial i,
      IntervalIntegrable (fun r => X.pullbackGradient i r w) volume s t ∧
      (X.characteristic i t w).val - (X.characteristic i s w).val =
        -(∫ r in s..t, X.pullbackGradient i r w) := by
  filter_upwards [X.speed_bound_ae hl hp i, X.path_ac i s t hs ht, X.ode i] with w hb hac hd
  exact ac_negative_gradient_integral (fun r => (X.characteristic i r w).val)
    (fun r => X.pullbackGradient i r w) (X.pullbackGradient_measurable_time i w)
    (primalObjectiveSpeedBound d O a lambda p) hb hs ht hac hd

theorem PrimalACCharacteristicData.endpoint_bound_ae
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (i : Fin 2) (s t : Real) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ∀ᵐ w ∂initial i,
      dist (X.characteristic i s w) (X.characteristic i t w) ≤
        primalObjectiveSpeedBound d O a lambda p * dist s t := by
  filter_upwards [X.speed_bound_ae hl hp i, X.path_ac i s t hs ht, X.ode i] with w hb hac hd
  exact ac_negative_gradient_endpoint_bound (fun r => (X.characteristic i r w).val)
    (fun r => X.pullbackGradient i r w) (X.pullbackGradient_measurable_time i w)
    (primalObjectiveSpeedBound d O a lambda p) hb hs ht hac hd

/-- Extend endpoint bounds, not values of an arbitrary gradient representative.
The result holds at every original closed-support label and every time pair. -/
theorem PrimalACCharacteristicData.supported_lipschitz
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (initial i).support) :
    LipschitzOnWith (Real.nnabs (primalObjectiveSpeedBound d O a lambda p))
      (fun t => X.characteristic i t w) (Ici (0 : Real)) :=
  supported_endpoints_lipschitz (initial i) (X.characteristic i) (Ici (0 : Real))
    (primalObjectiveSpeedBound d O a lambda p)
    (primalObjectiveSpeedBound_nonneg d O a lambda p hl)
    (fun t ht => X.continuous_space i t ht)
    (fun s hs t ht => X.endpoint_bound_ae hl hp i s t hs ht) w hw

/-- Joint continuity is derived without any previously known cap membership. -/
theorem PrimalACCharacteristicData.supported_joint_continuity
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p) (i : Fin 2) :
    ContinuousOn (fun tw : Real × UnitSphere d => X.characteristic i tw.1 tw.2)
      ((Ici (0 : Real)) ×ˢ (initial i).support) :=
  supported_joint_continuity_of_ae_endpoint_bound (initial i) (X.characteristic i)
    (Ici (0 : Real)) (primalObjectiveSpeedBound d O a lambda p)
    (primalObjectiveSpeedBound_nonneg d O a lambda p hl)
    (fun t ht => X.continuous_space i t ht)
    (fun s hs t ht => X.endpoint_bound_ae hl hp i s t hs ht)

theorem PrimalACCharacteristicData.supported_time_continuity
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (initial i).support) :
    ContinuousOn (fun t => X.characteristic i t w) (Ici (0 : Real)) :=
  (X.supported_lipschitz hl hp i w hw).continuousOn

/-- The original supported points are carried into the full current support. -/
theorem PrimalACCharacteristicData.characteristic_mem_support
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (i : Fin 2) (t : Real) (ht : 0 ≤ t) (w : UnitSphere d)
    (hw : w ∈ (initial i).support) : X.characteristic i t w ∈ (X.measure i t).support :=
  sphere_map_mem_support_of_continuousOn (initial i) (X.characteristic i t)
    (X.measurable_space i t) (X.continuous_space i t ht) hw

end PaperFormalization.MatrixFactorization
