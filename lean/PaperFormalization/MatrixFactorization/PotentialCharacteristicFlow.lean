import PaperFormalization.MatrixFactorization.AntipodalPotentialField
import PaperFormalization.MatrixFactorization.SphericalCharacteristics

/-! # MF23: explicit cap-free, dual-represented characteristic data

Execution records: `MF23_VALIDATION.md`.

This class is NOT declared equivalent to every source
WGF. The remaining source obligation is to obtain its classical optimal-dual
representation from the intended characteristic-solution definition. There
is no cap condition, no speed bound, no joint continuity, no uniqueness, and
no confinement conclusion among its fields. Laws are literal pushforwards.
Outside the cap class the selected potential is not fixed to dual weight zero.
-/
open MeasureTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- A precise conditional class on the nonnegative time half-line. Classical
potential differentials are explicit representation data, not hidden regularity. -/
structure PotentialCharacteristicFlow {d h : Nat} (O : Finset Nat)
    (a : Nat -> Weight h) (pole : UnitSphere d) (lambda p : Real)
    (teacher : Measure (UnitSphere d)) (initial : Fin 2 -> Measure (UnitSphere d)) where
  initial_probability : ∀ i, IsProbabilityMeasure (initial i)
  characteristic : Fin 2 -> Real -> UnitSphere d -> UnitSphere d
  measurable_space : ∀ i t, 0 <= t -> Measurable (characteristic i t)
  continuous_space : ∀ i t, 0 <= t ->
    ContinuousOn (characteristic i t) (initial i).support
  continuous_time : ∀ i w, w ∈ (initial i).support ->
    ContinuousOn (fun t => characteristic i t w) (Ici (0 : Real))
  initial_map : ∀ i w, w ∈ (initial i).support -> characteristic i 0 w = w
  dual : ∀ i t, 0 < t ->
    AntipodalGradientData pole ((initial i).map (characteristic i t))
  ode : ∀ i w, w ∈ (initial i).support -> ∀ t (ht : 0 < t),
    HasDerivAt (fun s => (characteristic i s w).val)
      (-potentialFullGradient O a pole lambda p
        (fun j => (initial j).map (characteristic j t)) teacher
        (fun j => dual j t ht) i (characteristic i t w)) t

variable {d h : Nat} {O : Finset Nat} {a : Nat -> Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 -> Measure (UnitSphere d)}

noncomputable def PotentialCharacteristicFlow.measure
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    (i : Fin 2) (t : Real) : Measure (UnitSphere d) :=
  (initial i).map (X.characteristic i t)

theorem PotentialCharacteristicFlow.measure_probability
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    (i : Fin 2) (t : Real) (ht : 0 <= t) : IsProbabilityMeasure (X.measure i t) := by
  letI := X.initial_probability i
  exact Measure.isProbabilityMeasure_map (X.measurable_space i t ht).aemeasurable

@[simp] theorem PotentialCharacteristicFlow.initial_law
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial) (i : Fin 2) :
    X.measure i 0 = initial i := by
  unfold PotentialCharacteristicFlow.measure
  calc
    _ = (initial i).map id := by
      apply Measure.map_congr
      filter_upwards [Measure.support_mem_ae (μ := initial i)] with w hw
      exact X.initial_map i w hw
    _ = initial i := Measure.map_id

/-- Every original supported label is a point of the current law's closed support. -/
theorem PotentialCharacteristicFlow.characteristic_mem_support
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    (i : Fin 2) (t : Real) (ht : 0 <= t) (w : UnitSphere d)
    (hw : w ∈ (initial i).support) : X.characteristic i t w ∈ (X.measure i t).support :=
  sphere_map_mem_support_of_continuousOn (initial i) (X.characteristic i t)
    (X.measurable_space i t ht) (X.continuous_space i t ht) hw

noncomputable def PotentialCharacteristicFlow.field
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    (t : Real) (ht : 0 < t) (i : Fin 2) (w : UnitSphere d) : Weight d :=
  potentialFullGradient O a pole lambda p (fun j => X.measure j t) teacher
    (fun j => X.dual j t ht) i w

/-- Global domination uses only probability and the proven dual-gradient bound. -/
theorem PotentialCharacteristicFlow.field_norm_le
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hp : 2 < p)
    (t : Real) (ht : 0 < t) (i : Fin 2) (w : UnitSphere d)
    (hw : w ∈ (X.measure i t).support) :
    norm (X.field t ht i w) <= potentialSpeedBound d O a lambda p :=
  potentialFullGradient_norm_le O a pole lambda p hp (fun j => X.measure j t)
    (fun j => X.measure_probability j t ht.le) teacher (fun j => X.dual j t ht) i w hw

/-- The existing actual cap field is recovered once current cap membership is proved. -/
theorem PotentialCharacteristicFlow.field_eq_source_on_caps
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    (t : Real) (ht : 0 < t) (r : Real) (hc : ∀ i, TwoCapClass pole r (X.measure i t))
    (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (X.measure i t).support) :
    X.field t ht i w = sphericalObjectiveGradient O a pole lambda p
      (X.measure 0 t) (X.measure 1 t) teacher teacher i w :=
  potentialFullGradient_eq_source O a pole r lambda p (fun j => X.measure j t) hc
    teacher (fun j => X.dual j t ht) i w hw

end PaperFormalization.MatrixFactorization
