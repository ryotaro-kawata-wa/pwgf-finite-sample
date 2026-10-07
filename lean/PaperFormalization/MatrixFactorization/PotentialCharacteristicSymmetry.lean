import PaperFormalization.MatrixFactorization.PotentialCharacteristicFlow
import PaperFormalization.MatrixFactorization.AntipodalPotentialSymmetry

/-! # MF23: use GLOBAL uniqueness on transformed GLOBAL represented flows

Execution records: `MF23_VALIDATION.md`.

This module never infers uniqueness of arbitrary finite
cap-interval solutions from a global uniqueness hypothesis. It transforms the
entire nonnegative-time trajectory, the exact original pushed laws, and the
actual optimal dual data. The uniqueness predicate is explicit for this
classical representation class; identifying it with the manuscript class
remains a separate source obligation.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat -> Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 -> Measure (UnitSphere d)}

noncomputable def PotentialCharacteristicFlow.reflectionCharacteristic
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    (i : Fin 2) (t : Real) (w : UnitSphere d) : UnitSphere d :=
  reflect (X.characteristic i.rev t (reflect w))

/-- The equality is between the actual measures, including the initial reflection. -/
theorem PotentialCharacteristicFlow.reflectionMeasure_eq
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    (i : Fin 2) (t : Real) (ht : 0 <= t) :
    (reflectionExchangePair initial i).map (X.reflectionCharacteristic i t) =
      reflectedMeasure (X.measure i.rev t) :=
  reflectedMeasure_map_conjugate (initial i.rev) (X.characteristic i.rev t)
    (X.measurable_space i.rev t ht)

noncomputable def PotentialCharacteristicFlow.reflectionDual
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    (i : Fin 2) (t : Real) (ht : 0 < t) :
    AntipodalGradientData pole ((reflectionExchangePair initial i).map
      (X.reflectionCharacteristic i t)) :=
  ((X.dual i.rev t ht).reflected (X.measure_probability i.rev t ht.le)).congrMeasure
    (X.reflectionMeasure_eq i t ht.le).symm

/-- The reflected velocity obeys the same literal dual field on every sphere point. -/
theorem PotentialCharacteristicFlow.reflectionField_eq
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    (hO : ∀ n ∈ O, Odd n) (t : Real) (ht : 0 < t) (i : Fin 2) (w : UnitSphere d) :
    potentialFullGradient O a pole lambda p
      (fun j => (reflectionExchangePair initial j).map (X.reflectionCharacteristic j t))
      teacher (fun j => X.reflectionDual j t ht) i (reflect w) = -X.field t ht i.rev w := by
  letI := X.measure_probability 0 t ht.le
  letI := X.measure_probability 1 t ht.le
  have hG (j : Fin 2) (z : UnitSphere d) :
      (X.reflectionDual j t ht).gradient z = -(X.dual j.rev t ht).gradient (reflect z) := by
    simp only [PotentialCharacteristicFlow.reflectionDual,
      AntipodalGradientData.congrMeasure_gradient, AntipodalGradientData.reflected_gradient]
  simp only [potentialFullGradient, hG, reflect_reflect,
    X.reflectionMeasure_eq 0 t ht.le, X.reflectionMeasure_eq 1 t ht.le]
  change sphericalFittingGradient O a (reflectedMeasure (X.measure 1 t))
      (reflectedMeasure (X.measure 0 t)) teacher teacher i (reflect w) +
    (lambda*(productAntipodalTransportSq pole (reflectedMeasure (X.measure 1 t))
      (reflectedMeasure (X.measure 0 t)))^(p/2-1)) •
      (-(X.dual i.rev t ht).gradient w) = _
  rw [sphericalFittingGradient_reflection_exchange O a hO (X.measure 0 t)
      (X.measure 1 t) teacher i w, productAntipodalTransportSq_reflection_exchange]
  simp only [PotentialCharacteristicFlow.field, potentialFullGradient, smul_neg, neg_add_rev]
  abel

/-- A global transformation, with no cap restriction and no new optimizer choice. -/
noncomputable def PotentialCharacteristicFlow.reflectionExchange
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    (hO : ∀ n ∈ O, Odd n) :
    PotentialCharacteristicFlow O a pole lambda p teacher (reflectionExchangePair initial) where
  initial_probability := by
    intro i
    letI := X.initial_probability i.rev
    exact reflectedMeasure_probability (initial i.rev)
  characteristic := X.reflectionCharacteristic
  measurable_space := by
    intro i t ht
    exact (reflect_measurable d).comp ((X.measurable_space i.rev t ht).comp (reflect_measurable d))
  continuous_space := by
    intro i t ht
    apply (reflect_continuous d).comp_continuousOn
    apply (X.continuous_space i.rev t ht).comp (reflect_continuous d).continuousOn
    intro w hw
    exact (reflectedMeasure_mem_support (initial i.rev) w).mp hw
  continuous_time := by
    intro i w hw
    have hw' := (reflectedMeasure_mem_support (initial i.rev) w).mp hw
    exact (reflect_continuous d).comp_continuousOn (X.continuous_time i.rev (reflect w) hw')
  initial_map := by
    intro i w hw
    have hw' := (reflectedMeasure_mem_support (initial i.rev) w).mp hw
    change reflect (X.characteristic i.rev 0 (reflect w)) = w
    rw [X.initial_map i.rev (reflect w) hw', reflect_reflect]
  dual := X.reflectionDual
  ode := by
    intro i w hw t ht
    have hw' := (reflectedMeasure_mem_support (initial i.rev) w).mp hw
    change HasDerivAt (fun s => -(X.characteristic i.rev s (reflect w)).val)
      (-potentialFullGradient O a pole lambda p
        (fun j => (reflectionExchangePair initial j).map (X.reflectionCharacteristic j t))
        teacher (fun j => X.reflectionDual j t ht) i
        (reflect (X.characteristic i.rev t (reflect w)))) t
    rw [X.reflectionField_eq hO t ht i (X.characteristic i.rev t (reflect w))]
    exact (X.ode i.rev (reflect w) hw' t ht).neg

@[simp] theorem PotentialCharacteristicFlow.reflectionExchange_measure
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    (hO : ∀ n ∈ O, Odd n) (i : Fin 2) (t : Real) (ht : 0 <= t) :
    (X.reflectionExchange hO).measure i t = reflectedMeasure (X.measure i.rev t) :=
  X.reflectionMeasure_eq i t ht

/-- Uniqueness among global represented laws, not among arbitrary finite solutions. -/
def PotentialCharacteristicLawUnique {d h : Nat} (O : Finset Nat)
    (a : Nat -> Weight h) (pole : UnitSphere d) (lambda p : Real)
    (teacher : Measure (UnitSphere d)) (initial : Fin 2 -> Measure (UnitSphere d)) : Prop :=
  forall X Y : PotentialCharacteristicFlow O a pole lambda p teacher initial,
    forall i t, 0 <= t -> X.measure i t = Y.measure i t

/-- A stronger uniqueness premise compares the original supported global maps. -/
def PotentialCharacteristicPathUnique {d h : Nat} (O : Finset Nat)
    (a : Nat -> Weight h) (pole : UnitSphere d) (lambda p : Real)
    (teacher : Measure (UnitSphere d)) (initial : Fin 2 -> Measure (UnitSphere d)) : Prop :=
  forall X Y : PotentialCharacteristicFlow O a pole lambda p teacher initial,
    forall i t, 0 <= t -> forall w, w ∈ (initial i).support ->
      X.characteristic i t w = Y.characteristic i t w

theorem PotentialCharacteristicPathUnique.law_unique
    (hu : PotentialCharacteristicPathUnique O a pole lambda p teacher initial) :
    PotentialCharacteristicLawUnique O a pole lambda p teacher initial := by
  intro X Y i t ht
  apply Measure.map_congr
  filter_upwards [Measure.support_mem_ae (μ := initial i)] with w hw
  exact hu X Y i t ht w hw

/-- Equality of initial laws is the only transport needed to invoke global uniqueness. -/
theorem potential_law_unique_of_initial_eq
    {initial' : Fin 2 -> Measure (UnitSphere d)}
    (hu : PotentialCharacteristicLawUnique O a pole lambda p teacher initial)
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    (Y : PotentialCharacteristicFlow O a pole lambda p teacher initial')
    (he : initial' = initial) (i : Fin 2) (t : Real) (ht : 0 <= t) :
    X.measure i t = Y.measure i t := by
  subst initial'
  exact hu X Y i t ht

/-- All-time branch invariance follows by comparing two actual GLOBAL represented
flows. This does not assert a local uniqueness theorem or source-class equivalence. -/
theorem PotentialCharacteristicFlow.antibranch_of_global_unique
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    (hO : ∀ n ∈ O, Odd n)
    (hu : PotentialCharacteristicLawUnique O a pole lambda p teacher initial)
    (hi : initial 1 = reflectedMeasure (initial 0)) :
    forall t, 0 <= t -> X.measure 1 t = reflectedMeasure (X.measure 0 t) := by
  have he : reflectionExchangePair initial = initial := by
    funext i
    fin_cases i <;> simp [reflectionExchangePair, hi, reflectedMeasure_involutive]
  intro t ht
  have hh := potential_law_unique_of_initial_eq hu X (X.reflectionExchange hO) he 1 t ht
  simpa only [X.reflectionExchange_measure hO 1 t ht,
    show (1 : Fin 2).rev = 0 by decide] using hh

end PaperFormalization.MatrixFactorization
