import PaperFormalization.MatrixFactorization.SphericalCharacteristics
import PaperFormalization.MatrixFactorization.SphericalObjectiveGradientSymmetry

/-! # Actual characteristic symmetry and conditional branch invariance

The transformed curves satisfy the same original field equation because
reflection and exchange covariance has been proved for that field. Initial
support and cap conditions are transported by actual maps. Uniqueness is the
source's explicitly stated hypothesis; neither existence nor uniqueness is
postulated as a theorem here.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def reflectionExchangePair {d : Nat}
    (mu : Fin 2 → Measure (UnitSphere d)) (i : Fin 2) : Measure (UnitSphere d) :=
  reflectedMeasure (mu i.rev)

def exchangePair {d : Nat} (mu : Fin 2 → Measure (UnitSphere d)) (i : Fin 2) :
    Measure (UnitSphere d) := mu i.rev

@[simp] theorem reflectionExchangePair_involutive {d : Nat} (mu : Fin 2 → Measure (UnitSphere d)) :
    reflectionExchangePair (reflectionExchangePair mu) = mu := by
  funext i
  simp only [reflectionExchangePair, Fin.rev_rev, reflectedMeasure_involutive]

@[simp] theorem exchangePair_involutive {d : Nat} (mu : Fin 2 → Measure (UnitSphere d)) :
    exchangePair (exchangePair mu) = mu := by
  funext i
  simp only [exchangePair,Fin.rev_rev]

variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}

/-- Reflecting and exchanging actual characteristics yields a solution for
exactly the reflected and exchanged original initial laws. -/
noncomputable def SphericalCharacteristicSolution.reflectionExchange
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (hO : ∀ n, n ∈ O → Odd n) :
    SphericalCharacteristicSolution O a pole radius lambda p teacher (reflectionExchangePair initial) T where
  time_nonneg := X.time_nonneg
  measure := fun i t => reflectedMeasure (X.measure i.rev t)
  characteristic := fun i t w => reflect (X.characteristic i.rev t (reflect w))
  map_law := by
    intro i t ht
    rw [X.map_law i.rev t ht]
    exact (reflectedMeasure_map_conjugate (initial i.rev) (X.characteristic i.rev t)
      (X.measurable_space i.rev t ht)).symm
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
    rw [X.initial_map i.rev (reflect w) hw', reflect_reflect]
  cap := by
    intro i t ht
    exact (X.cap i.rev t ht).reflected
  ode := by
    intro i w hw t ht
    have hw' := (reflectedMeasure_mem_support (initial i.rev) w).mp hw
    have ht' : t ∈ Icc (0 : Real) T := ⟨ht.1.le,ht.2.le⟩
    letI : IsProbabilityMeasure (X.measure 0 t) := (X.cap 0 t ht').probability
    letI : IsProbabilityMeasure (X.measure 1 t) := (X.cap 1 t ht').probability
    have hg := sphericalObjectiveGradient_reflection_exchange O a hO pole lambda p
      (X.measure 0 t) (X.measure 1 t) teacher radius (X.cap 0 t ht').radius_lt i
      (X.characteristic i.rev t (reflect w)) (X.characteristic_mem_caps i.rev t ht' (reflect w) hw')
    change HasDerivAt (fun s => -(X.characteristic i.rev s (reflect w)).val)
      (-sphericalObjectiveGradient O a pole lambda p (reflectedMeasure (X.measure 1 t))
        (reflectedMeasure (X.measure 0 t)) teacher teacher i
        (reflect (X.characteristic i.rev t (reflect w)))) t
    rw [hg]
    exact (X.ode i.rev (reflect w) hw' t ht).neg

/-- Ordinary exchange transforms actual solutions for a symmetric teacher. -/
noncomputable def SphericalCharacteristicSolution.exchange
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T) :
    SphericalCharacteristicSolution O a pole radius lambda p teacher (exchangePair initial) T where
  time_nonneg := X.time_nonneg
  measure := fun i t => X.measure i.rev t
  characteristic := fun i t w => X.characteristic i.rev t w
  map_law := fun i t ht => X.map_law i.rev t ht
  measurable_space := fun i t ht => X.measurable_space i.rev t ht
  continuous_space := fun i t ht => X.continuous_space i.rev t ht
  continuous_time := fun i w hw => X.continuous_time i.rev w hw
  initial_map := fun i w hw => X.initial_map i.rev w hw
  cap := fun i t ht => X.cap i.rev t ht
  ode := by
    intro i w hw t ht
    change HasDerivAt (fun s => (X.characteristic i.rev s w).val)
      (-sphericalObjectiveGradient O a pole lambda p (X.measure 1 t) (X.measure 0 t)
        teacher teacher i (X.characteristic i.rev t w)) t
    rw [sphericalObjectiveGradient_exchange O a pole lambda p (X.measure 0 t) (X.measure 1 t)
      teacher teacher i (X.characteristic i.rev t w)]
    exact X.ode i.rev w hw t ht


/-- Equality of initial laws allows source uniqueness to compare the actual solutions. -/
theorem characteristic_law_unique_of_initial_eq {d h : Nat} {O : Finset Nat}
    {a : Nat → Weight h} {pole : UnitSphere d} {radius lambda p : Real}
    {teacher : Measure (UnitSphere d)} {initial initial' : Fin 2 → Measure (UnitSphere d)} {T : Real}
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (Y : SphericalCharacteristicSolution O a pole radius lambda p teacher initial' T)
    (heq : initial' = initial) (i : Fin 2) (t : Real) (ht : t ∈ Icc (0 : Real) T) :
    X.measure i t = Y.measure i t := by
  subst initial'
  exact hunique X Y i t ht

/-- Source conditional invariance of the original antisymmetric measure branch. -/
theorem spherical_characteristic_antibranch_invariant {d h : Nat} {O : Finset Nat}
    {a : Nat → Weight h} (hO : ∀ n, n ∈ O → Odd n) {pole : UnitSphere d}
    {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
    {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0)) :
    ∀ t ∈ Icc (0 : Real) T, X.measure 1 t = reflectedMeasure (X.measure 0 t) := by
  have heq : reflectionExchangePair initial = initial := by
    funext i
    fin_cases i <;> simp [reflectionExchangePair,hinitial,reflectedMeasure_involutive]
  intro t ht
  exact characteristic_law_unique_of_initial_eq hunique X (X.reflectionExchange hO) heq 1 t ht

/-- Source conditional invariance of the original same-density measure branch. -/
theorem spherical_characteristic_same_density_invariant {d h : Nat} {O : Finset Nat}
    {a : Nat → Weight h} {pole : UnitSphere d} {radius lambda p : Real}
    {teacher : Measure (UnitSphere d)} {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = initial 0) :
    ∀ t ∈ Icc (0 : Real) T, X.measure 1 t = X.measure 0 t := by
  have heq : exchangePair initial = initial := by
    funext i
    fin_cases i <;> simp [exchangePair,hinitial]
  intro t ht
  exact characteristic_law_unique_of_initial_eq hunique X X.exchange heq 1 t ht

end PaperFormalization.MatrixFactorization
