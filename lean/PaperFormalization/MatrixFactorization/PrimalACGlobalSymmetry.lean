import PaperFormalization.MatrixFactorization.PrimalACReflection

/-! # MF27: use global uniqueness only on global primal AC trajectories

Verification status and conditional scope: see `MF27_VALIDATION.md`. The predicates below concern the explicit,
unchanged primal AC class. Their relation to the manuscript's intended class
is still a separate source obligation. No uniqueness of arbitrary finite cap
solutions is inferred, and no classical optimal-potential representation is
introduced. Equality is required only at nonnegative times.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Uniqueness of actual pushed laws within the global primal AC class. -/
def PrimalACLawUnique {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (lambda p : Real)
    (teacher : Measure (UnitSphere d)) (initial : Fin 2 → Measure (UnitSphere d)) : Prop :=
  ∀ X Y : PrimalACCharacteristicData O a pole lambda p teacher initial,
    ∀ i t, 0 ≤ t → X.measure i t = Y.measure i t

/-- Supported path uniqueness is sufficient; unsupported representative values are irrelevant. -/
def PrimalACPathUnique {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (lambda p : Real)
    (teacher : Measure (UnitSphere d)) (initial : Fin 2 → Measure (UnitSphere d)) : Prop :=
  ∀ X Y : PrimalACCharacteristicData O a pole lambda p teacher initial,
    ∀ i t, 0 ≤ t → ∀ w, w ∈ (initial i).support →
      X.characteristic i t w = Y.characteristic i t w

variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

theorem PrimalACPathUnique.law_unique
    (hu : PrimalACPathUnique O a pole lambda p teacher initial) :
    PrimalACLawUnique O a pole lambda p teacher initial := by
  intro X Y i t ht
  apply Measure.map_congr
  filter_upwards [Measure.support_mem_ae (μ := initial i)] with w hw
  exact hu X Y i t ht w hw

/-- Reindex an actual global competitor along equality of initial measures. -/
theorem primal_ac_law_unique_of_initial_eq
    {initial' : Fin 2 → Measure (UnitSphere d)}
    (hu : PrimalACLawUnique O a pole lambda p teacher initial)
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (Y : PrimalACCharacteristicData O a pole lambda p teacher initial')
    (he : initial' = initial) (i : Fin 2) (t : Real) (ht : 0 ≤ t) :
    X.measure i t = Y.measure i t := by
  subst initial'
  exact hu X Y i t ht

/-- The branch is a consequence of initial symmetry and the explicit GLOBAL
uniqueness premise, comparing X with its proved global reflected competitor. -/
theorem PrimalACCharacteristicData.antibranch_of_global_unique
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (hO : ∀ n ∈ O, Odd n)
    (hu : PrimalACLawUnique O a pole lambda p teacher initial)
    (hi : initial 1 = reflectedMeasure (initial 0)) :
    ∀ t : Real, 0 ≤ t → X.measure 1 t = reflectedMeasure (X.measure 0 t) := by
  have he : reflectionExchangePair initial = initial := by
    funext i
    fin_cases i <;> simp [reflectionExchangePair, hi, reflectedMeasure_involutive]
  intro t ht
  have hh := primal_ac_law_unique_of_initial_eq hu X (X.reflectionExchange hO) he 1 t ht
  simpa only [X.reflectionExchange_measure hO 1 t,
    show (1 : Fin 2).rev = 0 by decide] using hh

/-- Exact zero symmetric odd moments follow from the law identity, not from
injectivity of a finite list of moments. -/
theorem PrimalACCharacteristicData.symmetric_odd_moment_zero
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (hO : ∀ n ∈ O, Odd n)
    (hu : PrimalACLawUnique O a pole lambda p teacher initial)
    (hi : initial 1 = reflectedMeasure (initial 0))
    (t : Real) (ht : 0 ≤ t) (n : Nat) (hn : Odd n) :
    symmetricMoment (X.measure 0 t) (X.measure 1 t) n = 0 := by
  letI := X.measure_probability 0 t
  rw [X.antibranch_of_global_unique hO hu hi t ht]
  exact reflected_branch_symmetric_zero (X.measure 0 t) n hn

end PaperFormalization.MatrixFactorization
