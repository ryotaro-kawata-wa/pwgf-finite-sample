import PaperFormalization.MatrixFactorization.SphereL2ReflectionInverse
import PaperFormalization.MatrixFactorization.PrimalACGlobalSymmetry
import PaperFormalization.MatrixFactorization.IntegralL2PrimalBridge

/-! # MF30: the intrinsic source subclass and its actual reflected competitor

The author confirmed the intended deterministic, supported-space-continuous
AC characteristic interpretation on 2026-10-05. The predicate below retains
the source identity on every L2 direction, rather than assuming uniqueness
on the larger bounded-test primal class. It contains no cap, branch, speed,
decay, or uniqueness conclusion. No new flow record is introduced.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

/-- The original intrinsic first variation, on the same current law and
represented by the same measurable gradient at its actual AE times. -/
def PrimalACCharacteristicData.HasSourceL2FirstVariation
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial) : Prop :=
  ∀ᵐ t ∂volume.restrict (Ici (0 : Real)), ∀ i,
    ∃ G : sphereTangentL2 (X.measure i t),
      HasSphereL2FirstVariation (X.measure i t)
        (sourcePartialObjective O a pole lambda p (fun j => X.measure j t) teacher i) G ∧
      sphereL2Representative G =ᵐ[X.measure i t] X.gradient i t

/-- The actual global reflection preserves the full source L2 property. -/
theorem PrimalACCharacteristicData.HasSourceL2FirstVariation.reflectionExchange
    {X : PrimalACCharacteristicData O a pole lambda p teacher initial}
    (H : X.HasSourceL2FirstVariation) (hO : ∀ n ∈ O, Odd n) :
    (X.reflectionExchange hO).HasSourceL2FirstVariation := by
  classical
  filter_upwards [H] with t ht
  choose G hG hrep using ht
  have hsource := source_l2_firstVariation_reflection_exchange O a hO pole lambda p
    (fun j => X.measure j t) (fun j => X.measure_probability j t) teacher G hG
  let P (mu : Fin 2 → Measure (UnitSphere d)) (g : Fin 2 → UnitSphere d → Weight d) : Prop :=
    ∀ i, ∃ V : sphereTangentL2 (mu i),
      HasSphereL2FirstVariation (mu i)
        (sourcePartialObjective O a pole lambda p mu teacher i) V ∧
      sphereL2Representative V =ᵐ[mu i] g i
  change P (fun j => (X.reflectionExchange hO).measure j t)
    (fun j => (X.reflectionExchange hO).gradient j t)
  have hmeasure : (fun j => (X.reflectionExchange hO).measure j t) =
      reflectionExchangePair (fun j => X.measure j t) := by
    funext j
    exact X.reflectionExchange_measure hO j t
  rw [hmeasure]
  intro i
  refine ⟨sphereL2Reflected (G i.rev), hsource i, ?_⟩
  apply (sphereL2Reflected_rep (G i.rev)).trans
  filter_upwards [ae_reflected_of_ae (X.measure i.rev t) (hrep i.rev)] with w hw
  rw [hw]
  rfl

/-- Uniqueness quantifies only over the intrinsic source subclass. It does
not claim uniqueness for all competitors in the larger primal test class. -/
def SourceL2ACLawUnique {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (lambda p : Real)
    (teacher : Measure (UnitSphere d)) (initial : Fin 2 → Measure (UnitSphere d)) : Prop :=
  ∀ X Y : PrimalACCharacteristicData O a pole lambda p teacher initial,
    X.HasSourceL2FirstVariation → Y.HasSourceL2FirstVariation →
      ∀ i t, 0 ≤ t → X.measure i t = Y.measure i t

/-- Supported path uniqueness in exactly the same source subclass is sufficient. -/
def SourceL2ACPathUnique {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (lambda p : Real)
    (teacher : Measure (UnitSphere d)) (initial : Fin 2 → Measure (UnitSphere d)) : Prop :=
  ∀ X Y : PrimalACCharacteristicData O a pole lambda p teacher initial,
    X.HasSourceL2FirstVariation → Y.HasSourceL2FirstVariation →
      ∀ i t, 0 ≤ t → ∀ w, w ∈ (initial i).support →
        X.characteristic i t w = Y.characteristic i t w

theorem SourceL2ACPathUnique.law_unique
    (hu : SourceL2ACPathUnique O a pole lambda p teacher initial) :
    SourceL2ACLawUnique O a pole lambda p teacher initial := by
  intro X Y hX hY i t ht
  apply Measure.map_congr
  filter_upwards [Measure.support_mem_ae (μ := initial i)] with w hw
  exact hu X Y hX hY i t ht w hw

/-- Initial-law equality is used only to reindex the actual global competitor. -/
theorem source_l2_ac_law_unique_of_initial_eq
    {initial' : Fin 2 → Measure (UnitSphere d)}
    (hu : SourceL2ACLawUnique O a pole lambda p teacher initial)
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (hX : X.HasSourceL2FirstVariation)
    (Y : PrimalACCharacteristicData O a pole lambda p teacher initial')
    (hY : Y.HasSourceL2FirstVariation) (he : initial' = initial)
    (i : Fin 2) (t : Real) (ht : 0 ≤ t) : X.measure i t = Y.measure i t := by
  subst initial'
  exact hu X Y hX hY i t ht

/-- Branch invariance uses only original-source competitors. The reflected
candidate's full L2 identity is proved, not inferred from bounded testing. -/
theorem PrimalACCharacteristicData.antibranch_of_source_unique
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (hX : X.HasSourceL2FirstVariation) (hO : ∀ n ∈ O, Odd n)
    (hu : SourceL2ACLawUnique O a pole lambda p teacher initial)
    (hi : initial 1 = reflectedMeasure (initial 0)) :
    ∀ t : Real, 0 ≤ t → X.measure 1 t = reflectedMeasure (X.measure 0 t) := by
  have he : reflectionExchangePair initial = initial := by
    funext i
    fin_cases i <;> simp [reflectionExchangePair, hi, reflectedMeasure_involutive]
  intro t ht
  have hh := source_l2_ac_law_unique_of_initial_eq hu X hX
    (X.reflectionExchange hO) (hX.reflectionExchange hO) he 1 t ht
  simpa only [X.reflectionExchange_measure hO 1 t,
    show (1 : Fin 2).rev = 0 by decide] using hh

end PaperFormalization.MatrixFactorization
