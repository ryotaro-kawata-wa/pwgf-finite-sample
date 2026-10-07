import PaperFormalization.MatrixFactorization.PrimalACGlobalEstimates
import PaperFormalization.MatrixFactorization.PotentialCharacteristicMomentLimits

/-! # MF27: recover a classical representation AFTER primal confinement

Verification status and conditional scope: see `MF27_VALIDATION.md`. The input caps of this helper are discharged
by PrimalACCharacteristicData.source_confinement in the final theorem. Thus
classical dual data are constructed only after global confinement, not
assumed in order to prove it. This is a one-way reconstruction along a
confined trajectory, not equivalence of the unrestricted two solution classes.
It lets us reuse MF23's already checked transport and tensor-limit theorems.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

/-- Construct optimal on-cap dual data and the classical ODE for the ORIGINAL
maps. An arbitrary stored primal representative need not agree at null points. -/
noncomputable def PrimalACCharacteristicData.toPotentialAfterConfinement
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r : Real) (hcaps : ∀ i t, 0 ≤ t → TwoCapClass pole r (X.measure i t)) :
    PotentialCharacteristicFlow O a pole lambda p teacher initial where
  initial_probability := X.initial_probability
  characteristic := X.characteristic
  measurable_space := fun i t _ => X.measurable_space i t
  continuous_space := X.continuous_space
  continuous_time := X.supported_time_continuity hl hp
  initial_map := X.initial_map
  dual := fun i t ht => AntipodalGradientData.onCaps pole r (X.measure i t) (hcaps i t ht.le)
  ode := by
    intro i w hw t ht
    change HasDerivAt (fun u => (X.characteristic i u w).val)
      (-X.canonicalPullback i t w) t
    exact X.canonical_ode_on_prefix hl hp r (t+1) (by linarith)
      (fun j u hu => hcaps j u hu.1) i w hw t ⟨ht, by linarith⟩

@[simp] theorem PrimalACCharacteristicData.toPotentialAfterConfinement_measure
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r : Real) (hcaps : ∀ i t, 0 ≤ t → TwoCapClass pole r (X.measure i t)) :
    (X.toPotentialAfterConfinement hl hp r hcaps).measure = X.measure := rfl

@[simp] theorem PrimalACCharacteristicData.toPotentialAfterConfinement_characteristic
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r : Real) (hcaps : ∀ i t, 0 ≤ t → TwoCapClass pole r (X.measure i t)) :
    (X.toPotentialAfterConfinement hl hp r hcaps).characteristic = X.characteristic := rfl

/-- Transfer conclusions between the definitionally identical observables.
No uniqueness premise for the potential class occurs in this adapter. -/
theorem PrimalACGlobalEstimates.toPotentialEstimates
    {X : PrimalACCharacteristicData O a pole lambda p teacher initial}
    (H : PrimalACGlobalEstimates X)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r : Real) (hcaps : ∀ i t, 0 ≤ t → TwoCapClass pole r (X.measure i t)) :
    PotentialGlobalEstimates (X.toPotentialAfterConfinement hl hp r hcaps) := by
  exact ⟨H.transport_antitone, H.objective_antitone, H.decay,
    H.gradient_integrable, H.energy_derivative, H.transport_differential,
    H.energy_differential, H.zero_laws⟩

/-- Reuse all existing limit arguments on the same pushed laws and every tensor
order. In particular the degree-zero target moment is not replaced by zero. -/
theorem PrimalACGlobalEstimates.transport_and_moment_limits
    {X : PrimalACCharacteristicData O a pole lambda p teacher initial}
    (H : PrimalACGlobalEstimates X)
    [IsProbabilityMeasure teacher] (hl : 0 < lambda) (hp : 2 < p)
    (r : Real) (hcaps : ∀ i t, 0 ≤ t → TwoCapClass pole r (X.measure i t)) :
    Tendsto X.transport atTop (𝓝 0) ∧
    Tendsto (fun t => Real.sqrt (X.transport t)) atTop (𝓝 0) ∧
    (∀ i : Fin 2, Tendsto (fun t => sphericalWassersteinSq (X.measure i t) (antipodalMeasure pole))
      atTop (𝓝 0)) ∧
    (∀ i n, Tendsto (fun t => rawMoment (X.measure i t) n) atTop
      (𝓝 (rawMoment (antipodalMeasure pole) n))) ∧
    (∀ i n, Odd n → Tendsto (fun t => rawMoment (X.measure i t) n) atTop (𝓝 0)) ∧
    (∀ n, Tendsto (fun t => antisymmetricMoment (X.measure 0 t) (X.measure 1 t) n)
      atTop (𝓝 0)) := by
  have HP := H.toPotentialEstimates hl.le hp r hcaps
  exact ⟨HP.transport_limit hl hp, HP.productDistance_limit hl hp,
    HP.marginalTransport_limit hl hp, HP.rawMoment_limit hl hp,
    HP.odd_rawMoment_limit hl hp, HP.antisymmetricMoment_limit hl hp⟩

end PaperFormalization.MatrixFactorization
