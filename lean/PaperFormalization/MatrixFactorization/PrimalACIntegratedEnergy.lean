import PaperFormalization.MatrixFactorization.PrimalACOriginalEnergy
import PaperFormalization.MatrixFactorization.SphericalCharacteristicIntegratedEnergy
import PaperFormalization.MatrixFactorization.PrimalACIntegralForm

/-! # MF31: integrated energy for the same original primal AC trajectory

MF17's proved finite-interval energy identity is reused on literal cap
restrictions. Current-law AE equality then transfers both the integral and
true time integrability to the original measurable gradient. No values at
exceptional times are forced to match the canonical field.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

theorem PrimalACCharacteristicData.originalGradientEnergy_nonneg
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial) (t : Real) :
    0 ≤ X.originalGradientEnergy t :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))

/-- On an ordered interval, the original representative has precisely the
same integrated dissipation as the canonical field, with genuine L1 time control. -/
theorem PrimalACCharacteristicData.integrated_original_energy_ordered
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r : Real) (hcaps : ∀ i t, 0 ≤ t → TwoCapClass pole r (X.measure i t))
    (s t : Real) (hs : 0 ≤ s) (hst : s ≤ t) :
    IntervalIntegrable X.originalGradientEnergy volume s t ∧
    (∫ u in s..t, X.originalGradientEnergy u) = X.objective s - X.objective t := by
  have ht := hs.trans hst
  let Y := X.toSphericalCapInterval hl hp r t ht (fun i u hu => hcaps i u hu.1)
  have hint : IntervalIntegrable X.gradientEnergy volume s t :=
    Y.gradientEnergy_intervalIntegrable hp s t hs hst le_rfl
  have hid : (∫ u in s..t, X.gradientEnergy u) = X.objective s - X.objective t :=
    Y.integrated_energy hp s t hs hst le_rfl
  have he := ae_nonnegative_to_segment hs ht
    ((X.originalGradientEnergy_eq_ae hl hp r hcaps).mono (fun u hu => hu.2.symm))
  have heq : X.gradientEnergy =ᵐ[volume.restrict (uIoc s t)] X.originalGradientEnergy := by
    apply (ae_restrict_iff' measurableSet_uIoc).mpr
    exact he.mono (fun u hu hmem => hu (uIoc_subset_uIcc hmem))
  exact ⟨hint.congr_ae heq, (intervalIntegral.integral_congr_ae_restrict heq).symm.trans hid⟩

/-- Signed endpoint form includes equal and reversed nonnegative times. -/
theorem PrimalACCharacteristicData.integrated_original_energy
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r : Real) (hcaps : ∀ i t, 0 ≤ t → TwoCapClass pole r (X.measure i t))
    (s t : Real) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    IntervalIntegrable X.originalGradientEnergy volume s t ∧
    (∫ u in s..t, X.originalGradientEnergy u) = X.objective s - X.objective t := by
  rcases le_total s t with hst | hts
  · exact X.integrated_original_energy_ordered hl hp r hcaps s t hs hst
  · have H := X.integrated_original_energy_ordered hl hp r hcaps t s ht hts
    refine ⟨H.1.symm, ?_⟩
    rw [intervalIntegral.integral_symm, H.2, neg_sub]

/-- Full-objective AC is a consequence of the integral identity. -/
theorem PrimalACCharacteristicData.objective_ac_of_caps
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r : Real) (hcaps : ∀ i t, 0 ≤ t → TwoCapClass pole r (X.measure i t))
    (s t : Real) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    AbsolutelyContinuousOnInterval X.objective s t := by
  apply integral_characteristic_ac_all_segments (v := X.originalGradientEnergy) ?_ s t hs ht
  intro n
  refine ⟨(X.integrated_original_energy hl hp r hcaps 0 n le_rfl (Nat.cast_nonneg n)).1, ?_⟩
  intro u hu
  have he := (X.integrated_original_energy hl hp r hcaps 0 u le_rfl hu.1).2
  linarith

/-- The actual initial objective equals the current one plus accumulated
squared original-gradient energy. No initial stationarity is assumed. -/
theorem PrimalACCharacteristicData.original_energy_balance
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r : Real) (hcaps : ∀ i t, 0 ≤ t → TwoCapClass pole r (X.measure i t))
    (t : Real) (ht : 0 ≤ t) :
    X.objective t + (∫ u in 0..t, X.originalGradientEnergy u) = X.objective 0 := by
  rw [(X.integrated_original_energy hl hp r hcaps 0 t le_rfl ht).2]
  ring

end PaperFormalization.MatrixFactorization
