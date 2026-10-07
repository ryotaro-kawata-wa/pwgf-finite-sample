import PaperFormalization.MatrixFactorization.PrimalACGlobalEstimates

/-! # MF27: return dissipation to the ORIGINAL primal gradient representative

Verification status and conditional scope: see `MF27_VALIDATION.md`. Canonical gradients are used for the classical
local ODE, but the source states energy using its L2 gradient. After caps have
been proved, primal uniqueness identifies these fields only under the current
law and at the original AE times. Genuine norm-square integrability is retained.
No values of the stored representative are forced at exceptional times/points.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

/-- Only used with proved integrability at the AE times in the following results. -/
noncomputable def PrimalACCharacteristicData.originalGradientEnergy
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial) (t : Real) : Real :=
  ∑ i : Fin 2, ∫ w, norm (X.gradient i t w)^2 ∂X.measure i t

/-- The two energies agree at exactly the source's AE first-variation times. -/
theorem PrimalACCharacteristicData.originalGradientEnergy_eq_ae
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r : Real) (hcaps : ∀ i t, 0 ≤ t → TwoCapClass pole r (X.measure i t)) :
    ∀ᵐ t ∂volume.restrict (Ici (0 : Real)),
      (∀ i, Integrable (fun w => norm (X.gradient i t w)^2) (X.measure i t)) ∧
      X.originalGradientEnergy t = X.gradientEnergy t := by
  filter_upwards [X.first_variation, ae_restrict_mem measurableSet_Ici] with t ht ht0
  have he := (source_primal_gradient_statewise O a pole lambda p hl hp
    (fun i => X.measure i t) (fun i => X.measure_probability i t) teacher
    (fun i => X.gradient i t) ht).2.2 r (fun i => hcaps i t ht0)
  have hi := fun i => (ht i).norm_sq_integrable
  refine ⟨hi, ?_⟩
  unfold PrimalACCharacteristicData.originalGradientEnergy PrimalACCharacteristicData.gradientEnergy
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [he i] with w hw
  rw [hw]

/-- The source's representative, not an artificially everywhere-defined
canonical replacement, satisfies the original AE energy identity. Time zero
is omitted only as a Lebesgue-null endpoint; no endpoint derivative is added. -/
theorem PrimalACGlobalEstimates.original_energy_identity_ae
    {X : PrimalACCharacteristicData O a pole lambda p teacher initial}
    (H : PrimalACGlobalEstimates X)
    [IsProbabilityMeasure teacher] (hl : 0 < lambda) (hp : 2 < p)
    (r : Real) (hcaps : ∀ i t, 0 ≤ t → TwoCapClass pole r (X.measure i t)) :
    ∀ᵐ t ∂volume.restrict (Ioi (0 : Real)),
      (∀ i, Integrable (fun w => norm (X.gradient i t w)^2) (X.measure i t)) ∧
      HasDerivAt X.objective (-X.originalGradientEnergy t) t ∧
      deriv X.objective t ≤ -(lambda^2/4)*(X.transport t)^(p-1) ∧
      (0 < X.transport t → deriv X.objective t < 0) := by
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  have he := (ae_restrict_iff' measurableSet_Ici).mp
    (X.originalGradientEnergy_eq_ae hl.le hp r hcaps)
  filter_upwards [he] with t ht
  intro ht0
  have htpos : 0 < t := ht0
  obtain ⟨hint, heq⟩ := ht (show t ∈ Ici (0 : Real) from htpos.le)
  have hdiff := H.energy_differential t htpos
  refine ⟨hint, ?_, hdiff, ?_⟩
  · rw [heq]
    exact H.energy_derivative t htpos
  · intro hz
    exact hdiff.trans_lt (mul_neg_of_neg_of_pos
      (by nlinarith [sq_pos_of_pos hl]) (Real.rpow_pos_of_pos hz _))

end PaperFormalization.MatrixFactorization
