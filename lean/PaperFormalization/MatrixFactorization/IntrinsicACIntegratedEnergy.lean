import PaperFormalization.MatrixFactorization.IntrinsicACGlobalAttraction
import PaperFormalization.MatrixFactorization.PrimalACIntegratedEnergy
import PaperFormalization.MatrixFactorization.PrimalACSpacetimeTests

/-! # MF31: accumulated original-gradient energy from the source initial basin

Source-class uniqueness and the original sharp initial conditions supply
all-time caps internally. The accumulated energy identity then applies to
the same original measurable gradient at every signed nonnegative time pair.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

/-- Exact time-integrated dissipation and full-objective AC, with no supplied
future cap certificate or equality of exceptional gradient representatives. -/
theorem source_l2_ac_integrated_energy
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hX : X.HasSourceL2FirstVariation)
    (hu : SourceL2ACLawUnique O a pole lambda p teacher initial)
    (hi : initial 1 = reflectedMeasure (initial 0))
    (r : Real) (hc : ∀ i, TwoCapClass pole r (initial i))
    (hl : 0 < lambda) (hp : 2 < p) (hp3 : p < 3)
    (zstar : Real) (hzstar : 0 < zstar)
    (hrad : sourceRadialConstant d O a teacher*zstar^((4-p)/2) ≤ lambda/2)
    (hforce : (sourceFittingConstant d O a teacher/lambda)*zstar^((3-p)/2) ≤ r/2)
    (hinit : productAntipodalTransportSq pole (initial 0) (initial 1) ≤ zstar) :
    ∀ s t : Real, 0 ≤ s → 0 ≤ t →
      IntervalIntegrable X.originalGradientEnergy volume s t ∧
      X.objective t + (∫ u in s..t, X.originalGradientEnergy u) = X.objective s ∧
      AbsolutelyContinuousOnInterval X.objective s t := by
  have hcaps := (X.source_confinement_of_branch hO
    (X.antibranch_of_source_unique hX hO hu hi) r hc hl hp hp3 zstar hzstar hrad hforce hinit).2.2.1
  intro s t hs ht
  have H := X.integrated_original_energy hl.le hp r hcaps s t hs ht
  refine ⟨H.1, ?_, X.objective_ac_of_caps hl.le hp r hcaps s t hs ht⟩
  rw [H.2]
  ring

end PaperFormalization.MatrixFactorization
