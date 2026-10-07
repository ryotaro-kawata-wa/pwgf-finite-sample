import PaperFormalization.MatrixFactorization.PrimalACPotentialReconstruction
import PaperFormalization.MatrixFactorization.PrimalACOriginalEnergy

/-! # MF27: conditional global attraction for the primal AC class

Verification status and conditional scope: see `MF27_VALIDATION.md`. The full primal first variation, jointly Borel
pullback and AE AC/ODE are the existing MF25 input class. Its global law
uniqueness is explicit. Reflection covariance, the branch, canonical local
ODE, all-time caps, sharp decay, and convergence are proved internally.

The manuscript-to-primal-class/uniqueness correspondence remains unproved.
This theorem must not be renamed a completed source WGF theorem merely by
compiling it. No everywhere-classical dual gradient is assumed: a classical
on-cap representation is constructed AFTER confinement, solely to reuse the
verified MF23 tensor convergence results for the identical original laws.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

/-- Zero initial transport gives stationary ACTUAL laws, not zero fitting loss. -/
theorem PrimalACGlobalEstimates.zero_initial_stationary_laws
    {X : PrimalACCharacteristicData O a pole lambda p teacher initial}
    (H : PrimalACGlobalEstimates X)
    (hz : productAntipodalTransportSq pole (initial 0) (initial 1) = 0) :
    ∀ i t, 0 ≤ t → X.measure i t = antipodalMeasure pole := by
  have hz0 : X.transport 0 = 0 := by simpa only [X.transport_initial] using hz
  intro i t ht
  exact H.zero_laws 0 t le_rfl ht hz0 i

/-- One fixed primal trajectory: exact source support radius, sharp closed
basin, original pushed laws, true angular transport and raw tensor moments.
All-time cap and branch data occur ONLY as conclusions of this endpoint. -/
theorem primal_ac_global_attraction
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hu : PrimalACLawUnique O a pole lambda p teacher initial)
    (hi : initial 1 = reflectedMeasure (initial 0))
    (r : Real) (hc : ∀ i, TwoCapClass pole r (initial i))
    (hl : 0 < lambda) (hp : 2 < p) (hp3 : p < 3)
    (zstar : Real) (hzstar : 0 < zstar)
    (hrad : sourceRadialConstant d O a teacher*zstar^((4-p)/2) ≤ lambda/2)
    (hforce : (sourceFittingConstant d O a teacher/lambda)*zstar^((3-p)/2) ≤ r/2)
    (hinit : productAntipodalTransportSq pole (initial 0) (initial 1) ≤ zstar) :
    X.sourceBarrier < r ∧
    (∀ t : Real, 0 ≤ t → X.measure 1 t = reflectedMeasure (X.measure 0 t)) ∧
    (∀ i w, w ∈ (initial i).support → ∀ t : Real, 0 ≤ t →
      sphericalPoleRadius pole (X.characteristic i t w) ≤ X.sourceBarrier) ∧
    (∀ i t, 0 ≤ t → TwoCapClass pole r (X.measure i t)) ∧
    (∀ t : Real, 0 ≤ t →
      (∀ i : Fin 2, (X.measure i t).support ⊆ {w | sphericalPoleRadius pole w ≤ X.sourceBarrier}) ∧
      productSphericalSupportRadius pole (fun i => X.measure i t) ≤ X.sourceBarrier) ∧
    PrimalACGlobalEstimates X ∧
    Tendsto X.transport atTop (𝓝 0) ∧
    Tendsto (fun t => Real.sqrt (X.transport t)) atTop (𝓝 0) ∧
    (∀ i : Fin 2, Tendsto (fun t => sphericalWassersteinSq (X.measure i t) (antipodalMeasure pole))
      atTop (𝓝 0)) ∧
    (∀ i n, Tendsto (fun t => rawMoment (X.measure i t) n) atTop
      (𝓝 (rawMoment (antipodalMeasure pole) n))) ∧
    (∀ i n, Odd n → Tendsto (fun t => rawMoment (X.measure i t) n) atTop (𝓝 0)) ∧
    (∀ t : Real, 0 ≤ t → ∀ n, Odd n → symmetricMoment (X.measure 0 t) (X.measure 1 t) n = 0) ∧
    (∀ n, Tendsto (fun t => antisymmetricMoment (X.measure 0 t) (X.measure 1 t) n) atTop (𝓝 0)) ∧
    (∀ᵐ t ∂volume.restrict (Ioi (0 : Real)),
      (∀ i, Integrable (fun w => norm (X.gradient i t w)^2) (X.measure i t)) ∧
      HasDerivAt X.objective (-X.originalGradientEnergy t) t ∧
      deriv X.objective t ≤ -(lambda^2/4)*(X.transport t)^(p-1) ∧
      (0 < X.transport t → deriv X.objective t < 0)) ∧
    (productAntipodalTransportSq pole (initial 0) (initial 1) = 0 →
      ∀ i t, 0 ≤ t → X.measure i t = antipodalMeasure pole) := by
  have hconf := X.source_confinement hO hu hi r hc hl hp hp3 zstar hzstar hrad hforce hinit
  have H := (X.source_global_estimates hO hu hi r hc hl hp hp3 zstar hzstar hrad hforce hinit).2
  have hcaps := hconf.2.2.1
  obtain ⟨hZ, hD, hmarg, hmom, hodd, hanti⟩ := H.transport_and_moment_limits hl hp r hcaps
  exact ⟨hconf.1, X.antibranch_of_global_unique hO hu hi, hconf.2.1,
    hcaps, hconf.2.2.2, H, hZ, hD, hmarg, hmom, hodd,
    fun t ht n hn => X.symmetric_odd_moment_zero hO hu hi t ht n hn, hanti,
    H.original_energy_identity_ae hl hp r hcaps, H.zero_initial_stationary_laws⟩

end PaperFormalization.MatrixFactorization
