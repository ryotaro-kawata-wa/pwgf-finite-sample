import PaperFormalization.MatrixFactorization.IntrinsicACSourceClass
import PaperFormalization.MatrixFactorization.PrimalACKnownBranch
import PaperFormalization.MatrixFactorization.PrimalACWeakContinuity

/-! # MF30: sharp global attraction using uniqueness only in the source class

The source L2 first variation is preserved under reflection of the actual
whole AC trajectory. Original-class uniqueness then supplies its branch
identity. The known-branch continuation and convergence proofs operate on
this same trajectory. No uniqueness of all bounded-test primal competitors
is inferred, and no finite-interval uniqueness is assumed.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

/-- One fixed primal trajectory: exact source support radius, sharp closed
basin, original pushed laws, true angular transport and raw tensor moments.
The actual reflected competitor remains inside the intrinsic source class.
Neither a future branch identity nor uniqueness of the larger primal class
is an input. -/
theorem source_l2_ac_global_attraction
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
  exact primal_ac_global_attraction_of_branch X hO
    (X.antibranch_of_source_unique hX hO hu hi) r hc hl hp hp3 zstar hzstar hrad hforce hinit

end PaperFormalization.MatrixFactorization
