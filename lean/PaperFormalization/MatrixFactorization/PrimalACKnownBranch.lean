import PaperFormalization.MatrixFactorization.PrimalACGlobalAttraction

/-! # MF30: reuse global estimates with a branch proved in the source class

These adapters factor the analytic argument through its actual input, the
branch identity. They do not infer uniqueness of the larger primal class
from uniqueness in a narrower intrinsic source class, nor finite-interval
uniqueness from global uniqueness. All support barriers and cap conclusions
are still proved by the existing same-trajectory continuation argument.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

/-- The same original paths improve every good prefix to one strict barrier.
The supplied identity may come from uniqueness in a narrower source class. -/
theorem PrimalACCharacteristicData.prefix_source_barrier_of_branch
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hb : ∀ t : Real, 0 ≤ t → X.measure 1 t = reflectedMeasure (X.measure 0 t))
    (r : Real) (hc : ∀ i, TwoCapClass pole r (initial i))
    (hl : 0 < lambda) (hp : 2 < p) (hp3 : p < 3)
    (zstar : Real) (hzstar : 0 < zstar)
    (hrad : sourceRadialConstant d O a teacher*zstar^((4-p)/2) ≤ lambda/2)
    (hforce : (sourceFittingConstant d O a teacher/lambda)*zstar^((3-p)/2) ≤ r/2)
    (hinit : productAntipodalTransportSq pole (initial 0) (initial 1) ≤ zstar)
    (T : Real) (hT : 0 ≤ T)
    (hgood : ∀ i w, w ∈ (initial i).support → ∀ t ∈ Icc (0 : Real) T,
      sphericalPoleRadius pole (X.characteristic i t w) < r) :
    ∀ i w, w ∈ (initial i).support → ∀ t ∈ Icc (0 : Real) T,
      sphericalPoleRadius pole (X.characteristic i t w) ≤ X.sourceBarrier := by
  have hin : ∀ i w, w ∈ (initial i).support → ∀ t ∈ Icc (0 : Real) T,
      X.characteristic i t w ∈ sphericalCap pole r ∪ sphericalCap (reflect pole) r := by
    intro i w hw t ht
    have hg := hgood i w hw t ht
    rcases assignedPole_mem pole (X.characteristic i t w) with hpos | hneg
    · left
      simpa only [sphericalPoleRadius, sphericalCap, Set.mem_setOf_eq, hpos] using hg
    · right
      simpa only [sphericalPoleRadius, sphericalCap, Set.mem_setOf_eq, hneg] using hg
  let Y := X.classicalRestrictionOfGoodPrefix hl.le hp r T hT hc hin
  have hbranch : ∀ t ∈ Icc (0 : Real) T,
      Y.measure 1 t = reflectedMeasure (Y.measure 0 t) := by
    intro t ht
    exact hb t ht.1
  have hbar := Y.exact_barrier_of_branch hO hbranch hl hp hp3 zstar hzstar hrad hforce hinit
  exact hbar.2.1

/-- Source-shaped confinement from an already established branch identity.
The exact masses and complete closed supports are conclusions, not premises. -/
theorem PrimalACCharacteristicData.source_confinement_of_branch
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hb : ∀ t : Real, 0 ≤ t → X.measure 1 t = reflectedMeasure (X.measure 0 t))
    (r : Real) (hc : ∀ i, TwoCapClass pole r (initial i))
    (hl : 0 < lambda) (hp : 2 < p) (hp3 : p < 3)
    (zstar : Real) (hzstar : 0 < zstar)
    (hrad : sourceRadialConstant d O a teacher*zstar^((4-p)/2) ≤ lambda/2)
    (hforce : (sourceFittingConstant d O a teacher/lambda)*zstar^((3-p)/2) ≤ r/2)
    (hinit : productAntipodalTransportSq pole (initial 0) (initial 1) ≤ zstar) :
    X.sourceBarrier < r ∧
    (∀ i w, w ∈ (initial i).support → ∀ t : Real, 0 ≤ t →
      sphericalPoleRadius pole (X.characteristic i t w) ≤ X.sourceBarrier) ∧
    (∀ i t, 0 ≤ t → TwoCapClass pole r (X.measure i t)) ∧
    (∀ t : Real, 0 ≤ t →
      (∀ i : Fin 2, (X.measure i t).support ⊆ {w | sphericalPoleRadius pole w ≤ X.sourceBarrier}) ∧
      productSphericalSupportRadius pole (fun i => X.measure i t) ≤ X.sourceBarrier) := by
  have hB := X.sourceBarrier_lt r hc hl hp3 zstar hrad hforce hinit
  have hj := X.supported_joint_continuity hl.le hp
  have hpref := X.prefix_source_barrier_of_branch hO hb r hc hl hp hp3 zstar hzstar hrad hforce hinit
  have hm : ∀ i t, 0 ≤ t → Measurable (X.characteristic i t) :=
    fun i t _ => X.measurable_space i t
  have hcont := supportedFlowRadius_continuation pole initial X.initial_probability
    X.characteristic hj X.initial_map r X.sourceBarrier
    (productSphericalSupportRadius_cap_properties pole r initial hc).2.1 hB hpref
  have hcaps : ∀ i t, 0 ≤ t → TwoCapClass pole r (X.measure i t) :=
    supportedFlowRadius_continuation_map_caps pole r initial hc X.characteristic hj
      X.initial_map hm X.sourceBarrier hB hpref
  have hs : ∀ i t, 0 ≤ t →
      (X.measure i t).support ⊆ {w | sphericalPoleRadius pole w ≤ X.sourceBarrier} :=
    supportedFlowRadius_continuation_map_support pole initial X.initial_probability
      X.characteristic hj X.initial_map hm r X.sourceBarrier
      (productSphericalSupportRadius_cap_properties pole r initial hc).2.1 hB hpref
  refine ⟨hB, hcont.2.2, hcaps, ?_⟩
  intro t ht
  refine ⟨fun i => hs i t ht, ?_⟩
  exact ((productSphericalSupportRadius_cap_properties pole r
    (fun i => X.measure i t) (fun i => hcaps i t ht)).2.2.2 X.sourceBarrier).mpr
      (fun i w hw => hs i t ht hw)

/-- Initial source margins and an established branch identity supply
both confinement and every dynamical estimate. No potential data are supplied. -/
theorem PrimalACCharacteristicData.source_global_estimates_of_branch
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hb : ∀ t : Real, 0 ≤ t → X.measure 1 t = reflectedMeasure (X.measure 0 t))
    (r : Real) (hc : ∀ i, TwoCapClass pole r (initial i))
    (hl : 0 < lambda) (hp : 2 < p) (hp3 : p < 3)
    (zstar : Real) (hzstar : 0 < zstar)
    (hrad : sourceRadialConstant d O a teacher*zstar^((4-p)/2) ≤ lambda/2)
    (hforce : (sourceFittingConstant d O a teacher/lambda)*zstar^((3-p)/2) ≤ r/2)
    (hinit : productAntipodalTransportSq pole (initial 0) (initial 1) ≤ zstar) :
    (∀ i t, 0 ≤ t → TwoCapClass pole r (X.measure i t)) ∧ PrimalACGlobalEstimates X := by
  have hconf := X.source_confinement_of_branch hO hb r hc hl hp hp3 zstar hzstar hrad hforce hinit
  have hcaps := hconf.2.2.1
  have hZ0 : 0 ≤ productAntipodalTransportSq pole (initial 0) (initial 1) := by
    simpa only [X.transport_initial] using X.transport_nonneg 0
  have hm := source_basin_initial_margins O a teacher lambda p r zstar
    (productAntipodalTransportSq pole (initial 0) (initial 1)) hl hp3 hZ0 hinit hrad hforce
  exact ⟨hcaps, X.global_estimates_of_caps hO r hcaps
    hb hl hp (by linarith) hm.1⟩

/-- One fixed primal trajectory: exact source support radius, sharp closed
basin, original pushed laws, true angular transport and raw tensor moments.
All-time caps remain outputs; the branch identity is explicit so callers need
not assert uniqueness over unrelated larger classes. -/
theorem primal_ac_global_attraction_of_branch
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hb : ∀ t : Real, 0 ≤ t → X.measure 1 t = reflectedMeasure (X.measure 0 t))
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
  have hconf := X.source_confinement_of_branch hO hb r hc hl hp hp3 zstar hzstar hrad hforce hinit
  have H := (X.source_global_estimates_of_branch hO hb r hc hl hp hp3 zstar hzstar hrad hforce hinit).2
  have hcaps := hconf.2.2.1
  obtain ⟨hZ, hD, hmarg, hmom, hodd, hanti⟩ := H.transport_and_moment_limits hl hp r hcaps
  have hsym : ∀ t : Real, 0 ≤ t → ∀ n, Odd n →
      symmetricMoment (X.measure 0 t) (X.measure 1 t) n = 0 := by
    intro t ht n hn
    letI := X.measure_probability 0 t
    rw [hb t ht]
    exact reflected_branch_symmetric_zero (X.measure 0 t) n hn
  exact ⟨hconf.1, hb, hconf.2.1,
    hcaps, hconf.2.2.2, H, hZ, hD, hmarg, hmom, hodd,
    hsym, hanti,
    H.original_energy_identity_ae hl hp r hcaps, H.zero_initial_stationary_laws⟩

end PaperFormalization.MatrixFactorization
