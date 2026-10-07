import PaperFormalization.MatrixFactorization.PotentialCharacteristicLimits
import PaperFormalization.MatrixFactorization.RawMomentTransportBounds

/-! # MF23: original raw moments along the same represented global law

Execution records: `MF23_VALIDATION.md`.

Coordinate estimates are derived from actual tensor
powers and true transport. Finite-dimensional product topology then gives
convergence of the FULL raw tensor, without an injectivity claim for moments.
The terminal theorem still displays PotentialCharacteristicFlow and its
uniqueness predicate; the manuscript-to-representation bridge is NOT hidden.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

/-- All raw orders converge to the corresponding actual target moment.
Order zero is one, not zero; only the later odd-order corollary has zero limit. -/
theorem PotentialGlobalEstimates.rawMoment_limit
    {X : PotentialCharacteristicFlow O a pole lambda p teacher initial}
    (H : PotentialGlobalEstimates X) (hl : 0 < lambda) (hp : 2 < p)
    (i : Fin 2) (n : Nat) :
    Tendsto (fun t => rawMoment (X.measure i t) n) atTop
      (𝓝 (rawMoment (antipodalMeasure pole) n)) := by
  have hsqrt : Tendsto
      (fun t => Real.sqrt (sphericalWassersteinSq (X.measure i t) (antipodalMeasure pole)))
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp (H.marginalTransport_limit hl hp i)
  have hupper : Tendsto
      (fun t => (n : Real)*Real.sqrt (sphericalWassersteinSq (X.measure i t) (antipodalMeasure pole)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := (n : Real))).mul hsqrt
  -- The standard homeomorphism transfers convergence to the coordinate product.
  apply (PiLp.homeomorph 2 (fun _ : Fin n → Fin d => Real)).isInducing.tendsto_nhds_iff.mpr
  change Tendsto (fun t => fun I : Fin n → Fin d => rawMoment (X.measure i t) n I)
    atTop (𝓝 (fun I : Fin n → Fin d => rawMoment (antipodalMeasure pole) n I))
  apply tendsto_pi_nhds.mpr
  intro I
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun t => norm_nonneg _)) _ hupper
  filter_upwards [eventually_ge_atTop (0 : Real)] with t ht
  letI := X.measure_probability i t ht
  exact rawMoment_coordinate_transport_bound (X.measure i t) (antipodalMeasure pole) I

theorem PotentialGlobalEstimates.odd_rawMoment_limit
    {X : PotentialCharacteristicFlow O a pole lambda p teacher initial}
    (H : PotentialGlobalEstimates X) (hl : 0 < lambda) (hp : 2 < p)
    (i : Fin 2) (n : Nat) (hn : Odd n) :
    Tendsto (fun t => rawMoment (X.measure i t) n) atTop (𝓝 0) := by
  simpa only [rawMoment_antipodal_odd pole n hn] using H.rawMoment_limit hl hp i n

/-- Both marginals converge to the SAME target, so their antisymmetric raw
moment difference vanishes at every fixed order, not only active orders. -/
theorem PotentialGlobalEstimates.antisymmetricMoment_limit
    {X : PotentialCharacteristicFlow O a pole lambda p teacher initial}
    (H : PotentialGlobalEstimates X) (hl : 0 < lambda) (hp : 2 < p) (n : Nat) :
    Tendsto (fun t => antisymmetricMoment (X.measure 0 t) (X.measure 1 t) n)
      atTop (𝓝 0) := by
  have hh := (tendsto_const_nhds (x := (1/2 : Real))).smul
    ((H.rawMoment_limit hl hp 0 n).sub (H.rawMoment_limit hl hp 1 n))
  simpa only [antisymmetricMoment,sub_self,smul_zero] using hh

/-- Exact vanishing of symmetric ODD moments is derived from GLOBAL uniqueness,
not from an injectivity assertion about a finite tensor representation. -/
theorem PotentialCharacteristicFlow.symmetric_odd_moment_zero
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    (hO : ∀ n ∈ O, Odd n)
    (hu : PotentialCharacteristicLawUnique O a pole lambda p teacher initial)
    (hi : initial 1 = reflectedMeasure (initial 0))
    (t : Real) (ht : 0 ≤ t) (n : Nat) (hn : Odd n) :
    symmetricMoment (X.measure 0 t) (X.measure 1 t) n = 0 := by
  letI := X.measure_probability 0 t ht
  rw [X.antibranch_of_global_unique hO hu hi t ht]
  exact reflected_branch_symmetric_zero (X.measure 0 t) n hn

/-- Conditional end-to-end theorem for the explicit optimal-potential global
class. Initial data supply confinement, sharp dynamics and convergence. The
representation and uniqueness inputs remain visible and must NOT be relabeled
as a completed proof of the manuscript's cap-free WGF formulation.
-/
theorem represented_global_attraction
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hu : PotentialCharacteristicLawUnique O a pole lambda p teacher initial)
    (hi : initial 1 = reflectedMeasure (initial 0))
    (r : Real) (hc : ∀ i, TwoCapClass pole r (initial i))
    (hl : 0 < lambda) (hp : 2 < p) (hp3 : p < 3)
    (zstar : Real) (hzstar : 0 < zstar)
    (hrad : sourceRadialConstant d O a teacher*zstar^((4-p)/2) ≤ lambda/2)
    (hforce : (sourceFittingConstant d O a teacher/lambda)*zstar^((3-p)/2) ≤ r/2)
    (hinit : productAntipodalTransportSq pole (initial 0) (initial 1) ≤ zstar) :
    X.sourceBarrier < r ∧
    (∀ i t, 0 ≤ t → TwoCapClass pole r (X.measure i t)) ∧
    (∀ t : Real, 0 ≤ t →
      (∀ i : Fin 2, (X.measure i t).support ⊆ {w | sphericalPoleRadius pole w ≤ X.sourceBarrier}) ∧
      productSphericalSupportRadius pole (fun i => X.measure i t) ≤ X.sourceBarrier) ∧
    PotentialGlobalEstimates X ∧
    Tendsto X.transport atTop (𝓝 0) ∧
    Tendsto (fun t => Real.sqrt (X.transport t)) atTop (𝓝 0) ∧
    (∀ i n, Odd n → Tendsto (fun t => rawMoment (X.measure i t) n) atTop (𝓝 0)) ∧
    (∀ t : Real, 0 ≤ t → ∀ n, Odd n → symmetricMoment (X.measure 0 t) (X.measure 1 t) n = 0) ∧
    (∀ n, Tendsto (fun t => antisymmetricMoment (X.measure 0 t) (X.measure 1 t) n) atTop (𝓝 0)) := by
  have hcglobal := X.source_confinement hO hu hi r hc hl hp hp3 zstar hzstar hrad hforce hinit
  have H := (X.source_global_estimates hO hu hi r hc hl hp hp3 zstar hzstar hrad hforce hinit).2
  exact ⟨hcglobal.1,hcglobal.2.2.1,hcglobal.2.2.2,H,H.transport_limit hl hp,
    H.productDistance_limit hl hp,fun i n hn => H.odd_rawMoment_limit hl hp i n hn,
    fun t ht n hn => X.symmetric_odd_moment_zero hO hu hi t ht n hn,
    H.antisymmetricMoment_limit hl hp⟩

end PaperFormalization.MatrixFactorization
