import PaperFormalization.MatrixFactorization.PotentialCharacteristicFirstCap
import PaperFormalization.MatrixFactorization.PotentialCharacteristicSymmetry
import PaperFormalization.MatrixFactorization.KnownBranchCharacteristicSupport
import PaperFormalization.MatrixFactorization.SupportedFlowRadiusBounds

/-! # MF23: global continuation for the explicitly represented potential flow

Execution records: `MF23_VALIDATION.md`.

This proves a conditional theorem for the precise
PotentialCharacteristicFlow class, NOT yet an unconditional theorem for every
WGF in the manuscript. Obtaining classical optimal-potential differential
data from the intended source solution remains an explicit open bridge.
Within this class, no cap, joint continuity, future branch identity or finite
uniqueness is postulated. The first-exit input is proved using the source's
sharp initial conditions and the SAME global particle maps on every prefix.
-/
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

/-- The literal printed barrier, independent of time and of a chosen prefix. -/
noncomputable def PotentialCharacteristicFlow.sourceBarrier
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial) : Real :=
  max (productSphericalSupportRadius pole initial)
    ((sourceFittingConstant d O a teacher/lambda)*
      (productAntipodalTransportSq pole (initial 0) (initial 1))^((3-p)/2))

/-- Strictness is derived from compact initial support and the two source margins. -/
theorem PotentialCharacteristicFlow.sourceBarrier_lt
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (r : Real)
    (hc : ∀ i, TwoCapClass pole r (initial i))
    (hl : 0 < lambda) (hp3 : p < 3) (zstar : Real)
    (hrad : sourceRadialConstant d O a teacher*zstar^((4-p)/2) ≤ lambda/2)
    (hforce : (sourceFittingConstant d O a teacher/lambda)*zstar^((3-p)/2) ≤ r/2)
    (hinit : productAntipodalTransportSq pole (initial 0) (initial 1) ≤ zstar) :
    X.sourceBarrier < r := by
  letI := X.initial_probability 0
  letI := X.initial_probability 1
  have hZ0 : 0 ≤ productAntipodalTransportSq pole (initial 0) (initial 1) :=
    add_nonneg (sphericalWassersteinSq_nonneg _ _) (sphericalWassersteinSq_nonneg _ _)
  have hR0 := productSphericalSupportRadius_cap_properties pole r initial hc
  have hm := source_basin_initial_margins O a teacher lambda p r zstar
    (productAntipodalTransportSq pole (initial 0) (initial 1)) hl hp3 hZ0 hinit hrad hforce
  exact max_lt hR0.2.1 (hm.2.trans_lt (by linarith [(hc 0).radius_pos]))

/-- Every good prefix improves to one fixed strict barrier. Global uniqueness
is applied only to global represented flows, via the derived branch theorem. -/
theorem PotentialCharacteristicFlow.prefix_source_barrier
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hu : PotentialCharacteristicLawUnique O a pole lambda p teacher initial)
    (hi : initial 1 = reflectedMeasure (initial 0))
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
      simpa only [sphericalPoleRadius,sphericalCap,Set.mem_setOf_eq,hpos] using hg
    · right
      simpa only [sphericalPoleRadius,sphericalCap,Set.mem_setOf_eq,hneg] using hg
  let Y := X.toCapInterval r T hT hc hin
  have hbranch : ∀ t ∈ Icc (0 : Real) T,
      Y.measure 1 t = reflectedMeasure (Y.measure 0 t) := by
    intro t ht
    exact X.antibranch_of_global_unique hO hu hi t ht.1
  have hbar := Y.exact_barrier_of_branch hO hbranch hl hp hp3 zstar hzstar hrad hforce hinit
  exact hbar.2.1

/-- All-time confinement for THIS represented class. Each current cap class,
including both half masses, is an output. The maximum-radius continuity input
of MF22 is discharged by the cap-free potential speed theorem, not by a cap
interval bound. This statement deliberately retains its representation type. -/
theorem PotentialCharacteristicFlow.source_confinement
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
    (∀ i w, w ∈ (initial i).support → ∀ t : Real, 0 ≤ t →
      sphericalPoleRadius pole (X.characteristic i t w) ≤ X.sourceBarrier) ∧
    (∀ i t, 0 ≤ t → TwoCapClass pole r (X.measure i t)) ∧
    (∀ t : Real, 0 ≤ t →
      (∀ i : Fin 2, (X.measure i t).support ⊆ {w | sphericalPoleRadius pole w ≤ X.sourceBarrier}) ∧
      productSphericalSupportRadius pole (fun i => X.measure i t) ≤ X.sourceBarrier) := by
  have hB := X.sourceBarrier_lt r hc hl hp3 zstar hrad hforce hinit
  have hj := X.characteristic_joint_continuousOn hp
  have hpref := X.prefix_source_barrier hO hu hi r hc hl hp hp3 zstar hzstar hrad hforce hinit
  have hcont := supportedFlowRadius_continuation pole initial X.initial_probability
    X.characteristic hj X.initial_map r X.sourceBarrier
    (productSphericalSupportRadius_cap_properties pole r initial hc).2.1 hB hpref
  have hcaps : ∀ i t, 0 ≤ t → TwoCapClass pole r (X.measure i t) :=
    supportedFlowRadius_continuation_map_caps pole r initial hc X.characteristic hj
      X.initial_map X.measurable_space X.sourceBarrier hB hpref
  have hs : ∀ i t, 0 ≤ t →
      (X.measure i t).support ⊆ {w | sphericalPoleRadius pole w ≤ X.sourceBarrier} :=
    supportedFlowRadius_continuation_map_support pole initial X.initial_probability
      X.characteristic hj X.initial_map X.measurable_space r X.sourceBarrier
      (productSphericalSupportRadius_cap_properties pole r initial hc).2.1 hB hpref
  refine ⟨hB,hcont.2.2,hcaps,?_⟩
  intro t ht
  refine ⟨fun i => hs i t ht,?_⟩
  exact ((productSphericalSupportRadius_cap_properties pole r
    (fun i => X.measure i t) (fun i => hcaps i t ht)).2.2.2 X.sourceBarrier).mpr
      (fun i w hw => hs i t ht hw)

end PaperFormalization.MatrixFactorization
