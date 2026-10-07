import PaperFormalization.MatrixFactorization.PrimalACGlobalSymmetry
import PaperFormalization.MatrixFactorization.KnownBranchCharacteristicSupport
import PaperFormalization.MatrixFactorization.SupportedFlowRadiusBounds

/-! # MF27: confinement for the unchanged primal AC class

Verification status and conditional scope: see `MF27_VALIDATION.md`. All-time caps, future branch identities,
supported regularity, and finite uniqueness are NOT inputs. MF25 derives
joint continuity without caps; MF26 constructs a literal cap restriction on
each good prefix; MF21/MF23 provide the sharp known-branch barrier; MF22 rules
out exit. Original-source class correspondence remains a separate obligation.
-/
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

/-- The exact source initial support supremum and forcing scale; no prefix parameter. -/
noncomputable def PrimalACCharacteristicData.sourceBarrier
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial) : Real :=
  max (productSphericalSupportRadius pole initial)
    ((sourceFittingConstant d O a teacher/lambda)*
      (productAntipodalTransportSq pole (initial 0) (initial 1))^((3-p)/2))

theorem PrimalACCharacteristicData.sourceBarrier_lt
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
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

/-- The same original paths improve every good prefix to one strict barrier.
Their branch identity is obtained from global primal-law uniqueness. -/
theorem PrimalACCharacteristicData.prefix_source_barrier
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hu : PrimalACLawUnique O a pole lambda p teacher initial)
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
      simpa only [sphericalPoleRadius, sphericalCap, Set.mem_setOf_eq, hpos] using hg
    · right
      simpa only [sphericalPoleRadius, sphericalCap, Set.mem_setOf_eq, hneg] using hg
  let Y := X.classicalRestrictionOfGoodPrefix hl.le hp r T hT hc hin
  have hbranch : ∀ t ∈ Icc (0 : Real) T,
      Y.measure 1 t = reflectedMeasure (Y.measure 0 t) := by
    intro t ht
    exact X.antibranch_of_global_unique hO hu hi t ht.1
  have hbar := Y.exact_barrier_of_branch hO hbranch hl hp hp3 zstar hzstar hrad hforce hinit
  exact hbar.2.1

/-- Conditional source-shaped global confinement for the primal AC class.
The exact masses and complete closed supports are conclusions, not premises. -/
theorem PrimalACCharacteristicData.source_confinement
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
    (∀ i w, w ∈ (initial i).support → ∀ t : Real, 0 ≤ t →
      sphericalPoleRadius pole (X.characteristic i t w) ≤ X.sourceBarrier) ∧
    (∀ i t, 0 ≤ t → TwoCapClass pole r (X.measure i t)) ∧
    (∀ t : Real, 0 ≤ t →
      (∀ i : Fin 2, (X.measure i t).support ⊆ {w | sphericalPoleRadius pole w ≤ X.sourceBarrier}) ∧
      productSphericalSupportRadius pole (fun i => X.measure i t) ≤ X.sourceBarrier) := by
  have hB := X.sourceBarrier_lt r hc hl hp3 zstar hrad hforce hinit
  have hj := X.supported_joint_continuity hl.le hp
  have hpref := X.prefix_source_barrier hO hu hi r hc hl hp hp3 zstar hzstar hrad hforce hinit
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

end PaperFormalization.MatrixFactorization
