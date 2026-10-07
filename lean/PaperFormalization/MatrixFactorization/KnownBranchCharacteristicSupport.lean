import PaperFormalization.MatrixFactorization.KnownBranchCharacteristicDecay
import PaperFormalization.MatrixFactorization.SourceExactSupportBarrier

/-! # MF23: the sharp support barrier with an independently proved branch

Execution records: `MF23_VALIDATION.md`.

Only the use of branch invariance is factored out of the
verified interval argument. The source Cstar, Lfit, closed zstar conditions,
actual initial support supremum and original measures are unchanged. At the
global endpoint the branch is derived, not assumed for positive times.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}

/-- A half-cost barrier avoids differentiating the unsquared radius at a pole. -/
theorem SphericalCharacteristicSolution.particle_barrier_of_branch
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hb : ∀ t ∈ Icc (0 : Real) T, X.measure 1 t = reflectedMeasure (X.measure 0 t))
    (hl : 0 < lambda) (hp : 2 < p) (hp3 : p < 3)
    (hsmall0 : sourceRadialConstant d O a teacher*
      (productAntipodalTransportSq pole (initial 0) (initial 1))^((4-p)/2) ≤ lambda/2)
    (R0 : Real) (hR0 : 0 ≤ R0)
    (hbound : ∀ i w, w ∈ (initial i).support → sphericalPoleRadius pole w ≤ R0)
    (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (initial i).support)
    (t : Real) (ht : t ∈ Icc (0 : Real) T) :
    sphericalPoleRadius pole (X.characteristic i t w) ≤
      max R0 ((sourceFittingConstant d O a teacher/lambda)*
        (productAntipodalTransportSq pole (initial 0) (initial 1))^((3-p)/2)) := by
  let Z0 := productAntipodalTransportSq pole (initial 0) (initial 1)
  let R := max R0 ((sourceFittingConstant d O a teacher/lambda)*Z0^((3-p)/2))
  have hR : 0 ≤ R := hR0.trans (le_max_left _ _)
  have hper := X.transport_persists_of_branch hO hb hl hp (by linarith : p < 4) hsmall0
  have hc : ContinuousOn (fun s => assignedCost pole (X.characteristic i s w)) (Icc 0 T) :=
    (assignedCost_continuous pole).comp_continuousOn (X.continuous_time i w hw)
  have hd : ∀ s ∈ Ioo (0 : Real) T,
      DifferentiableAt Real (fun u => assignedCost pole (X.characteristic i u w)) s :=
    fun s hs => (X.assignedCost_hasDerivAt i w hw s hs).differentiableAt
  have hi : assignedCost pole (X.characteristic i 0 w) ≤ R^2/2 := by
    rw [X.initial_map i w hw,assignedCost_eq_half_poleRadius_sq]
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (sphericalPoleRadius_nonneg pole w)
        ((hbound i w hw).trans (le_max_left _ _)) 2) (by norm_num)
  have hbar := scalar_support_barrier hc hd hi (fun s hs hlarge => by
    have hsc : s ∈ Icc (0 : Real) T := ⟨hs.1.le,hs.2.le⟩
    have hr : 0 ≤ sphericalPoleRadius pole (X.characteristic i s w) := sphericalPoleRadius_nonneg _ _
    have hRcur : R ≤ sphericalPoleRadius pole (X.characteristic i s w) := by
      rw [assignedCost_eq_half_poleRadius_sq] at hlarge
      by_contra hn
      have hsq := pow_le_pow_left₀ hr (le_of_lt (lt_of_not_ge hn)) 2
      nlinarith
    apply (X.particle_cost_bound_of_branch hO hb i w hw s hs).trans
    exact radial_forcing_absorbed (sourceBranchConstants_nonneg d O a teacher).2 hl hp hp3
      (hper.2 s hsc).1 (hper.2 s hsc).2.1 hr ((le_max_right _ _).trans hRcur))
  have hcost := hbar t ht
  rw [assignedCost_eq_half_poleRadius_sq] at hcost
  change sphericalPoleRadius pole (X.characteristic i t w) ≤ R
  nlinarith [sphericalPoleRadius_nonneg pole (X.characteristic i t w)]

/-- The same exact Rbar as the source, including its strict margin and the
entire current closed support, follows from the two initial source conditions. -/
theorem SphericalCharacteristicSolution.exact_barrier_of_branch
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hb : ∀ t ∈ Icc (0 : Real) T, X.measure 1 t = reflectedMeasure (X.measure 0 t))
    (hl : 0 < lambda) (hp : 2 < p) (hp3 : p < 3)
    (zstar : Real) (_hzstar : 0 < zstar)
    (hrad : sourceRadialConstant d O a teacher*zstar^((4-p)/2) ≤ lambda/2)
    (hforce : (sourceFittingConstant d O a teacher/lambda)*zstar^((3-p)/2) ≤ radius/2)
    (hinit : productAntipodalTransportSq pole (initial 0) (initial 1) ≤ zstar) :
    let Rbar := max (productSphericalSupportRadius pole initial)
      ((sourceFittingConstant d O a teacher/lambda)*
        (productAntipodalTransportSq pole (initial 0) (initial 1))^((3-p)/2))
    Rbar < radius ∧
    (∀ i w, w ∈ (initial i).support → ∀ t ∈ Icc (0 : Real) T,
      sphericalPoleRadius pole (X.characteristic i t w) ≤ Rbar) ∧
    (∀ t ∈ Icc (0 : Real) T,
      (∀ i : Fin 2, (X.measure i t).support ⊆ {w | sphericalPoleRadius pole w ≤ Rbar}) ∧
      productSphericalSupportRadius pole (fun i => X.measure i t) ≤ Rbar ∧
      (∀ i : Fin 2, TwoCapClass pole ((Rbar+radius)/2) (X.measure i t))) := by
  let R0 := productSphericalSupportRadius pole initial
  let Rbar := max R0 ((sourceFittingConstant d O a teacher/lambda)*
    (productAntipodalTransportSq pole (initial 0) (initial 1))^((3-p)/2))
  have hR0 := X.initial_exact_support_radius
  have hr := (X.cap 0 0 ⟨le_rfl,X.time_nonneg⟩).radius_pos
  have hZ0 : 0 ≤ productAntipodalTransportSq pole (initial 0) (initial 1) := by
    rw [← X.transport_initial]
    exact X.productTransport_nonneg 0 ⟨le_rfl,X.time_nonneg⟩
  have hm := source_basin_initial_margins O a teacher lambda p radius zstar
    (productAntipodalTransportSq pole (initial 0) (initial 1)) hl hp3 hZ0 hinit hrad hforce
  have hRbar : Rbar < radius := max_lt hR0.2.1 (hm.2.trans_lt (by linarith))
  have hRbar0 : 0 ≤ Rbar := hR0.1.trans (le_max_left _ _)
  have hparticle : ∀ i w, w ∈ (initial i).support → ∀ t ∈ Icc (0 : Real) T,
      sphericalPoleRadius pole (X.characteristic i t w) ≤ Rbar := by
    intro i w hw t ht
    exact X.particle_barrier_of_branch hO hb hl hp hp3 hm.1 R0 hR0.1 hR0.2.2.1 i w hw t ht
  have hs : ∀ i t, t ∈ Icc (0 : Real) T →
      (X.measure i t).support ⊆ {w | sphericalPoleRadius pole w ≤ Rbar} := by
    intro i t ht
    apply X.support_radius_le i t ht
    intro w hw
    exact hparticle i w hw t ht
  refine ⟨hRbar,hparticle,?_⟩
  intro t ht
  refine ⟨fun i => hs i t ht,?_,?_⟩
  · exact ((productSphericalSupportRadius_cap_properties pole radius
      (fun i => X.measure i t) (fun i => X.cap i t ht)).2.2.2 Rbar).mpr
      (fun i w hw => hs i t ht hw)
  · intro i
    exact (X.cap i t ht).refine_radius_of_le Rbar ((Rbar+radius)/2)
      (by linarith) (by linarith) (by linarith) (hs i t ht)

end PaperFormalization.MatrixFactorization
