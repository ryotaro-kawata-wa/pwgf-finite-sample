import PaperFormalization.MatrixFactorization.CharacteristicPointwiseRadial
import PaperFormalization.MatrixFactorization.ScalarRadialSupport
import PaperFormalization.MatrixFactorization.ScalarSupportBarrier

/-! # A supported-particle barrier on the original finite cap interval

The barrier acts on the actual half-squared angular cost, so neither pole
requires differentiation of the unsquared distance. Mean-distance persistence
is used only to bound the fitting-force coefficient, never to bound an
individual support radius by the mean distance. The given cap interval is not
extended by this theorem, and the coefficient remains explicitly coarse.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}

/-- Every original supported characteristic remains below the fixed initial
support/forcing barrier throughout the same given closed cap interval. -/
theorem SphericalCharacteristicSolution.particle_radius_le_initial_barrier
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (hl : 0 < lambda) (hp : 2 < p) (hp3 : p < 3)
    (hsmall0 : productAntipodalTransportSq pole (initial 0) (initial 1) ≤
      coarseRadialRadius lambda p (fittingCurvatureConstant d O a/64))
    (R0 : Real) (hR0 : 0 ≤ R0)
    (hbound : ∀ i w, w ∈ (initial i).support → sphericalPoleRadius pole w ≤ R0)
    (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (initial i).support)
    (t : Real) (ht : t ∈ Icc 0 T) :
    sphericalPoleRadius pole (X.characteristic i t w) ≤
      max R0 ((fittingCurvatureConstant d O a/lambda)*
        (productAntipodalTransportSq pole (initial 0) (initial 1))^((3-p)/2)) := by
  let Z0 := productAntipodalTransportSq pole (initial 0) (initial 1)
  let R := max R0 ((fittingCurvatureConstant d O a/lambda)*Z0^((3-p)/2))
  have hR : 0 ≤ R := hR0.trans (le_max_left _ _)
  have hpersist := X.transport_persists hO hunique hinitial hl hp (by linarith : p < 4) hsmall0
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
  have hb := scalar_support_barrier hc hd hi (fun s hs hlarge => by
    have hsc : s ∈ Icc (0 : Real) T := ⟨hs.1.le,hs.2.le⟩
    have hr : 0 ≤ sphericalPoleRadius pole (X.characteristic i s w) :=
      sphericalPoleRadius_nonneg _ _
    have hRcur : R ≤ sphericalPoleRadius pole (X.characteristic i s w) := by
      rw [assignedCost_eq_half_poleRadius_sq] at hlarge
      by_contra hn
      have hsq := pow_le_pow_left₀ hr (le_of_lt (lt_of_not_ge hn)) 2
      nlinarith
    apply (X.assignedCost_deriv_le_antibranch hO hunique hinitial i w hw s hs).trans
    exact radial_forcing_absorbed (fittingCurvatureConstant_nonneg d O a) hl hp hp3
      (hpersist.2 s hsc).1
      (hpersist.2 s hsc).2.1
      hr ((le_max_right _ _).trans hRcur))
  have hcost := hb t ht
  rw [assignedCost_eq_half_poleRadius_sq] at hcost
  change sphericalPoleRadius pole (X.characteristic i t w) ≤ R
  nlinarith [sphericalPoleRadius_nonneg pole (X.characteristic i t w)]

end PaperFormalization.MatrixFactorization
