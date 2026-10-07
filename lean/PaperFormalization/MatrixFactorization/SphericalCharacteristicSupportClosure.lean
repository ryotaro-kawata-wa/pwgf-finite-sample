import PaperFormalization.MatrixFactorization.SphericalCharacteristicSupportBarrier
import PaperFormalization.MatrixFactorization.SphericalSupportRadius
import PaperFormalization.MatrixFactorization.TwoCapRadiusRefinement
import PaperFormalization.MatrixFactorization.CoarseSupportMargin
import PaperFormalization.MatrixFactorization.SphericalCharacteristicDecayClosure

/-! # A uniform strict support barrier for the actual cap-interval solution

The initial support radius is derived from the original compact supports. The
new sufficient basin combines the existing mean-distance margin and a coarse
pointwise forcing margin. Every bound concerns the actual current closed
support. This does not extend the assumed cap interval to a global trajectory.
-/
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}

/-- The proved particle barrier passes to the entire current closed support. -/
theorem SphericalCharacteristicSolution.support_radius_le_initial_barrier
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (hl : 0 < lambda) (hp : 2 < p) (hp3 : p < 3)
    (hsmall0 : productAntipodalTransportSq pole (initial 0) (initial 1) ≤
      coarseRadialRadius lambda p (fittingCurvatureConstant d O a/64))
    (R0 : Real) (hR0 : 0 ≤ R0)
    (hbound : ∀ i w, w ∈ (initial i).support → sphericalPoleRadius pole w ≤ R0)
    (i : Fin 2) (t : Real) (ht : t ∈ Icc 0 T) :
    (X.measure i t).support ⊆ {w | sphericalPoleRadius pole w ≤
      max R0 ((fittingCurvatureConstant d O a/lambda)*
        (productAntipodalTransportSq pole (initial 0) (initial 1))^((3-p)/2))} := by
  apply X.support_radius_le i t ht
  intro w hw
  exact X.particle_radius_le_initial_barrier hO hunique hinitial hl hp hp3 hsmall0
    R0 hR0 hbound i w hw t ht

/-- A closed sufficient initial transport bound yields one strictly interior
barrier, uniform over time, both original supports and both current supports. -/
theorem SphericalCharacteristicSolution.support_strict_barrier
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (hl : 0 < lambda) (hp : 2 < p) (hp3 : p < 3)
    (hsmall0 : productAntipodalTransportSq pole (initial 0) (initial 1) ≤
      coarseSupportBasin lambda p (fittingCurvatureConstant d O a) radius) :
    ∃ R0 : Real, 0 ≤ R0 ∧ R0 < radius ∧
      (∀ i w, w ∈ (initial i).support → sphericalPoleRadius pole w ≤ R0) ∧
      max R0 ((fittingCurvatureConstant d O a/lambda)*
        (productAntipodalTransportSq pole (initial 0) (initial 1))^((3-p)/2)) < radius ∧
      (∀ i w, w ∈ (initial i).support → ∀ t ∈ Icc (0 : Real) T,
        sphericalPoleRadius pole (X.characteristic i t w) ≤
          max R0 ((fittingCurvatureConstant d O a/lambda)*
            (productAntipodalTransportSq pole (initial 0) (initial 1))^((3-p)/2))) ∧
      (∀ i t, t ∈ Icc (0 : Real) T →
        (X.measure i t).support ⊆ {w | sphericalPoleRadius pole w ≤
          max R0 ((fittingCurvatureConstant d O a/lambda)*
            (productAntipodalTransportSq pole (initial 0) (initial 1))^((3-p)/2))}) := by
  have hr := (X.cap 0 0 ⟨le_rfl,X.time_nonneg⟩).radius_pos
  have hz0 : 0 ≤ productAntipodalTransportSq pole (initial 0) (initial 1) := by
    rw [← X.transport_initial]
    exact X.productTransport_nonneg 0 ⟨le_rfl,X.time_nonneg⟩
  have hb := coarseSupportBasin_bounds lambda p (fittingCurvatureConstant d O a) radius
    (productAntipodalTransportSq pole (initial 0) (initial 1)) hl hp3
    (fittingCurvatureConstant_nonneg d O a) hr hz0 hsmall0
  obtain ⟨R0,hR0,hR0r,hbound⟩ := X.initial_support_radius_lt
  refine ⟨R0,hR0,hR0r,hbound,max_lt hR0r (hb.2.trans_lt (by linarith)),?_,?_⟩
  · intro i w hw t ht
    exact X.particle_radius_le_initial_barrier hO hunique hinitial hl hp hp3 hb.1
      R0 hR0 hbound i w hw t ht
  · intro i t ht
    exact X.support_radius_le_initial_barrier hO hunique hinitial hl hp hp3 hb.1
      R0 hR0 hbound i t ht

/-- The source-facing finite-interval endpoint supplies a uniformly smaller
cap class with exact half masses, together with the actual distance decay and
energy dissipation. The global continuation problem is a separate obligation. -/
theorem spherical_characteristic_cap_interval_support_control
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (hl : 0 < lambda) (hp : 2 < p) (hp3 : p < 3)
    (hsmall0 : productAntipodalTransportSq pole (initial 0) (initial 1) ≤
      coarseSupportBasin lambda p (fittingCurvatureConstant d O a) radius) :
    ∃ R0 : Real, 0 ≤ R0 ∧ R0 < radius ∧
      let R := max R0 ((fittingCurvatureConstant d O a/lambda)*
        (productAntipodalTransportSq pole (initial 0) (initial 1))^((3-p)/2))
      R < radius ∧
      (∀ t ∈ Icc (0 : Real) T,
        (∀ i : Fin 2, TwoCapClass pole ((R+radius)/2) (X.measure i t)) ∧
        (∀ i : Fin 2, (X.measure i t).support ⊆ {w | sphericalPoleRadius pole w ≤ R}) ∧
        X.transport t ≤
          (X.transport 0)/
            (1+(lambda*(p-2)/2)*(X.transport 0)^((p-2)/2)*t)^(2/(p-2)) ∧
        X.objective t ≤ X.objective 0) ∧
      (∀ t ∈ Ioo (0 : Real) T,
        HasDerivAt X.objective (-X.gradientEnergy t) t ∧
        deriv X.transport t ≤ -lambda*(X.transport t)^(p/2) ∧
        deriv X.objective t ≤ -(lambda^2/4)*(X.transport t)^(p-1)) := by
  obtain ⟨R0,hR0,hR0r,hbound,hRr,hparticle,hsupport⟩ :=
    X.support_strict_barrier hO hunique hinitial hl hp hp3 hsmall0
  let R := max R0 ((fittingCurvatureConstant d O a/lambda)*
    (productAntipodalTransportSq pole (initial 0) (initial 1))^((3-p)/2))
  have hR : 0 ≤ R := hR0.trans (le_max_left _ _)
  have hr := (X.cap 0 0 ⟨le_rfl,X.time_nonneg⟩).radius_pos
  have hsmall : productAntipodalTransportSq pole (initial 0) (initial 1) ≤
      coarseRadialRadius lambda p (fittingCurvatureConstant d O a/64) :=
    hsmall0.trans (min_le_left _ _)
  have hdec := spherical_characteristic_cap_interval_dissipation X hO hunique hinitial
    hl hp (by linarith : p < 4) hsmall
  refine ⟨R0,hR0,hR0r,hRr,?_,?_⟩
  · intro t ht
    refine ⟨?_,fun i => hsupport i t ht,(hdec.2.2.2.1 t ht).2.1,
      (hdec.2.2.2.1 t ht).2.2.2⟩
    intro i
    exact (X.cap i t ht).refine_radius_of_le R ((R+radius)/2)
      (by linarith) (by dsimp [R]; linarith) (by dsimp [R]; linarith)
      (hsupport i t ht)
  · intro t ht
    have hd := hdec.2.2.2.2.1 t ht
    exact ⟨hd.1,hd.2.1,hd.2.2.1⟩

end PaperFormalization.MatrixFactorization
