import PaperFormalization.MatrixFactorization.SourceCharacteristicPersistence
import PaperFormalization.MatrixFactorization.SphericalCharacteristicIntegratedBounds

/-! # Sharp initial-margin time integrals along actual characteristics

The exact initial printed Cstar margin supplies the derived current estimates.
The original objective drop and the original transport drop control their
respective time integrals on any closed subinterval, including length zero.
The given cap-interval hypothesis is retained; no global confinement or
additional time integrability premise is imposed.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}

/-- The integral of the original transport power is controlled by the actual
objective drop, using the derived squared-gradient estimate. -/
theorem SphericalCharacteristicSolution.integrated_gradientEnergy_lower_source
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (hsmall0 : sourceRadialConstant d O a teacher*
      (productAntipodalTransportSq pole (initial 0) (initial 1))^((4-p)/2) ≤ lambda/2)
    (s t : Real) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    (lambda^2/4)*(∫ u in s..t, (X.transport u)^(p-1)) ≤ X.objective s-X.objective t := by
  have hi := (X.transport_rpow_intervalIntegrable (p-1) (by linarith) s t hs hst ht).const_mul (lambda^2/4)
  have hb : ∀ u ∈ Ioo s t, (lambda^2/4)*(X.transport u)^(p-1) ≤ X.gradientEnergy u := by
    intro u hu
    have hut : u ∈ Ioo (0 : Real) T := ⟨hs.trans_lt hu.1,hu.2.trans_le ht⟩
    have hd := X.objective_deriv_le_source_from_initial hO hunique hinitial hl hp hp4 hsmall0 u hut
    rw [(X.objective_hasDerivAt hp u hut).deriv] at hd
    linarith
  have hineq := intervalIntegral.integral_mono_on_of_le_Ioo hst hi
    (X.gradientEnergy_intervalIntegrable hp s t hs hst ht) hb
  rw [intervalIntegral.integral_const_mul, X.integrated_energy hp s t hs hst ht] at hineq
  exact hineq

/-- The negative actual transport derivative is time integrable. Its
nonnegativity is derived from the original initial-smallness theorem. -/
theorem SphericalCharacteristicSolution.transport_deriv_intervalIntegrable_source
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (hsmall0 : sourceRadialConstant d O a teacher*
      (productAntipodalTransportSq pole (initial 0) (initial 1))^((4-p)/2) ≤ lambda/2)
    (s t : Real) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    IntervalIntegrable (fun u => -deriv X.transport u) volume s t := by
  have hc : ContinuousOn (fun u => -X.transport u) (Icc s t) :=
    X.productTransport_continuousOn.neg.mono (Icc_subset_Icc hs ht)
  have hd (u : Real) (hu : u ∈ Ioo s t) :
      HasDerivAt (fun v => -X.transport v) (-deriv X.transport u) u := by
    exact ((X.productTransport_hasDerivAt hp u
      ⟨hs.trans_lt hu.1,hu.2.trans_le ht⟩).differentiableAt.hasDerivAt).neg
  have hn (u : Real) (hu : u ∈ Ioo s t) : 0 ≤ -deriv X.transport u := by
    have hut : u ∈ Ioo (0 : Real) T := ⟨hs.trans_lt hu.1,hu.2.trans_le ht⟩
    have hb := X.transport_deriv_le_source_from_initial hO hunique hinitial hl hp hp4 hsmall0 u hut
    have hz := X.productTransport_nonneg u ⟨hut.1.le,hut.2.le⟩
    have hm : 0 ≤ lambda*(X.transport u)^(p/2) := mul_nonneg hl.le (Real.rpow_nonneg hz _)
    linarith
  apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
    (g := fun u => -X.transport u)
  · simpa only [uIcc_of_le hst] using hc
  · simpa only [min_eq_left hst, max_eq_right hst] using hd
  · simpa only [min_eq_left hst, max_eq_right hst] using hn

/-- The actual distance drop controls the accumulated nonnegative transport
power on every closed subinterval of the given cap-interval solution. -/
theorem SphericalCharacteristicSolution.integrated_transport_decay_source
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (hsmall0 : sourceRadialConstant d O a teacher*
      (productAntipodalTransportSq pole (initial 0) (initial 1))^((4-p)/2) ≤ lambda/2)
    (s t : Real) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    lambda*(∫ u in s..t, (X.transport u)^(p/2)) ≤ X.transport s-X.transport t := by
  have hi := (X.transport_rpow_intervalIntegrable (p/2) (by linarith) s t hs hst ht).const_mul lambda
  have hdi := X.transport_deriv_intervalIntegrable_source hO hunique hinitial hl hp hp4 hsmall0 s t hs hst ht
  have hc : ContinuousOn (fun u => -X.transport u) (Icc s t) :=
    X.productTransport_continuousOn.neg.mono (Icc_subset_Icc hs ht)
  have hd (u : Real) (hu : u ∈ Ioo s t) :
      HasDerivAt (fun v => -X.transport v) (-deriv X.transport u) u := by
    exact ((X.productTransport_hasDerivAt hp u
      ⟨hs.trans_lt hu.1,hu.2.trans_le ht⟩).differentiableAt.hasDerivAt).neg
  have he : (∫ u in s..t, -deriv X.transport u) = X.transport s-X.transport t := by
    simpa only [neg_sub_neg] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hc hd hdi
  have hb : ∀ u ∈ Ioo s t, lambda*(X.transport u)^(p/2) ≤ -deriv X.transport u := by
    intro u hu
    have hd := X.transport_deriv_le_source_from_initial hO hunique hinitial hl hp hp4 hsmall0
      u ⟨hs.trans_lt hu.1,hu.2.trans_le ht⟩
    linarith
  have hineq := intervalIntegral.integral_mono_on_of_le_Ioo hst hi hdi hb
  rw [intervalIntegral.integral_const_mul,he] at hineq
  exact hineq

end PaperFormalization.MatrixFactorization
