import PaperFormalization.MatrixFactorization.SphericalCharacteristicIntegratedEnergy

/-! # Quantitative time integrals along the original characteristic law

Both estimates use initial-only persistence on the existing cap interval.
The powers of the genuine squared transport are time integrable by continuity.
The actual transport derivative is integrable by the nonnegative-derivative
fundamental theorem; no chain rule or time-integrability premise is supplied.
The sufficient initial radius remains the verified coarse radius.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}

/-- Nonnegative real powers of the actual transport are time integrable,
including zero transport and both subinterval endpoints. -/
theorem SphericalCharacteristicSolution.transport_rpow_intervalIntegrable
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (q : Real) (hq : 0 ≤ q) (s t : Real)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    IntervalIntegrable (fun u => X.transport u ^ q) volume s t := by
  have hc : ContinuousOn (fun u => X.transport u ^ q) (Icc 0 T) :=
    X.productTransport_continuousOn.rpow_const (fun _ _ => Or.inr hq)
  exact (hc.mono (Icc_subset_Icc hs ht)).intervalIntegrable_of_Icc hst

/-- The integral of the original transport power is controlled by the actual
objective drop, using the derived squared-gradient estimate. -/
theorem SphericalCharacteristicSolution.integrated_gradientEnergy_lower
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (hsmall0 : productAntipodalTransportSq pole (initial 0) (initial 1) ≤
      coarseRadialRadius lambda p (fittingCurvatureConstant d O a/64))
    (s t : Real) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    (lambda^2/4)*(∫ u in s..t, (X.transport u)^(p-1)) ≤ X.objective s-X.objective t := by
  have hi := (X.transport_rpow_intervalIntegrable (p-1) (by linarith) s t hs hst ht).const_mul (lambda^2/4)
  have hb : ∀ u ∈ Ioo s t, (lambda^2/4)*(X.transport u)^(p-1) ≤ X.gradientEnergy u := by
    intro u hu
    have hut : u ∈ Ioo (0 : Real) T := ⟨hs.trans_lt hu.1,hu.2.trans_le ht⟩
    have hd := X.objective_deriv_le_from_initial hO hunique hinitial hl hp hp4 hsmall0 u hut
    rw [(X.objective_hasDerivAt hp u hut).deriv] at hd
    linarith
  have hineq := intervalIntegral.integral_mono_on_of_le_Ioo hst hi
    (X.gradientEnergy_intervalIntegrable hp s t hs hst ht) hb
  rw [intervalIntegral.integral_const_mul, X.integrated_energy hp s t hs hst ht] at hineq
  exact hineq

/-- The negative actual transport derivative is time integrable. Its
nonnegativity is derived from the original initial-smallness theorem. -/
theorem SphericalCharacteristicSolution.transport_deriv_intervalIntegrable
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (hsmall0 : productAntipodalTransportSq pole (initial 0) (initial 1) ≤
      coarseRadialRadius lambda p (fittingCurvatureConstant d O a/64))
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
    have hb := (X.transport_decay hO hunique hinitial hl hp hp4 hsmall0).2.1 u hut
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
theorem SphericalCharacteristicSolution.integrated_transport_decay
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (hsmall0 : productAntipodalTransportSq pole (initial 0) (initial 1) ≤
      coarseRadialRadius lambda p (fittingCurvatureConstant d O a/64))
    (s t : Real) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    lambda*(∫ u in s..t, (X.transport u)^(p/2)) ≤ X.transport s-X.transport t := by
  have hi := (X.transport_rpow_intervalIntegrable (p/2) (by linarith) s t hs hst ht).const_mul lambda
  have hdi := X.transport_deriv_intervalIntegrable hO hunique hinitial hl hp hp4 hsmall0 s t hs hst ht
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
    have hd := (X.transport_decay hO hunique hinitial hl hp hp4 hsmall0).2.1
      u ⟨hs.trans_lt hu.1,hu.2.trans_le ht⟩
    linarith
  have hineq := intervalIntegral.integral_mono_on_of_le_Ioo hst hi hdi hb
  rw [intervalIntegral.integral_const_mul,he] at hineq
  exact hineq

end PaperFormalization.MatrixFactorization
