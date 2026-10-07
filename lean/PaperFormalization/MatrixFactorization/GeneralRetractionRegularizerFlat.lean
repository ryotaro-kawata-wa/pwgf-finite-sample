import PaperFormalization.MatrixFactorization.TransverseRetractionObjective
import PaperFormalization.MatrixFactorization.GeneralRetractionTransport

/-! # MF10: ordinary second-order flatness at zero transport

A continuous factor that vanishes at zero may multiply a differentiable
vanishing factor without requiring the first factor to be differentiable.
This supplies the zero-transport power law for every real p>2, including
2<p<3, directly from the proved transport jets.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Only continuity of A is needed because A(0)=B(0)=0. -/
theorem vanishing_continuous_mul_hasDerivAt_zero (A B : Real → Real) (c : Real)
    (hA : ContinuousAt A 0) (hA0 : A 0 = 0) (hB0 : B 0 = 0)
    (hB : HasDerivAt B c 0) : HasDerivAt (fun t => A t*B t) 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero] at hB ⊢
  have hAt : Tendsto A (𝓝[≠] (0 : Real)) (𝓝 0) := by
    simpa only [hA0] using hA.tendsto.mono_left nhdsWithin_le_nhds
  have hp := hAt.mul hB
  have hp' : Tendsto (fun t : Real => A t*(t⁻¹ • (B (0+t)-B 0))) (𝓝[≠] (0 : Real)) (𝓝 0) := by
    simpa only [zero_mul] using hp
  apply hp'.congr'
  filter_upwards with t
  simp only [zero_add, hA0, hB0, mul_zero, sub_zero, smul_eq_mul]
  ring

/-- A scalar calculus adapter, whose hypotheses are discharged by the actual
transport theorem below. The fractional-power factor is not differentiated
at zero when its exponent lies strictly between zero and one. -/
theorem zero_regularizer_chain_rule (Z : Real → Real) (lambda p d2 : Real)
    (hp : 2 < p) (hZ : Z 0 = 0) (h1 : HasDerivAt Z 0 0)
    (h2 : HasDerivAt (deriv Z) d2 0)
    (hnear : ∀ᶠ t in 𝓝 (0 : Real), DifferentiableAt Real Z t) :
    HasDerivAt (fun t => lambda/p*(Z t)^(p/2)) 0 0 ∧
    HasDerivAt (deriv (fun t => lambda/p*(Z t)^(p/2))) 0 0 := by
  have hp0 : p ≠ 0 := by linarith
  have hp1 : 1 ≤ p/2 := by linarith
  have hpow : 0 < p/2-1 := by linarith
  have hfirst := (h1.rpow_const (p := p/2) (Or.inr hp1)).const_mul (lambda/p)
  have hfirst' : HasDerivAt (fun t => lambda/p*(Z t)^(p/2)) 0 0 := by
    simpa only [zero_mul, mul_zero] using hfirst
  have he : deriv (fun t => lambda/p*(Z t)^(p/2)) =ᶠ[𝓝 (0 : Real)]
      (fun t => (lambda/2*(Z t)^(p/2-1))*deriv Z t) := by
    filter_upwards [hnear] with t ht
    rw [((ht.hasDerivAt.rpow_const (p := p/2) (Or.inr hp1)).const_mul (lambda/p)).deriv]
    field_simp [hp0]
  have hA : ContinuousAt (fun t => lambda/2*(Z t)^(p/2-1)) 0 :=
    continuousAt_const.mul (h1.continuousAt.rpow_const (Or.inr hpow.le))
  have hA0 : lambda/2*(Z 0)^(p/2-1) = 0 := by rw [hZ, Real.zero_rpow hpow.ne', mul_zero]
  have hd := vanishing_continuous_mul_hasDerivAt_zero
    (fun t => lambda/2*(Z t)^(p/2-1)) (deriv Z) d2 hA hA0 h1.deriv h2
  exact ⟨hfirst', hd.congr_of_eventuallyEq he⟩

/-- The original zero-cost law makes the already verified EXP transport
quadratic, and hence forces the original first variation to vanish. -/
theorem variationFirst_zero_of_zero_transport {d : Nat} (P : SphericalVariation d)
    (hZ : variationTransport P 0 = 0) : 2*variationFirst P = 0 := by
  have hpoly : HasDerivAt (fun t : Real => t^2*variationEnergy P) 0 0 := by
    simpa using ((hasDerivAt_id (0 : Real)).pow 2).mul_const (variationEnergy P)
  have hzero := hpoly.congr_of_eventuallyEq (variationTransport_zero_quadratic P hZ)
  exact (variationTransport_variations P).1.unique hzero

/-- Flatness for the literal normalized pushed measures, including arbitrary
continuous tangent fields and unequal velocities at the antipodal atoms. -/
theorem metricRegularizer_retracted_zero_variations {d : Nat} (P : SphericalVariation d)
    (lambda p : Real) (hp : 2 < p) (hZ : variationTransport P 0 = 0) :
    HasDerivAt (variationRetractedRegularizer P lambda p) 0 0 ∧
    HasDerivAt (deriv (variationRetractedRegularizer P lambda p)) 0 0 := by
  have ht := variationRetractedTransport_variations P
  have hfirst : HasDerivAt (variationRetractedTransport P) 0 0 :=
    ht.1.congr_deriv (variationFirst_zero_of_zero_transport P hZ)
  have hzero : variationRetractedTransport P 0 = 0 := by
    simpa only [variationRetractedTransport_zero] using hZ
  exact zero_regularizer_chain_rule (variationRetractedTransport P) lambda p
    (2*variationSecond P) hp hzero hfirst ht.2.1 ht.2.2

/-- The power is differentiable near zero for every real exponent p>2,
including at points where the transported measures exactly match the target. -/
theorem variationRetractedRegularizer_differentiable_near {d : Nat}
    (P : SphericalVariation d) (lambda p : Real) (hp : 2 < p) :
    ∀ᶠ t in 𝓝 (0 : Real), DifferentiableAt Real
      (variationRetractedRegularizer P lambda p) t := by
  have hp1 : 1 ≤ p/2 := by linarith
  filter_upwards [(variationRetractedTransport_variations P).2.2] with t ht
  exact ((ht.hasDerivAt.rpow_const (p := p/2) (Or.inr hp1)).const_mul
    (lambda/p)).differentiableAt

/-- Zero transport makes the actual normalized metric penalty smaller than
quadratic, without requiring a common speed for the tangent vector field. -/
theorem metricRegularizer_retracted_zero_littleO {d : Nat}
    (P : SphericalVariation d) (lambda p : Real) (hp : 2 < p)
    (hZ : variationTransport P 0 = 0) :
    variationRetractedRegularizer P lambda p =o[𝓝 (0 : Real)] (fun t => t^2) := by
  have hj := metricRegularizer_retracted_zero_variations P lambda p hp hZ
  have hi := peano_second_at_zero (variationRetractedRegularizer P lambda p)
    0 hj.1 hj.2 (variationRetractedRegularizer_differentiable_near P lambda p hp)
  have he (i : Fin 2) : sphericalRetractFamily (P.velocity i) (P.tangent i) 0 = id :=
    funext (sphericalRetractFamily_zero (P.velocity i) (P.tangent i))
  have hz : productAntipodalTransportSq P.pole (P.measure 0) (P.measure 1) = 0 := by
    simpa only [variationTransport_zero] using hZ
  have hzero : variationRetractedRegularizer P lambda p 0 = 0 := by
    simp only [variationRetractedRegularizer, he, Measure.map_id,
      metricRegularizer, hz, Real.zero_rpow (by linarith : p/2 ≠ 0), mul_zero]
  simpa only [hzero, zero_div, zero_mul, sub_zero] using hi

end PaperFormalization.MatrixFactorization
