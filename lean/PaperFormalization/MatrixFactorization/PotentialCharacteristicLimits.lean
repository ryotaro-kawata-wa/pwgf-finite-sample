import PaperFormalization.MatrixFactorization.PotentialCharacteristicGlobalEstimates
import PaperFormalization.MatrixFactorization.SphericalTransportContinuity

/-! # MF23: transport convergence for one represented global trajectory

Execution records: `MF23_VALIDATION.md`.

The limits apply to the same literal pushed laws used
in the ODE, not to a family of unrelated finite solutions. The convergence
functional is the true all-coupling angular transport cost and its square
root. No new abstract Wasserstein metric instance is postulated.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

/-- Zero initial distance and arbitrary real p>2 are covered by the existing profile lemma. -/
theorem PotentialGlobalEstimates.transport_limit
    {X : PotentialCharacteristicFlow O a pole lambda p teacher initial}
    (H : PotentialGlobalEstimates X) (hl : 0 < lambda) (hp : 2 < p) :
    Tendsto X.transport atTop (𝓝 0) := by
  exact scalar_tendsto_zero_of_powerDecayProfile_bound hl (by linarith)
    (H.decay 0 le_rfl).1 (fun t ht => ⟨(H.decay t ht).1,(H.decay t ht).2.1⟩)

/-- The original product Wasserstein-distance expression, sqrt of the sum of squares. -/
theorem PotentialGlobalEstimates.productDistance_limit
    {X : PotentialCharacteristicFlow O a pole lambda p teacher initial}
    (H : PotentialGlobalEstimates X) (hl : 0 < lambda) (hp : 2 < p) :
    Tendsto (fun t => Real.sqrt (X.transport t)) atTop (𝓝 0) := by
  simpa only [Real.sqrt_zero, Function.comp_def] using
    Real.continuous_sqrt.continuousAt.tendsto.comp (H.transport_limit hl hp)

/-- Each marginal converges to the same antipodal target in squared angular transport. -/
theorem PotentialGlobalEstimates.marginalTransport_limit
    {X : PotentialCharacteristicFlow O a pole lambda p teacher initial}
    (H : PotentialGlobalEstimates X) (hl : 0 < lambda) (hp : 2 < p) (i : Fin 2) :
    Tendsto (fun t => sphericalWassersteinSq (X.measure i t) (antipodalMeasure pole))
      atTop (𝓝 0) := by
  have hb (t : Real) (ht : 0 ≤ t) :
      0 ≤ sphericalWassersteinSq (X.measure i t) (antipodalMeasure pole) ∧
      sphericalWassersteinSq (X.measure i t) (antipodalMeasure pole) ≤ X.transport t := by
    letI := X.measure_probability 0 t ht
    letI := X.measure_probability 1 t ht
    letI := X.measure_probability i t ht
    have h0 := sphericalWassersteinSq_nonneg (X.measure 0 t) (antipodalMeasure pole)
    have h1 := sphericalWassersteinSq_nonneg (X.measure 1 t) (antipodalMeasure pole)
    refine ⟨sphericalWassersteinSq_nonneg _ _,?_⟩
    fin_cases i
    · exact le_add_of_nonneg_right h1
    · exact le_add_of_nonneg_left h0
  exact squeeze_zero'
    ((eventually_ge_atTop (0 : Real)).mono (fun t ht => (hb t ht).1))
    ((eventually_ge_atTop (0 : Real)).mono (fun t ht => (hb t ht).2))
    (H.transport_limit hl hp)

/-- A transport-to-observable adapter. The test's Lipschitz property is an
explicit helper input; raw tensor coordinate tests discharge it separately.
Integrability is supplied by compactness in the existing transport theorem. -/
theorem PotentialGlobalEstimates.lipschitz_test_limit
    {X : PotentialCharacteristicFlow O a pole lambda p teacher initial}
    (H : PotentialGlobalEstimates X) (hl : 0 < lambda) (hp : 2 < p)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    (f : UnitSphere d → E) (hf : Continuous f) (L : Real) (hL : 0 ≤ L)
    (hlip : ∀ w y, norm (f w-f y) ≤ L*sphericalDistance w y) (i : Fin 2) :
    Tendsto (fun t => ∫ w, f w ∂X.measure i t) atTop
      (𝓝 (∫ w, f w ∂antipodalMeasure pole)) := by
  have hsqrt : Tendsto
      (fun t => Real.sqrt (sphericalWassersteinSq (X.measure i t) (antipodalMeasure pole)))
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp (H.marginalTransport_limit hl hp i)
  have hupper : Tendsto
      (fun t => L*Real.sqrt (sphericalWassersteinSq (X.measure i t) (antipodalMeasure pole)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := L)).mul hsqrt
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun t => norm_nonneg _)) _ hupper
  filter_upwards [eventually_ge_atTop (0 : Real)] with t ht
  letI := X.measure_probability i t ht
  exact sphericalWasserstein_expectation_sub_norm_le (X.measure i t) (antipodalMeasure pole)
    f hf L hL hlip

/-- No all-time cap or decay hypothesis occurs here: the preceding endpoint
constructs both from initial data, within the explicit represented-flow class.
This is NOT a claim that the source-to-representation theorem has been proved. -/
theorem PotentialCharacteristicFlow.source_transport_convergence
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
    Tendsto X.transport atTop (𝓝 0) ∧
    Tendsto (fun t => Real.sqrt (X.transport t)) atTop (𝓝 0) ∧
    (∀ i : Fin 2, Tendsto (fun t => sphericalWassersteinSq (X.measure i t) (antipodalMeasure pole))
      atTop (𝓝 0)) := by
  have H := (X.source_global_estimates hO hu hi r hc hl hp hp3 zstar hzstar hrad hforce hinit).2
  exact ⟨H.transport_limit hl hp,H.productDistance_limit hl hp,H.marginalTransport_limit hl hp⟩

end PaperFormalization.MatrixFactorization
