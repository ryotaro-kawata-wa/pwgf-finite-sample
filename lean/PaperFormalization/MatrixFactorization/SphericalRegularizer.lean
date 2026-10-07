import PaperFormalization.MatrixFactorization.SphericalCostIntegral

/-! # MF03: positive-distance variations of the actual metric regularizer

MF03 checkpoint candidate; see MF03_VALIDATION.md for execution status.
SphericalVariation packages only original two-cap
probability measures and continuous tangent fields. It contains no cost,
integrability, derivative, Hessian, or curvature conclusion as a hypothesis.
The original product cost is used literally, not a newly defined surrogate.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

structure SphericalVariation (d : Nat) where
  pole : UnitSphere d
  radius : Real
  measure : Fin 2 → Measure (UnitSphere d)
  cap : ∀ i, TwoCapClass pole radius (measure i)
  velocity : Fin 2 → UnitSphere d → Weight d
  tangent : ∀ i w, inner Real w.val (velocity i w) = 0
  continuous_velocity : ∀ i, Continuous (velocity i)

noncomputable def variationTransport {d : Nat} (P : SphericalVariation d) (t : Real) : Real :=
  productAntipodalTransportSq P.pole
    ((P.measure 0).map (sphericalExpFamily (P.velocity 0) (P.tangent 0) t))
    ((P.measure 1).map (sphericalExpFamily (P.velocity 1) (P.tangent 1) t))

noncomputable def variationFirst {d : Nat} (P : SphericalVariation d) : Real :=
  ∑ i : Fin 2, marginalCostFirst P.pole (P.measure i) (P.velocity i)

noncomputable def variationSecond {d : Nat} (P : SphericalVariation d) : Real :=
  ∑ i : Fin 2, marginalCostSecond P.pole (P.measure i) (P.velocity i)

noncomputable def variationEnergy {d : Nat} (P : SphericalVariation d) : Real :=
  ∑ i : Fin 2, ∫ w, (norm (P.velocity i w))^2 ∂P.measure i

/-- The original (lambda/p)*Z_pm^(p/2), on arbitrary input measures. -/
noncomputable def metricRegularizer {d : Nat} (a : UnitSphere d) (lambda p : Real)
    (mu1 mu2 : Measure (UnitSphere d)) : Real :=
  lambda/p*(productAntipodalTransportSq a mu1 mu2)^(p/2)

noncomputable def variationRegularizer {d : Nat} (P : SphericalVariation d)
    (lambda p t : Real) : Real := lambda/p*(variationTransport P t)^(p/2)

theorem variationRegularizer_source {d : Nat} (P : SphericalVariation d) (lambda p t : Real) :
    variationRegularizer P lambda p t = metricRegularizer P.pole lambda p
      ((P.measure 0).map (sphericalExpFamily (P.velocity 0) (P.tangent 0) t))
      ((P.measure 1).map (sphericalExpFamily (P.velocity 1) (P.tangent 1) t)) := rfl

@[simp] theorem variationTransport_zero {d : Nat} (P : SphericalVariation d) :
    variationTransport P 0 = productAntipodalTransportSq P.pole (P.measure 0) (P.measure 1) := by
  have he (i : Fin 2) : sphericalExpFamily (P.velocity i) (P.tangent i) 0 = id :=
    funext (sphericalExpFamily_zero (P.velocity i) (P.tangent i))
  simp only [variationTransport, he, Measure.map_id]

theorem variationTransport_marginals {d : Nat} (P : SphericalVariation d) (t : Real) :
    variationTransport P t =
      marginalExpTransportSq P.pole (P.measure 0) (P.velocity 0) (P.tangent 0) t +
      marginalExpTransportSq P.pole (P.measure 1) (P.velocity 1) (P.tangent 1) t := rfl

/-- Integrability is an output of the original compact-cap construction. -/
theorem variation_integrable {d : Nat} (P : SphericalVariation d) (i : Fin 2) :
    Integrable (fun w => inner Real (assignedGradient P.pole w) (P.velocity i w)) (P.measure i) ∧
    Integrable (fun w => assignedHessian P.pole w (P.velocity i w)) (P.measure i) ∧
    Integrable (fun w => (norm (P.velocity i w))^2) (P.measure i) := by
  letI : IsProbabilityMeasure (P.measure i) := (P.cap i).probability
  have hi := marginalTransport_variations P.pole P.radius (P.measure i) (P.cap i)
    (P.velocity i) (P.tangent i) (P.continuous_velocity i)
  exact ⟨hi.1,hi.2.1,sphere_integrable _ _ ((P.continuous_velocity i).norm.pow 2)⟩

theorem variationEnergy_nonneg {d : Nat} (P : SphericalVariation d) : 0 ≤ variationEnergy P := by
  exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun w => sq_nonneg _))

/-- Both factors retain their original mass normalization and their factor 2. -/
theorem variationTransport_variations {d : Nat} (P : SphericalVariation d) :
    HasDerivAt (variationTransport P) (2*variationFirst P) 0 ∧
    HasDerivAt (deriv (variationTransport P)) (2*variationSecond P) 0 ∧
    (∀ᶠ t in 𝓝 (0 : Real), DifferentiableAt Real (variationTransport P) t) := by
  have h0 := marginalTransport_variations P.pole P.radius (P.measure 0) (P.cap 0)
    (P.velocity 0) (P.tangent 0) (P.continuous_velocity 0)
  have h1 := marginalTransport_variations P.pole P.radius (P.measure 1) (P.cap 1)
    (P.velocity 1) (P.tangent 1) (P.continuous_velocity 1)
  let z0 := marginalExpTransportSq P.pole (P.measure 0) (P.velocity 0) (P.tangent 0)
  let z1 := marginalExpTransportSq P.pole (P.measure 1) (P.velocity 1) (P.tangent 1)
  have he : (fun t => deriv z0 t+deriv z1 t) =ᶠ[𝓝 (0 : Real)] deriv (variationTransport P) := by
    filter_upwards [h0.2.2.2.2,h1.2.2.2.2] with t ht0 ht1
    exact (ht0.hasDerivAt.add ht1.hasDerivAt).deriv.symm
  refine ⟨?_,?_,?_⟩
  · apply (h0.2.2.1.add h1.2.2.1).congr_deriv
    simp only [variationFirst, Fin.sum_univ_two]
    ring
  · have hd := (h0.2.2.2.1.add h1.2.2.2.1).congr_of_eventuallyEq he.symm
    apply hd.congr_deriv
    simp only [variationSecond, Fin.sum_univ_two]
    ring
  · filter_upwards [h0.2.2.2.2,h1.2.2.2.2] with t ht0 ht1
    exact ht0.add ht1

/-- Literal lower and upper bounds from the pointwise spherical Hessian. -/
theorem variationSecond_bounds {d : Nat} (P : SphericalVariation d) :
    sphericalRadialWeight P.radius*variationEnergy P ≤ variationSecond P ∧
    variationSecond P ≤ variationEnergy P := by
  have hpoint (i : Fin 2) :
      sphericalRadialWeight P.radius*(∫ w, (norm (P.velocity i w))^2 ∂P.measure i) ≤
        marginalCostSecond P.pole (P.measure i) (P.velocity i) ∧
      marginalCostSecond P.pole (P.measure i) (P.velocity i) ≤
        (∫ w, (norm (P.velocity i w))^2 ∂P.measure i) := by
    letI : IsProbabilityMeasure (P.measure i) := (P.cap i).probability
    have hi := variation_integrable P i
    have hb : ∀ᵐ w ∂P.measure i,
        sphericalRadialWeight P.radius*(norm (P.velocity i w))^2 ≤ assignedHessian P.pole w (P.velocity i w) ∧
        assignedHessian P.pole w (P.velocity i w) ≤ (norm (P.velocity i w))^2 := by
      filter_upwards [Measure.support_mem_ae (μ := P.measure i)] with w hw
      have hd := assignedPole_distance_lt_cap P.pole P.radius (P.cap i).radius_lt
        ((P.cap i).support_subset hw)
      exact poleHessian_bounds (assignedPole P.pole w) w (P.velocity i w) hd.le (P.cap i).radius_lt
    constructor
    · rw [← integral_const_mul]
      exact integral_mono_ae (hi.2.2.const_mul _) hi.2.1 (hb.mono (fun w h => h.1))
    · exact integral_mono_ae hi.2.1 hi.2.2 (hb.mono (fun w h => h.2))
  constructor
  · simpa only [variationEnergy, variationSecond, Finset.mul_sum] using
      Finset.sum_le_sum (fun i _ => (hpoint i).1)
  · exact Finset.sum_le_sum (fun i _ => (hpoint i).2)

/-- A scalar chain-rule adapter; the model theorem below supplies every jet.
It is NOT an additional hypothesis on the spherical probability model. -/
theorem positive_regularizer_chain_rule
    (Z : Real → Real) (lambda p d1 d2 : Real) (hp : 2 < p)
    (hZ : 0 < Z 0) (h1 : HasDerivAt Z (2*d1) 0)
    (h2 : HasDerivAt (deriv Z) (2*d2) 0)
    (hnear : ∀ᶠ t in 𝓝 (0 : Real), DifferentiableAt Real Z t) :
    HasDerivAt (fun t => lambda/p*(Z t)^(p/2))
      (lambda*(Z 0)^(p/2-1)*d1) 0 ∧
    HasDerivAt (deriv (fun t => lambda/p*(Z t)^(p/2)))
      (lambda*(Z 0)^(p/2-1)*d2 + lambda*(p-2)*(Z 0)^(p/2-2)*d1^2) 0 := by
  have hp0 : p ≠ 0 := by linarith
  have hd := (h1.rpow_const (p := p/2) (Or.inl hZ.ne')).const_mul (lambda/p)
  have hfirst : HasDerivAt (fun t => lambda/p*(Z t)^(p/2))
      (lambda*(Z 0)^(p/2-1)*d1) 0 := by
    apply hd.congr_deriv
    field_simp [hp0]
  have hznear : ∀ᶠ t in 𝓝 (0 : Real), 0 < Z t :=
    h1.continuousAt.eventually (lt_mem_nhds hZ)
  have he : (fun t => lambda/2*(Z t)^(p/2-1)*deriv Z t)
      =ᶠ[𝓝 (0 : Real)] deriv (fun t => lambda/p*(Z t)^(p/2)) := by
    filter_upwards [hnear,hznear] with t ht hz
    have hdt := ((ht.hasDerivAt.rpow_const (p := p/2) (Or.inl hz.ne')).const_mul (lambda/p)).deriv
    rw [hdt]
    field_simp [hp0]
  have hh := ((h1.rpow_const (p := p/2-1) (Or.inl hZ.ne')).const_mul (lambda/2)).mul h2
  have hh' : HasDerivAt (fun t => lambda/2*(Z t)^(p/2-1)*deriv Z t)
      (lambda*(Z 0)^(p/2-1)*d2 + lambda*(p-2)*(Z 0)^(p/2-2)*d1^2) 0 := by
    apply hh.congr_deriv
    rw [h1.deriv]
    have hexp : p/2-1-1 = p/2-2 := by ring
    rw [hexp]
    ring
  exact ⟨hfirst,hh'.congr_of_eventuallyEq he.symm⟩

/-- Actual regularizer variation, with no supplied cost or derivative premise.
The positive-distance condition is the source's stated case split. -/
theorem metricRegularizer_positive_variations {d : Nat} (P : SphericalVariation d)
    (lambda p : Real) (hlambda : 0 < lambda) (hp : 2 < p)
    (hZ : 0 < variationTransport P 0) :
    HasDerivAt (variationRegularizer P lambda p)
      (lambda*(variationTransport P 0)^(p/2-1)*variationFirst P) 0 ∧
    HasDerivAt (deriv (variationRegularizer P lambda p))
      (lambda*(variationTransport P 0)^(p/2-1)*variationSecond P +
        lambda*(p-2)*(variationTransport P 0)^(p/2-2)*(variationFirst P)^2) 0 := by
  have h := variationTransport_variations P
  exact positive_regularizer_chain_rule (variationTransport P) lambda p
    (variationFirst P) (variationSecond P) hp hZ h.1 h.2.1 h.2.2

/-- Nonnegativity of the rank-one term, with precisely p-2, not p/2-1. -/
theorem metricRegularizer_rankOne_nonneg {d : Nat} (P : SphericalVariation d)
    {lambda p : Real} (hlambda : 0 ≤ lambda) (hp : 2 ≤ p)
    (hZ : 0 < variationTransport P 0) :
    0 ≤ lambda*(p-2)*(variationTransport P 0)^(p/2-2)*(variationFirst P)^2 := by
  exact mul_nonneg (mul_nonneg (mul_nonneg hlambda (sub_nonneg.mpr hp))
    (Real.rpow_nonneg hZ.le _)) (sq_nonneg _)

/-- The actual second derivative has the source uniform compact-cap lower bound. -/
theorem metricRegularizer_second_lower_bound {d : Nat} (P : SphericalVariation d)
    (lambda p : Real) (hlambda : 0 < lambda) (hp : 2 < p)
    (hZ : 0 < variationTransport P 0) :
    lambda*(variationTransport P 0)^(p/2-1)*sphericalRadialWeight P.radius*variationEnergy P ≤
      deriv (deriv (variationRegularizer P lambda p)) 0 := by
  rw [(metricRegularizer_positive_variations P lambda p hlambda hp hZ).2.deriv]
  have hw : 0 ≤ lambda*(variationTransport P 0)^(p/2-1) :=
    mul_nonneg hlambda.le (Real.rpow_nonneg hZ.le _)
  have hb := mul_le_mul_of_nonneg_left (variationSecond_bounds P).1 hw
  have hn := metricRegularizer_rankOne_nonneg P hlambda.le hp.le hZ
  nlinarith

end PaperFormalization.MatrixFactorization
