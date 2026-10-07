import PaperFormalization.MatrixFactorization.CapPrimalFirstVariation
import PaperFormalization.MatrixFactorization.AntipodalPotentialField

/-! # MF24: the original regularizer's primal gradient

Verification status and conditional scope: see `MF24_VALIDATION.md`. A cap-free L1 perturbation estimate for the actual metric
regularizer bounds ANY first-variation representative almost everywhere.
Only the unconditional probability transport bound from MF23 is reused; no
AntipodalGradientData is an input. On a cap law the representative is identified
with the existing field by actual differentiation, also at zero transport.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Elementary mean-value bound on a nonnegative compact interval. -/
theorem real_rpow_increment_upper {x y K e q : Real} (hq : 1 < q)
    (hx : x ∈ Icc 0 K) (hy : y ∈ Icc 0 K) (he : 0 ≤ e) (hxy : x ≤ y+e) :
    x^q ≤ y^q + (q*K^(q-1))*e := by
  have hK : 0 ≤ K := hy.1.trans hy.2
  have hL : 0 ≤ q*K^(q-1) := mul_nonneg (by linarith) (Real.rpow_nonneg hK _)
  by_cases horder : x ≤ y
  · exact (Real.rpow_le_rpow hx.1 horder (by linarith)).trans
      (le_add_of_nonneg_right (mul_nonneg hL he))
  have hyx : y ≤ x := (lt_of_not_ge horder).le
  have hd (s : Real) (hs : s ∈ Icc 0 K) :
      HasDerivAt (fun t : Real => t^q) (q*s^(q-1)) s := by
    simpa only [one_mul, id_eq] using
      (hasDerivAt_id s).rpow_const (p := q) (Or.inr hq.le)
  have hb (s : Real) (hs : s ∈ Icc 0 K) : norm (q*s^(q-1)) ≤ q*K^(q-1) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hs.1 _))]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs.1 hs.2 (by linarith)) (by linarith)
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hd s hs).hasDerivWithinAt) hb (convex_Icc (0 : Real) K) hy hx
  simp only [Real.norm_eq_abs] at hm
  rw [abs_of_nonneg (sub_nonneg.mpr hyx)] at hm
  have hdiff : x-y ≤ e := by linarith
  have hu := (le_abs_self (x^q-y^q)).trans hm
  have hlast := mul_le_mul_of_nonneg_left hdiff hL
  linarith

noncomputable def partialMetricFunctional {d : Nat} (pole : UnitSphere d)
    (lambda p : Real) (other : Measure (UnitSphere d)) (mu : Measure (UnitSphere d)) : Real :=
  metricRegularizer pole lambda p mu other

noncomputable def primalMetricSpeedBound (lambda p : Real) : Real :=
  lambda*(2*Real.pi^2)^(p/2-1)*Real.pi

theorem primalMetricSpeedBound_nonneg {lambda p : Real} (hl : 0 ≤ lambda) :
    0 ≤ primalMetricSpeedBound lambda p := by
  unfold primalMetricSpeedBound
  positivity

/-- The bound is for the actual all-coupling regularizer, before any gradient
representation is supplied. Its constant is independent of state and support. -/
theorem BoundedTangentTest.metric_upper_near_zero {d : Nat} (V : BoundedTangentTest d)
    (pole : UnitSphere d) (lambda p : Real) (hl : 0 ≤ lambda) (hp : 2 < p)
    (mu other : Measure (UnitSphere d)) [IsProbabilityMeasure mu] [IsProbabilityMeasure other] :
    ∀ᶠ t in 𝓝 (0 : Real),
      partialMetricFunctional pole lambda p other (V.push mu t) ≤
        partialMetricFunctional pole lambda p other mu +
          (primalMetricSpeedBound lambda p*(∫ w, norm (V.field w) ∂mu))*|t| := by
  have hp0 : p ≠ 0 := by linarith
  have hI : 0 ≤ ∫ w, norm (V.field w) ∂mu := integral_nonneg (fun w => norm_nonneg _)
  have hbase := productAntipodalTransportSq_global_bounds pole mu other
  filter_upwards [V.transport_upper_near_zero mu (antipodalMeasure pole)] with t ht
  letI : IsProbabilityMeasure (V.push mu t) := V.push_probability mu t
  have hnew := productAntipodalTransportSq_global_bounds pole (V.push mu t) other
  have he : 0 ≤ (2*Real.pi*(∫ w, norm (V.field w) ∂mu))*|t| := by positivity
  have hinc : productAntipodalTransportSq pole (V.push mu t) other ≤
      productAntipodalTransportSq pole mu other + (2*Real.pi*(∫ w, norm (V.field w) ∂mu))*|t| := by
    unfold productAntipodalTransportSq
    linarith
  have hh := real_rpow_increment_upper (q := p/2) (by linarith) hnew hbase he hinc
  have hs := mul_le_mul_of_nonneg_left hh (div_nonneg hl (by linarith : 0 ≤ p))
  unfold partialMetricFunctional metricRegularizer primalMetricSpeedBound
  convert hs using 1
  all_goals first | rfl | (field_simp [hp0] <;> ring)

/-- Global AE boundedness for the regularizer, from its primal first variation. -/
theorem primalMetricGradient_norm_le {d : Nat} (pole : UnitSphere d)
    (lambda p : Real) (hl : 0 ≤ lambda) (hp : 2 < p)
    (mu other : Measure (UnitSphere d)) [IsProbabilityMeasure mu] [IsProbabilityMeasure other]
    (g : UnitSphere d → Weight d)
    (H : HasSphereFirstVariation mu (partialMetricFunctional pole lambda p other) g) :
    ∀ᵐ w ∂mu, norm (g w) ≤ primalMetricSpeedBound lambda p :=
  H.norm_le_of_upper _ (primalMetricSpeedBound_nonneg hl)
    (fun V => V.metric_upper_near_zero pole lambda p hl hp mu other)

/-- Actual local first variation for a cap marginal. The fixed other marginal
need only be a probability; zero product transport is included for every p>2. -/
theorem cap_partialMetric_firstVariation {d : Nat} (pole : UnitSphere d)
    (r lambda p : Real) (hp : 2 < p) (mu other : Measure (UnitSphere d))
    (hc : TwoCapClass pole r mu) [IsProbabilityMeasure other] :
    HasSphereFirstVariation mu (partialMetricFunctional pole lambda p other)
      (metricGradient pole lambda p mu other) := by
  letI : IsProbabilityMeasure mu := hc.probability
  refine ⟨metricGradient_measurable pole lambda p mu other,
    Eventually.of_forall (metricGradient_tangent pole lambda p mu other), ?_, ?_⟩
  · simpa only [metricGradient, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] using
      (assignedGradient_norm_sq_integrable pole r mu hc).const_mul
        (lambda^2*((productAntipodalTransportSq pole mu other)^(p/2-1))^2)
  · intro V
    have hZ : HasDerivAt (fun t => productAntipodalTransportSq pole (V.push mu t) other)
        (2*(∫ w, inner Real (assignedGradient pole w) (V.field w) ∂mu)) 0 := by
      have hd := ((V.cap_halfTransport_derivative pole r mu hc).const_mul 2).add_const
        (sphericalWassersteinSq other (antipodalMeasure pole))
      apply hd.congr_of_eventuallyEq
      filter_upwards with t
      unfold productAntipodalTransportSq halfTransportFunctional
      ring
    have hR := (hZ.rpow_const (p := p/2) (Or.inr (by linarith))).const_mul (lambda/p)
    change HasDerivAt (fun t => lambda/p*(productAntipodalTransportSq pole (V.push mu t) other)^(p/2)) _ 0
    apply hR.congr_deriv
    simp only [V.push_zero, metricGradient, real_inner_smul_left, integral_const_mul]
    field_simp [show p ≠ 0 by linarith] <;> ring

/-- Local identification of any regularizer representative as an L2 measure
class. No all-support classical potential representation is needed. -/
theorem cap_primalMetricGradient_eq_ae {d : Nat} (pole : UnitSphere d)
    (r lambda p : Real) (hp : 2 < p) (mu other : Measure (UnitSphere d))
    (hc : TwoCapClass pole r mu) [IsProbabilityMeasure other]
    (g : UnitSphere d → Weight d)
    (H : HasSphereFirstVariation mu (partialMetricFunctional pole lambda p other) g) :
    g =ᵐ[mu] metricGradient pole lambda p mu other := by
  letI : IsProbabilityMeasure mu := hc.probability
  exact H.unique_ae (cap_partialMetric_firstVariation pole r lambda p hp mu other hc)

end PaperFormalization.MatrixFactorization
