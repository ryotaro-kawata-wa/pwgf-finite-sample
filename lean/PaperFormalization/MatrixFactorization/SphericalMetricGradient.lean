import PaperFormalization.MatrixFactorization.GeneralRetractionObjective

/-! # The actual metric gradient as a function of the original product state

The field depends on the two measures and the fixed parameters, not on a
chosen perturbation direction. Its integrability and exact L2 norm follow
from the original closed-support cap class and the optimal transport formula.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

theorem assignedGradient_measurable {d : Nat} (pole : UnitSphere d) :
    Measurable (assignedGradient pole) :=
  (poleGradient_measurable d).comp (f := fun w : UnitSphere d => (assignedPole pole w,w))
    ((assignedPole_measurable pole).prodMk measurable_id)

theorem assignedGradient_tangent {d : Nat} (pole w : UnitSphere d) :
    inner Real w.val (assignedGradient pole w) = 0 := poleGradient_tangent _ _

theorem assignedGradient_norm_on_support {d : Nat} (pole : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (w : UnitSphere d) (hw : w ∈ mu.support) :
    norm (assignedGradient pole w) = sphericalDistance w (assignedPole pole w) := by
  have hd := assignedPole_distance_lt_cap pole r hcap.radius_lt (hcap.support_subset hw)
  exact poleGradient_norm _ _ (by linarith [hcap.radius_lt,Real.pi_pos])

theorem assignedGradient_integrable {d : Nat} (pole : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu) :
    Integrable (assignedGradient pole) mu := by
  letI : IsProbabilityMeasure mu := hcap.probability
  apply Integrable.of_bound (assignedGradient_measurable pole).aestronglyMeasurable r
  filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
  rw [assignedGradient_norm_on_support pole r mu hcap w hw]
  exact (assignedPole_distance_lt_cap pole r hcap.radius_lt (hcap.support_subset hw)).le

theorem assignedGradient_norm_sq_integrable {d : Nat} (pole : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu) :
    Integrable (fun w => norm (assignedGradient pole w)^2) mu := by
  letI : IsProbabilityMeasure mu := hcap.probability
  apply Integrable.of_bound ((assignedGradient_measurable pole).norm.pow_const 2).aestronglyMeasurable (r^2)
  filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), assignedGradient_norm_on_support pole r mu hcap w hw]
  exact pow_le_pow_left₀ (sphericalDistance_nonneg _ _)
    (assignedPole_distance_lt_cap pole r hcap.radius_lt (hcap.support_subset hw)).le 2

/-- The radial field's actual squared L2 norm is the original transport cost. -/
theorem assignedGradient_energy {d : Nat} (pole : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu) :
    (∫ w, norm (assignedGradient pole w)^2 ∂mu) = sphericalWassersteinSq mu (antipodalMeasure pole) := by
  rw [sphericalWassersteinSq_antipodal pole r mu hcap, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
  rw [assignedGradient_norm_on_support pole r mu hcap w hw]
  unfold assignedCost
  ring

noncomputable def metricGradient {d : Nat} (pole : UnitSphere d) (lambda p : Real)
    (mu1 mu2 : Measure (UnitSphere d)) (w : UnitSphere d) : Weight d :=
  (lambda*(productAntipodalTransportSq pole mu1 mu2)^(p/2-1)) • assignedGradient pole w

theorem metricGradient_tangent {d : Nat} (pole : UnitSphere d) (lambda p : Real)
    (mu1 mu2 : Measure (UnitSphere d)) (w : UnitSphere d) :
    inner Real w.val (metricGradient pole lambda p mu1 mu2 w) = 0 := by
  simp only [metricGradient, inner_smul_right, assignedGradient_tangent, mul_zero]

theorem metricGradient_measurable {d : Nat} (pole : UnitSphere d) (lambda p : Real)
    (mu1 mu2 : Measure (UnitSphere d)) : Measurable (metricGradient pole lambda p mu1 mu2) := by
  unfold metricGradient
  exact (measurable_const (a := lambda*(productAntipodalTransportSq pole mu1 mu2)^(p/2-1))).smul
    (assignedGradient_measurable pole)

theorem metricGradient_integrable {d : Nat} (P : SphericalVariation d)
    (lambda p : Real) (i : Fin 2) :
    Integrable (metricGradient P.pole lambda p (P.measure 0) (P.measure 1)) (P.measure i) := by
  unfold metricGradient
  exact (assignedGradient_integrable P.pole P.radius (P.measure i) (P.cap i)).smul
    (lambda*(productAntipodalTransportSq P.pole (P.measure 0) (P.measure 1))^(p/2-1))

theorem regularizerGradient_eq_metricGradient {d : Nat} (P : SphericalVariation d)
    (lambda p : Real) : regularizerGradient P lambda p =
      metricGradient P.pole lambda p (P.measure 0) (P.measure 1) := by
  funext w
  simp only [regularizerGradient,metricGradient,variationTransport_zero]

theorem metricGradient_zero_transport {d : Nat} (pole : UnitSphere d) (lambda p : Real)
    (mu1 mu2 : Measure (UnitSphere d)) (hp : 2 < p)
    (hZ : productAntipodalTransportSq pole mu1 mu2 = 0) :
    metricGradient pole lambda p mu1 mu2 = 0 := by
  funext w
  simp only [metricGradient,hZ,Real.zero_rpow (by linarith : p/2-1 ≠ 0),mul_zero,zero_smul,Pi.zero_apply]

/-- The gradient norm is exact, rather than merely a bound for a ray model. -/
theorem metricGradient_energy {d : Nat} (P : SphericalVariation d) (lambda p : Real) :
    (∑ i : Fin 2, ∫ w, norm (metricGradient P.pole lambda p (P.measure 0) (P.measure 1) w)^2 ∂P.measure i) =
      (lambda*(variationTransport P 0)^(p/2-1))^2 * variationTransport P 0 := by
  simp only [metricGradient,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,integral_const_mul,
    Fin.sum_univ_two,assignedGradient_energy P.pole P.radius (P.measure 0) (P.cap 0),
    assignedGradient_energy P.pole P.radius (P.measure 1) (P.cap 1),variationTransport_zero]
  unfold productAntipodalTransportSq
  ring

theorem normalized_metricGradient_first_variation {d : Nat} (P : SphericalVariation d)
    (lambda p : Real) (hp : 2 < p) :
    HasDerivAt (variationRetractedRegularizer P lambda p)
      (∑ i : Fin 2, ∫ w, inner Real
        (metricGradient P.pole lambda p (P.measure 0) (P.measure 1) w) (P.velocity i w) ∂P.measure i) 0 := by
  rw [← regularizerGradient_eq_metricGradient P lambda p, regularizerGradient_pairing]
  rcases eq_or_lt_of_le (variationTransport_initial_nonneg P) with hz | hz
  · have hd := (metricRegularizer_retracted_zero_variations P lambda p hp hz.symm).1
    simpa only [hz.symm,Real.zero_rpow (by linarith : p/2-1 ≠ 0),mul_zero,zero_mul] using hd
  · exact (metricRegularizer_retracted_positive_variations P lambda p hp hz).1

end PaperFormalization.MatrixFactorization
