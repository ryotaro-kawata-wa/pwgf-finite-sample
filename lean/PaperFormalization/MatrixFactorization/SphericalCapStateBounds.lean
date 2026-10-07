import PaperFormalization.MatrixFactorization.SphericalObjectiveGradient

/-! # Uniform state bounds from the original cap conditions

The transport infimum is bounded using its proved assigned-gradient energy
formula. Consequently the actual full field is bounded uniformly on each
original closed support, including states of zero target transport.
-/
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The optimal spherical transport cost is at most the squared cap radius. -/
theorem sphericalWassersteinSq_le_cap_sq {d : Nat} (pole : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu) :
    sphericalWassersteinSq mu (antipodalMeasure pole) ≤ r^2 := by
  letI : IsProbabilityMeasure mu := hcap.probability
  rw [← assignedGradient_energy pole r mu hcap]
  calc
    _ ≤ ∫ _ : UnitSphere d, r^2 ∂mu := by
      apply integral_mono_ae (assignedGradient_norm_sq_integrable pole r mu hcap) (integrable_const _)
      filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
      rw [assignedGradient_norm_on_support pole r mu hcap w hw]
      exact pow_le_pow_left₀ (sphericalDistance_nonneg _ _)
        (assignedPole_distance_lt_cap pole r hcap.radius_lt (hcap.support_subset hw)).le 2
    _ = r^2 := by simp

theorem productAntipodalTransportSq_le_caps {d : Nat} (pole : UnitSphere d) (r : Real)
    (mu : Fin 2 → Measure (UnitSphere d)) (hcap : ∀ i, TwoCapClass pole r (mu i)) :
    productAntipodalTransportSq pole (mu 0) (mu 1) ≤ 2*r^2 := by
  have h0 := sphericalWassersteinSq_le_cap_sq pole r (mu 0) (hcap 0)
  have h1 := sphericalWassersteinSq_le_cap_sq pole r (mu 1) (hcap 1)
  unfold productAntipodalTransportSq
  linarith

/-- The bound remains finite at zero transport for every real exponent p>2. -/
theorem metricGradient_norm_le_cap {d : Nat} (pole : UnitSphere d) (r lambda p : Real)
    (mu : Fin 2 → Measure (UnitSphere d)) (hcap : ∀ i, TwoCapClass pole r (mu i))
    (hp : 2 < p) (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (mu i).support) :
    norm (metricGradient pole lambda p (mu 0) (mu 1) w) ≤
      |lambda| *(2*r^2)^(p/2-1)*r := by
  letI : IsProbabilityMeasure (mu 0) := (hcap 0).probability
  letI : IsProbabilityMeasure (mu 1) := (hcap 1).probability
  have hZ : 0 ≤ productAntipodalTransportSq pole (mu 0) (mu 1) :=
    add_nonneg (sphericalWassersteinSq_nonneg _ _) (sphericalWassersteinSq_nonneg _ _)
  have hq : norm (assignedGradient pole w) ≤ r := by
    rw [assignedGradient_norm_on_support pole r (mu i) (hcap i) w hw]
    exact (assignedPole_distance_lt_cap pole r (hcap i).radius_lt ((hcap i).support_subset hw)).le
  rw [metricGradient, norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hZ _)]
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hZ
      (productAntipodalTransportSq_le_caps pole r mu hcap) (by linarith)) (abs_nonneg lambda))
    hq (norm_nonneg _) (by positivity)

/-- The actual full field has a bound depending only on fixed data and the cap radius. -/
theorem sphericalObjectiveGradient_norm_le_cap {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (r lambda p : Real)
    (mu : Fin 2 → Measure (UnitSphere d)) (hcap : ∀ i, TwoCapClass pole r (mu i))
    (hp : 2 < p) (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2]
    (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (mu i).support) :
    norm (sphericalObjectiveGradient O a pole lambda p (mu 0) (mu 1) teacher1 teacher2 i w) ≤
      fittingCurvatureConstant d O a+|lambda| *(2*r^2)^(p/2-1)*r := by
  letI : IsProbabilityMeasure (mu 0) := (hcap 0).probability
  letI : IsProbabilityMeasure (mu 1) := (hcap 1).probability
  exact (norm_add_le _ _).trans (add_le_add
    (sphericalFittingGradient_norm_le O a (mu 0) (mu 1) teacher1 teacher2 i w)
    (metricGradient_norm_le_cap pole r lambda p mu hcap hp i w hw))

end PaperFormalization.MatrixFactorization
