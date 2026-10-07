import PaperFormalization.MatrixFactorization.AntipodalPotentialGradient
import PaperFormalization.MatrixFactorization.SphericalObjectiveGradient

/-! # MF23: a cap-free bound for a dual-represented full field

Execution records: `MF23_VALIDATION.md`.

The full field is the verified Gaussian fitting field
plus a differential of an optimal potential for the TRUE transport infimum.
The statewise representation is explicit. No theorem here asserts that every
weak WGF admits a classical dual differential at every support point.
-/
open MeasureTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Explicit representation data for a classical spherical transport gradient.
Existence outside the cap class is not a theorem of this structure. -/
structure AntipodalGradientData {d : Nat} (pole : UnitSphere d)
    (mu : Measure (UnitSphere d)) where
  weight : Real
  optimal : AntipodalPotentialOptimal pole mu weight
  gradient : UnitSphere d -> Weight d
  measurable_gradient : Measurable gradient
  differential : ∀ w, w ∈ mu.support ->
    HasSpherePotentialGradient (antipodalPotential pole weight) w (gradient w)

theorem AntipodalGradientData.norm_le_pi {d : Nat} {pole : UnitSphere d}
    {mu : Measure (UnitSphere d)} (G : AntipodalGradientData pole mu)
    {w : UnitSphere d} (hw : w ∈ mu.support) : norm (G.gradient w) <= Real.pi :=
  antipodalPotential_gradient_norm_le pole w G.weight (G.gradient w) (G.differential w hw)

/-- The representation does not assume its local agreement with MF12. -/
theorem AntipodalGradientData.eq_assigned_on_caps {d : Nat} {pole : UnitSphere d}
    {mu : Measure (UnitSphere d)} (G : AntipodalGradientData pole mu)
    (r : Real) (hc : TwoCapClass pole r mu) {w : UnitSphere d} (hw : w ∈ mu.support) :
    G.gradient w = assignedGradient pole w :=
  antipodalPotential_gradient_eq_assigned pole r G.weight mu hc G.optimal hw
    (G.gradient w) (G.differential w hw)

/-- An explicit representation exists for the already verified cap model. -/
noncomputable def AntipodalGradientData.onCaps {d : Nat} (pole : UnitSphere d)
    (r : Real) (mu : Measure (UnitSphere d)) (hc : TwoCapClass pole r mu) :
    AntipodalGradientData pole mu where
  weight := 0
  optimal := antipodalPotential_zero_optimal pole r mu hc
  gradient := assignedGradient pole
  measurable_gradient := assignedGradient_measurable pole
  differential := by
    intro w hw
    refine ⟨ assignedGradient_tangent pole w, ?_ ⟩
    intro v hv
    have hd := (assignedCost_exp_variations pole w r hc.radius_lt
      (hc.support_subset hw) v hv).1
    simpa only [antipodalPotential_zero] using hd

/-- All probability laws, not just cap laws, have bounded angular transport. -/
theorem sphericalWassersteinSq_le_pi_sq_global {d : Nat}
    (mu nu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    sphericalWassersteinSq mu nu <= Real.pi^2 :=
  (sphericalWassersteinSq_le_cost (productSphericalCoupling mu nu)).trans
    (sphericalTransportCost_le_pi_sq (productSphericalCoupling mu nu))

theorem productAntipodalTransportSq_global_bounds {d : Nat} (pole : UnitSphere d)
    (mu0 mu1 : Measure (UnitSphere d)) [IsProbabilityMeasure mu0] [IsProbabilityMeasure mu1] :
    0 <= productAntipodalTransportSq pole mu0 mu1 ∧
      productAntipodalTransportSq pole mu0 mu1 <= 2*Real.pi^2 := by
  constructor
  · exact add_nonneg (sphericalWassersteinSq_nonneg _ _) (sphericalWassersteinSq_nonneg _ _)
  · have h0 := sphericalWassersteinSq_le_pi_sq_global mu0 (antipodalMeasure pole)
    have h1 := sphericalWassersteinSq_le_pi_sq_global mu1 (antipodalMeasure pole)
    change sphericalWassersteinSq _ _ + sphericalWassersteinSq _ _ <= _
    linarith

noncomputable def potentialFullGradient {d h : Nat} (O : Finset Nat)
    (a : Nat -> Weight h) (pole : UnitSphere d) (lambda p : Real)
    (mu : Fin 2 -> Measure (UnitSphere d)) (teacher : Measure (UnitSphere d))
    (G : ∀ i, AntipodalGradientData pole (mu i)) (i : Fin 2) (w : UnitSphere d) : Weight d :=
  sphericalFittingGradient O a (mu 0) (mu 1) teacher teacher i w +
    (lambda*(productAntipodalTransportSq pole (mu 0) (mu 1))^(p/2-1)) • (G i).gradient w

/-- This constant has no dependence on cap radius, state, dual weights, time,
or particle label. It is a domination constant, not a sharp basin constant. -/
noncomputable def potentialSpeedBound (d : Nat) {h : Nat} (O : Finset Nat)
    (a : Nat -> Weight h) (lambda p : Real) : Real :=
  fittingCurvatureConstant d O a + |lambda| * (2*Real.pi^2)^(p/2-1)*Real.pi

theorem potentialSpeedBound_nonneg (d : Nat) {h : Nat} (O : Finset Nat)
    (a : Nat -> Weight h) (lambda p : Real) : 0 <= potentialSpeedBound d O a lambda p := by
  have h := fittingCurvatureConstant_nonneg d O a
  unfold potentialSpeedBound
  positivity

/-- A uniform speed bound derived before any cap membership is available. -/
theorem potentialFullGradient_norm_le {d h : Nat} (O : Finset Nat)
    (a : Nat -> Weight h) (pole : UnitSphere d) (lambda p : Real) (hp : 2 < p)
    (mu : Fin 2 -> Measure (UnitSphere d)) (hprob : ∀ i, IsProbabilityMeasure (mu i))
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (G : ∀ i, AntipodalGradientData pole (mu i)) (i : Fin 2)
    (w : UnitSphere d) (hw : w ∈ (mu i).support) :
    norm (potentialFullGradient O a pole lambda p mu teacher G i w) <=
      potentialSpeedBound d O a lambda p := by
  letI := hprob 0
  letI := hprob 1
  have hZ := productAntipodalTransportSq_global_bounds pole (mu 0) (mu 1)
  have hpw := Real.rpow_le_rpow hZ.1 hZ.2 (by linarith : 0 <= p/2-1)
  unfold potentialFullGradient
  apply (norm_add_le _ _).trans
  rw [norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hZ.1 _)]
  exact add_le_add (sphericalFittingGradient_norm_le O a (mu 0) (mu 1) teacher teacher i w)
    (mul_le_mul (mul_le_mul_of_nonneg_left hpw (abs_nonneg lambda))
      ((G i).norm_le_pi hw) (norm_nonneg _) (by positivity))

/-- Local equality with the source field is derived, not installed outside caps. -/
theorem potentialFullGradient_eq_source {d h : Nat} (O : Finset Nat)
    (a : Nat -> Weight h) (pole : UnitSphere d) (r lambda p : Real)
    (mu : Fin 2 -> Measure (UnitSphere d)) (hc : ∀ i, TwoCapClass pole r (mu i))
    (teacher : Measure (UnitSphere d)) (G : ∀ i, AntipodalGradientData pole (mu i))
    (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (mu i).support) :
    potentialFullGradient O a pole lambda p mu teacher G i w =
      sphericalObjectiveGradient O a pole lambda p (mu 0) (mu 1) teacher teacher i w := by
  simp only [potentialFullGradient, sphericalObjectiveGradient, metricGradient,
    (G i).eq_assigned_on_caps r (hc i) hw]

end PaperFormalization.MatrixFactorization
