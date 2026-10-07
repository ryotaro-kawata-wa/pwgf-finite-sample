import PaperFormalization.MatrixFactorization.ContractionFeatureIntegral
import PaperFormalization.MatrixFactorization.SphericalFittingGradientSymmetry
import PaperFormalization.MatrixFactorization.SphericalTransportSymmetry
import PaperFormalization.MatrixFactorization.AntisymmetricFittingForce

/-! # The actual radial fitting pairing under original cap measures

The assigned radial gradient is used as a measurable integrable field.
Fubini connects its Gaussian fitting pairing to the actual derivative of the
assigned-pole contraction mean feature. No global continuity of q is assumed.
-/
open MeasureTheory ProbabilityTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def radialFittingIntegrand {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (mu teacher : Measure (UnitSphere d))
    (w : UnitSphere d) (z : Weight d) : Real :=
  inner Real (fittingGradientIntegrand O a mu (reflectedMeasure mu) teacher teacher 0 w z)
    (assignedGradient pole w)

theorem radialFittingIntegrand_integrable_prod {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    Integrable (fun wz : UnitSphere d × Weight d => radialFittingIntegrand O a pole mu teacher wz.1 wz.2)
      (mu.prod (stdGaussian (Weight d))) := by
  letI : IsProbabilityMeasure mu := hcap.probability
  have hb := (assignedGradient_integrable pole r mu hcap).norm.mul_prod
    ((fittingCurvatureConstant_integrable d O a).const_mul 4)
  have hm := (fittingGradientIntegrand_stronglyMeasurable O a mu (reflectedMeasure mu)
    teacher teacher 0).inner (𝕜 := Real)
    ((assignedGradient_measurable pole).stronglyMeasurable.comp_measurable measurable_fst)
  apply hb.mono' hm.aestronglyMeasurable
  apply Eventually.of_forall
  intro wz
  change norm (inner Real (fittingGradientIntegrand O a mu (reflectedMeasure mu)
    teacher teacher 0 wz.1 wz.2) (assignedGradient pole wz.1)) ≤ _
  rw [Real.norm_eq_abs]
  calc
    _ ≤ norm (fittingGradientIntegrand O a mu (reflectedMeasure mu) teacher teacher 0 wz.1 wz.2)*
        norm (assignedGradient pole wz.1) := abs_real_inner_le_norm _ _
    _ ≤ (4*(fittingFeatureEnvelope O a wz.2)^4)*norm (assignedGradient pole wz.1) :=
      mul_le_mul_of_nonneg_right
        (fittingGradientIntegrand_norm_le O a mu (reflectedMeasure mu) teacher teacher 0 wz.1 wz.2)
        (norm_nonneg _)
    _ = _ := mul_comm _ _

theorem radialFittingIntegrand_sphere_integral {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (pole : UnitSphere d)
    (mu teacher : Measure (UnitSphere d)) [IsFiniteMeasure mu] (z : Weight d) :
    (∫ w, radialFittingIntegrand O a pole mu teacher w z ∂mu) =
      inner Real (antisymmetricOutputForce O a mu teacher z)
        (meanFeatureAlongContractionFirst 0 O a pole mu z 1) := by
  have he (w : UnitSphere d) : radialFittingIntegrand O a pole mu teacher w z =
      inner Real (antisymmetricOutputForce O a mu teacher z)
        (contractionFeatureFirst 0 O a pole w z 1) := by
    rw [radialFittingIntegrand, real_inner_comm,
      fittingGradientIntegrand_pairing O a mu (reflectedMeasure mu) teacher teacher 0 w
        (assignedGradient pole w) z (assignedGradient_tangent pole w),
      fittingOutputGradient_antibranch_zero O a hO]
    change _ = inner Real _ (inner Real (assignedContractionVelocity pole 1 w) z •
      finiteHermiteActivationJet 1 O a (inner Real (assignedContraction pole 1 w).val z))
    rw [assignedContractionVelocity_one, assignedContraction_one, real_inner_smul_right]
    ring
  simp_rw [he]
  exact integral_inner (contractionFeature_integrable 0 O a pole mu z 1).2.1 _

/-- The first-factor radial pairing is a genuine exchange of two integrals. -/
theorem sphericalFittingGradient_radial_pairing {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (pole : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    (∫ w, inner Real (sphericalFittingGradient O a mu (reflectedMeasure mu) teacher teacher 0 w)
      (assignedGradient pole w) ∂mu) =
    ∫ z, inner Real (antisymmetricOutputForce O a mu teacher z)
      (meanFeatureAlongContractionFirst 0 O a pole mu z 1) ∂stdGaussian (Weight d) := by
  letI : IsProbabilityMeasure mu := hcap.probability
  have he (w : UnitSphere d) : inner Real
      (sphericalFittingGradient O a mu (reflectedMeasure mu) teacher teacher 0 w) (assignedGradient pole w) =
      ∫ z, radialFittingIntegrand O a pole mu teacher w z ∂stdGaussian (Weight d) := by
    rw [real_inner_comm, sphericalFittingGradient, ← integral_inner
      (fittingGradientIntegrand_integrable O a mu (reflectedMeasure mu) teacher teacher 0 w)]
    exact integral_congr_ae (Eventually.of_forall (fun z => real_inner_comm _ _))
  simp_rw [he]
  rw [integral_integral_swap (radialFittingIntegrand_integrable_prod O a pole r mu hcap teacher)]
  exact integral_congr_ae (Eventually.of_forall
    (radialFittingIntegrand_sphere_integral O a hO pole mu teacher))

/-- Reflection gives equal contributions from the two original branch marginals. -/
theorem sphericalFittingGradient_radial_reflected {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (pole : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    (∫ w, inner Real (sphericalFittingGradient O a mu (reflectedMeasure mu) teacher teacher 1 w)
      (assignedGradient pole w) ∂reflectedMeasure mu) =
    ∫ w, inner Real (sphericalFittingGradient O a mu (reflectedMeasure mu) teacher teacher 0 w)
      (assignedGradient pole w) ∂mu := by
  letI : IsProbabilityMeasure mu := hcap.probability
  have hm := (sphericalFittingGradient_continuous O a mu (reflectedMeasure mu)
    teacher teacher 1).stronglyMeasurable.inner (𝕜 := Real)
    (assignedGradient_measurable pole).stronglyMeasurable
  change (∫ w, inner Real (sphericalFittingGradient O a mu (reflectedMeasure mu)
    teacher teacher 1 w) (assignedGradient pole w) ∂mu.map reflect) = _
  rw [integral_map (reflect_measurable d).aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hcap.ae_caps] with w hw
  rw [sphericalFittingGradient_antibranch O a hO mu teacher 1 w,
    assignedGradient_reflected_on_caps pole r hcap.radius_lt hw, inner_neg_neg]
  rfl

noncomputable def antisymmetricRadialFittingPairing {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (mu teacher : Measure (UnitSphere d)) : Real :=
  (∫ w, inner Real (sphericalFittingGradient O a mu (reflectedMeasure mu) teacher teacher 0 w)
    (assignedGradient pole w) ∂mu) +
  (∫ w, inner Real (sphericalFittingGradient O a mu (reflectedMeasure mu) teacher teacher 1 w)
    (assignedGradient pole w) ∂reflectedMeasure mu)

/-- The actual product radial force is identified before any remainder estimate. -/
theorem antisymmetricRadialFittingPairing_eq {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (pole : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    antisymmetricRadialFittingPairing O a pole mu teacher =
      2*∫ z, inner Real (antisymmetricOutputForce O a mu teacher z)
        (meanFeatureAlongContractionFirst 0 O a pole mu z 1) ∂stdGaussian (Weight d) := by
  rw [antisymmetricRadialFittingPairing,
    sphericalFittingGradient_radial_reflected O a hO pole r mu hcap teacher,
    sphericalFittingGradient_radial_pairing O a hO pole r mu hcap teacher]
  ring

end PaperFormalization.MatrixFactorization
