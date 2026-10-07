import PaperFormalization.MatrixFactorization.AntisymmetricFittingForce

/-! # Actual first variations along the antisymmetric branch

The original state and continuous product velocity obey reflection
compatibility. Their original-measure feature derivatives therefore have
opposite signs, and the Gaussian fitting derivative has the exact branch
force formula. No global continuity of the assigned-pole gradient is used.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

theorem variationFeature_antibranch_initial {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (P : SphericalVariation d)
    (hmu : P.measure 1 = reflectedMeasure (P.measure 0)) (z : Weight d) :
    variationFeature O a P 1 0 z = -variationFeature O a P 0 0 z := by
  letI : IsProbabilityMeasure (P.measure 0) := (P.cap 0).probability
  simp only [variationFeature_initial, hmu]
  exact meanFeature_reflected _ (finiteHermiteActivation_continuous O a)
    (finiteHermiteActivation_odd O a hO) (P.measure 0) z

/-- Reflection-compatible continuous velocities give the actual opposite
mean-feature derivatives after integration under the original measures. -/
theorem variationFeatureFirst_antibranch_initial {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (P : SphericalVariation d)
    (hmu : P.measure 1 = reflectedMeasure (P.measure 0))
    (hv : ∀ w, P.velocity 1 (reflect w) = -P.velocity 0 w) (z : Weight d) :
    variationFeatureFirst O a P 1 0 z = -variationFeatureFirst O a P 0 0 z := by
  simp only [variationFeatureFirst, meanFeatureJetAlongExpFirst,
    sphericalFeatureFirst_at_zero, zero_add]
  rw [hmu, integral_reflectedMeasure (P.measure 0)
    (fun w => inner Real (P.velocity 1 w) z •
      finiteHermiteActivationJet 1 O a (inner Real w.val z))
    (((P.continuous_velocity 1).inner (𝕜 := Real) continuous_const).smul
      ((finiteHermiteActivationJet_continuous 1 O a).comp
        (continuous_subtype_val.inner (𝕜 := Real) continuous_const)))]
  simp only [hv, reflect_val, inner_neg_left,
    finiteHermiteActivationJet_one_even O a hO, neg_smul, integral_neg]

/-- This is the simultaneous variation of both original output factors. -/
theorem variationMatrixFirst_antibranch {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (P : SphericalVariation d)
    (hmu : P.measure 1 = reflectedMeasure (P.measure 0))
    (hv : ∀ w, P.velocity 1 (reflect w) = -P.velocity 0 w)
    (teacher : Measure (UnitSphere d)) (z : Weight d) :
    variationMatrixFirst O a P teacher teacher 0 z =
      2*inner Real (antisymmetricOutputForce O a (P.measure 0) teacher z)
        (variationFeatureFirst O a P 0 0 z) := by
  simp only [variationMatrixFirst, teacherOutput,
    variationFeature_antibranch_initial O a hO P hmu z,
    variationFeatureFirst_antibranch_initial O a hO P hmu hv z,
    matrixPointFirst_antibranch, variationFeature_initial, antisymmetricOutputForce]

/-- The original Gaussian integral has the same exact factor two. -/
theorem variationFittingFirst_antibranch {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (P : SphericalVariation d)
    (hmu : P.measure 1 = reflectedMeasure (P.measure 0))
    (hv : ∀ w, P.velocity 1 (reflect w) = -P.velocity 0 w)
    (teacher : Measure (UnitSphere d)) :
    variationFittingFirst O a P teacher teacher 0 =
      2*∫ z, inner Real (antisymmetricOutputForce O a (P.measure 0) teacher z)
        (variationFeatureFirst O a P 0 0 z) ∂stdGaussian (Weight d) := by
  simp only [variationFittingFirst, variationMatrixFirst_antibranch O a hO P hmu hv,
    integral_const_mul]

/-- The exact branch force computes the derivative of the actual normalized
source perturbation, with no output-derivative premise. -/
theorem normalized_fitting_antibranch_variation {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (P : SphericalVariation d)
    (hmu : P.measure 1 = reflectedMeasure (P.measure 0))
    (hv : ∀ w, P.velocity 1 (reflect w) = -P.velocity 0 w)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    HasDerivAt (variationRetractedFitting O a P teacher teacher)
      (2*∫ z, inner Real (antisymmetricOutputForce O a (P.measure 0) teacher z)
        (variationFeatureFirst O a P 0 0 z) ∂stdGaussian (Weight d)) 0 :=
  (variationRetractedFitting_initial_variations O a P teacher teacher).1.congr_deriv
    (variationFittingFirst_antibranch O a hO P hmu hv teacher)

end PaperFormalization.MatrixFactorization
