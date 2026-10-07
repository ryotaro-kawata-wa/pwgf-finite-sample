import PaperFormalization.MatrixFactorization.SphericalFeatureGaussian

/-! # MF04: one Gaussian envelope for the fitting construction

The degree is deliberately an upper bound, not a claim about the minimal degree.
All constants are obtained from the given finite Hermite coefficients. This
envelope controls the original teacher feature and all three student jets.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def fittingFeatureDegree (O : Finset Nat) : Nat :=
  hermiteJetOrder 0 O + (hermiteJetOrder 1 O+1) +
    (hermiteJetOrder 2 O+2) + activationOrder O

noncomputable def fittingFeatureMass {h : Nat} (O : Finset Nat) (a : Nat → Weight h) : Real :=
  activationJetMass 0 O a + 2*activationJetMass 1 O a +
    activationJetMass 2 O a + activationMass O a

noncomputable def fittingFeatureEnvelope {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (z : Weight d) : Real :=
  fittingFeatureMass O a * (1+norm z)^fittingFeatureDegree O

theorem fittingFeatureMass_nonneg {h : Nat} (O : Finset Nat) (a : Nat → Weight h) :
    0 ≤ fittingFeatureMass O a := by
  have h0 := activationJetMass_nonneg 0 O a
  have h1 := activationJetMass_nonneg 1 O a
  have h2 := activationJetMass_nonneg 2 O a
  have ht := activationMass_nonneg O a
  unfold fittingFeatureMass
  positivity

theorem fittingFeatureEnvelope_nonneg {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (z : Weight d) : 0 ≤ fittingFeatureEnvelope O a z :=
  mul_nonneg (fittingFeatureMass_nonneg O a) (by positivity)

theorem fittingFeatureEnvelope_bounds {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (z : Weight d) :
    featureEnvelope 0 O a z ≤ fittingFeatureEnvelope O a z ∧
    featureFirstEnvelope 0 O a z ≤ fittingFeatureEnvelope O a z ∧
    featureSecondEnvelope 0 O a z ≤ fittingFeatureEnvelope O a z ∧
    activationMass O a*(1+norm z)^activationOrder O ≤ fittingFeatureEnvelope O a z := by
  have h0 := activationJetMass_nonneg 0 O a
  have h1 := activationJetMass_nonneg 1 O a
  have h2 := activationJetMass_nonneg 2 O a
  have ht := activationMass_nonneg O a
  have lift (C : Real) (M : Nat) (hC : C ≤ fittingFeatureMass O a)
      (hM : M ≤ fittingFeatureDegree O) :
      C*(1+norm z)^M ≤ fittingFeatureEnvelope O a z := by
    exact mul_le_mul hC (pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg z)) hM)
      (by positivity) (fittingFeatureMass_nonneg O a)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact lift _ _ (by unfold fittingFeatureMass; linarith)
      (by unfold fittingFeatureDegree; omega)
  · exact (featureFirstEnvelope_polynomial_bound 0 O a z).trans
      (lift _ _ (by unfold fittingFeatureMass; norm_num; linarith)
        (by unfold fittingFeatureDegree; norm_num; omega))
  · exact (featureSecondEnvelope_polynomial_bound 0 O a z).trans
      (lift _ _ (by unfold fittingFeatureMass; norm_num; linarith)
        (by unfold fittingFeatureDegree; norm_num; omega))
  · exact lift _ _ (by unfold fittingFeatureMass; linarith)
      (by unfold fittingFeatureDegree; omega)

/-- Every natural power of the common envelope is genuinely Gaussian integrable. -/
theorem fittingFeatureEnvelope_gaussian_integrable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (S : Real) (q : Nat) :
    Integrable (fun z : Weight d => (S*fittingFeatureEnvelope O a z)^q)
      (stdGaussian (Weight d)) := by
  have hi := (gaussian_one_add_norm_pow_integrable d (fittingFeatureDegree O*q)).const_mul
    ((S*fittingFeatureMass O a)^q)
  convert hi using 1
  funext z
  simp only [fittingFeatureEnvelope, ← mul_assoc, mul_pow, ← pow_mul]

end PaperFormalization.MatrixFactorization
