import PaperFormalization.MatrixFactorization.SphericalFeatureIntegral

/-! # MF04: Gaussian moments of the actual varied mean features

The bounds below are uniform in signed time. Integrating the pointwise envelopes
uses the original probability measure and its true speed moments. All natural
Gaussian moments of the mean feature and its first two derivatives then follow.
-/
open MeasureTheory ProbabilityTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

theorem meanFeatureAlongExp_stronglyMeasurable {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu]
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (t : Real) :
    StronglyMeasurable (fun z => meanFeatureJetAlongExp k O a mu v hv z t) ∧
    StronglyMeasurable (fun z => meanFeatureJetAlongExpFirst k O a mu v hv z t) ∧
    StronglyMeasurable (fun z => meanFeatureJetAlongExpSecond k O a mu v hv z t) := by
  have hm : Continuous (fun p : Weight d × UnitSphere d => ((t,p.1),p.2)) := by fun_prop
  have h0 := ((sphericalFeatureJet_continuous k O a v hv hc).comp
    (f := fun p : Weight d × UnitSphere d => ((t,p.1),p.2)) hm).stronglyMeasurable.integral_prod_right
      (ν := mu) (f := fun z w => sphericalFeatureJet k O a w (v w) (hv w) z t)
  have h1 := ((sphericalFeatureFirst_continuous k O a v hv hc).comp
    (f := fun p : Weight d × UnitSphere d => ((t,p.1),p.2)) hm).stronglyMeasurable.integral_prod_right
      (ν := mu) (f := fun z w => sphericalFeatureFirst k O a w (v w) (hv w) z t)
  have h2 := ((sphericalFeatureSecond_continuous k O a v hv hc).comp
    (f := fun p : Weight d × UnitSphere d => ((t,p.1),p.2)) hm).stronglyMeasurable.integral_prod_right
      (ν := mu) (f := fun z w => sphericalFeatureSecond k O a w (v w) (hv w) z t)
  have he : (fun z => meanFeatureJetAlongExp k O a mu v hv z t) =
      (fun z => ∫ w, sphericalFeatureJet k O a w (v w) (hv w) z t ∂mu) :=
    funext (fun z => meanFeatureJetAlongExp_integral k O a mu v hv hc z t)
  exact ⟨he ▸ h0, h1, h2⟩

/-- The zeroth bound uses probability normalization; the derivative bounds
retain the original first and second speed moments. -/
theorem meanFeatureAlongExp_bounds {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (z : Weight d) (t : Real) :
    norm (meanFeatureJetAlongExp k O a mu v hv z t) ≤ featureEnvelope k O a z ∧
    norm (meanFeatureJetAlongExpFirst k O a mu v hv z t) ≤
      (∫ w, norm (v w) ∂mu)*featureFirstEnvelope k O a z ∧
    norm (meanFeatureJetAlongExpSecond k O a mu v hv z t) ≤
      (∫ w, (norm (v w))^2 ∂mu)*featureSecondEnvelope k O a z := by
  have hi := sphericalFeature_integrable k O a mu v hv hc z t
  have hnorm : Integrable (fun w => norm (v w)) mu := sphere_integrable mu _ hc.norm
  have hnorm2 : Integrable (fun w => (norm (v w))^2) mu := sphere_integrable mu _ (hc.norm.pow 2)
  refine ⟨?_, ?_, ?_⟩
  · rw [meanFeatureJetAlongExp_integral k O a mu v hv hc z t]
    calc
      _ ≤ ∫ w, norm (sphericalFeatureJet k O a w (v w) (hv w) z t) ∂mu := norm_integral_le_integral_norm _
      _ ≤ ∫ _ : UnitSphere d, featureEnvelope k O a z ∂mu :=
        integral_mono hi.1.norm (integrable_const _)
          (fun w => sphericalFeatureJet_bound k O a w (v w) (hv w) z t)
      _ = _ := by simp
  · unfold meanFeatureJetAlongExpFirst
    calc
      _ ≤ ∫ w, norm (sphericalFeatureFirst k O a w (v w) (hv w) z t) ∂mu := norm_integral_le_integral_norm _
      _ ≤ ∫ w, norm (v w)*featureFirstEnvelope k O a z ∂mu :=
        integral_mono hi.2.1.norm (hnorm.mul_const _)
          (fun w => sphericalFeatureFirst_bound k O a w (v w) (hv w) z t)
      _ = _ := integral_mul_const _ _
  · unfold meanFeatureJetAlongExpSecond
    calc
      _ ≤ ∫ w, norm (sphericalFeatureSecond k O a w (v w) (hv w) z t) ∂mu := norm_integral_le_integral_norm _
      _ ≤ ∫ w, (norm (v w))^2*featureSecondEnvelope k O a z ∂mu :=
        integral_mono hi.2.2.norm (hnorm2.mul_const _)
          (fun w => sphericalFeatureSecond_bound k O a w (v w) (hv w) z t)
      _ = _ := integral_mul_const _ _

/-- Polynomial Gaussian moments are derived for all three actual mean-feature jets. -/
theorem meanFeatureAlongExp_gaussian_pow_integrable {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (t : Real) (q : Nat) :
    Integrable (fun z => norm (meanFeatureJetAlongExp k O a mu v hv z t)^q) (stdGaussian (Weight d)) ∧
    Integrable (fun z => norm (meanFeatureJetAlongExpFirst k O a mu v hv z t)^q) (stdGaussian (Weight d)) ∧
    Integrable (fun z => norm (meanFeatureJetAlongExpSecond k O a mu v hv z t)^q) (stdGaussian (Weight d)) := by
  have hm := meanFeatureAlongExp_stronglyMeasurable k O a mu v hv hc t
  have hb := meanFeatureAlongExp_bounds k O a mu v hv hc
  have hspeed : 0 ≤ ∫ w, norm (v w) ∂mu := integral_nonneg (fun w => norm_nonneg _)
  have hspeed2 : 0 ≤ ∫ w, (norm (v w))^2 ∂mu := integral_nonneg (fun w => sq_nonneg _)
  refine ⟨?_, ?_, ?_⟩
  · exact gaussian_of_polynomial_bound _ hm.1 (activationJetMass k O a)
      (activationJetMass_nonneg k O a) (hermiteJetOrder k O) q (fun z => (hb z t).1)
  · apply gaussian_of_polynomial_bound _ hm.2.1
      ((∫ w, norm (v w) ∂mu)*activationJetMass (k+1) O a)
      (mul_nonneg hspeed (activationJetMass_nonneg (k+1) O a)) (hermiteJetOrder (k+1) O+1) q
    intro z
    have h := (hb z t).2.1.trans
      (mul_le_mul_of_nonneg_left (featureFirstEnvelope_polynomial_bound k O a z) hspeed)
    simpa only [mul_assoc] using h
  · apply gaussian_of_polynomial_bound _ hm.2.2
      ((∫ w, (norm (v w))^2 ∂mu)*(activationJetMass (k+2) O a+activationJetMass (k+1) O a))
      (mul_nonneg hspeed2 (add_nonneg (activationJetMass_nonneg (k+2) O a) (activationJetMass_nonneg (k+1) O a)))
      (max (hermiteJetOrder (k+2) O+2) (hermiteJetOrder (k+1) O+1)) q
    intro z
    have h := (hb z t).2.2.trans
      (mul_le_mul_of_nonneg_left (featureSecondEnvelope_polynomial_bound k O a z) hspeed2)
    simpa only [mul_assoc] using h

end PaperFormalization.MatrixFactorization
