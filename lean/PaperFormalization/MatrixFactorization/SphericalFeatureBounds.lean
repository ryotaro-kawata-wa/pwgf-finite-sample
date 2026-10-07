import PaperFormalization.MatrixFactorization.SphericalFeatureDifferential
import PaperFormalization.MatrixFactorization.GaussianIntegrability

/-! # MF04: uniform feature envelopes for the original Gaussian input

The pointwise estimates hold for every signed time. Their constants depend on
activation data and the initial tangent speed; they do not impose a cutoff on
the Gaussian input. These bounds are later integrated over the original sphere
measure before differentiating the fitting expectation.
-/
open MeasureTheory ProbabilityTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def featureEnvelope {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (z : Weight d) : Real :=
  activationJetMass k O a * (1+norm z)^(hermiteJetOrder k O)

noncomputable def featureFirstEnvelope {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (z : Weight d) : Real :=
  norm z * featureEnvelope (k+1) O a z

noncomputable def featureSecondEnvelope {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (z : Weight d) : Real :=
  (norm z)^2 * featureEnvelope (k+2) O a z + norm z * featureEnvelope (k+1) O a z

theorem featureEnvelope_nonneg {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (z : Weight d) : 0 ≤ featureEnvelope k O a z := by
  exact mul_nonneg (activationJetMass_nonneg k O a) (pow_nonneg (by positivity) _)

theorem featureFirstEnvelope_nonneg {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (z : Weight d) : 0 ≤ featureFirstEnvelope k O a z :=
  mul_nonneg (norm_nonneg z) (featureEnvelope_nonneg (k+1) O a z)

theorem featureSecondEnvelope_nonneg {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (z : Weight d) : 0 ≤ featureSecondEnvelope k O a z :=
  add_nonneg (mul_nonneg (sq_nonneg _) (featureEnvelope_nonneg (k+2) O a z))
    (featureFirstEnvelope_nonneg k O a z)

theorem finiteHermiteActivationJet_sphere_bound {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (z : Weight d) :
    norm (finiteHermiteActivationJet k O a (inner Real w.val z)) ≤ featureEnvelope k O a z := by
  have hi : abs (inner Real w.val z) ≤ norm z := by
    simpa only [unitSphere_norm, one_mul] using abs_real_inner_le_norm w.val z
  exact (finiteHermiteActivationJet_growth k O a _).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) _)
      (activationJetMass_nonneg k O a))

theorem sphericalFeatureJet_bound {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (z : Weight d) (t : Real) :
    norm (sphericalFeatureJet k O a w v hv z t) ≤ featureEnvelope k O a z :=
  finiteHermiteActivationJet_sphere_bound k O a (geodesicPoint w v hv t) z

theorem sphericalFeatureFirst_bound {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (z : Weight d) (t : Real) :
    norm (sphericalFeatureFirst k O a w v hv z t) ≤ norm v * featureFirstEnvelope k O a z := by
  have hi : abs (inner Real (sphereExpVelocity w v t) z) ≤ norm v*norm z := by
    simpa only [sphereExpVelocity_norm w v hv t] using
      abs_real_inner_le_norm (sphereExpVelocity w v t) z
  rw [sphericalFeatureFirst, norm_smul, Real.norm_eq_abs]
  have hb := mul_le_mul hi (sphericalFeatureJet_bound (k+1) O a w v hv z t)
    (norm_nonneg _) (mul_nonneg (norm_nonneg v) (norm_nonneg z))
  simpa only [featureFirstEnvelope, mul_assoc] using hb

theorem sphericalFeatureSecond_bound {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (z : Weight d) (t : Real) :
    norm (sphericalFeatureSecond k O a w v hv z t) ≤
      (norm v)^2 * featureSecondEnvelope k O a z := by
  have hi : abs (inner Real (sphereExpVelocity w v t) z) ≤ norm v*norm z := by
    simpa only [sphereExpVelocity_norm w v hv t] using
      abs_real_inner_le_norm (sphereExpVelocity w v t) z
  have hp : abs (inner Real (geodesicPoint w v hv t).val z) ≤ norm z := by
    simpa only [unitSphere_norm, one_mul] using
      abs_real_inner_le_norm (geodesicPoint w v hv t).val z
  have h1 := mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hi 2)
    (sphericalFeatureJet_bound (k+2) O a w v hv z t) (norm_nonneg _) (sq_nonneg _)
  have h2 := mul_le_mul (mul_le_mul_of_nonneg_left hp (sq_nonneg (norm v)))
    (sphericalFeatureJet_bound (k+1) O a w v hv z t) (norm_nonneg _)
    (mul_nonneg (sq_nonneg _) (norm_nonneg _))
  unfold sphericalFeatureSecond
  calc
    _ ≤ norm ((inner Real (sphereExpVelocity w v t) z)^2 • sphericalFeatureJet (k+2) O a w v hv z t) +
        norm (((norm v)^2*inner Real (geodesicPoint w v hv t).val z) •
          sphericalFeatureJet (k+1) O a w v hv z t) := norm_sub_le _ _
    _ ≤ (norm v*norm z)^2*featureEnvelope (k+2) O a z +
        ((norm v)^2*norm z)*featureEnvelope (k+1) O a z := by
      simpa only [norm_smul, Real.norm_eq_abs, abs_pow, abs_mul,
        abs_of_nonneg (norm_nonneg v)] using add_le_add h1 h2
    _ = _ := by unfold featureSecondEnvelope; ring

/-- A scalar polynomial envelope supplies integrability of every natural power. -/
theorem gaussian_of_polynomial_bound {d : Nat} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] (f : Weight d → E)
    (hf : StronglyMeasurable f) (C : Real) (hC : 0 ≤ C) (M q : Nat)
    (hb : ∀ z, norm (f z) ≤ C*(1+norm z)^M) :
    Integrable (fun z => norm (f z)^q) (stdGaussian (Weight d)) := by
  have hd := (gaussian_one_add_norm_pow_integrable d (M*q)).const_mul (C^q)
  apply hd.mono' (hf.norm.pow q).aestronglyMeasurable
  filter_upwards with z
  change norm (norm (f z)^q) ≤ C^q*(1+norm z)^(M*q)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  calc
    _ ≤ (C*(1+norm z)^M)^q := pow_le_pow_left₀ (norm_nonneg _) (hb z) q
    _ = _ := by rw [mul_pow, ← pow_mul]


/-- The three envelopes are measurable scalar polynomials in the input norm. -/
theorem featureEnvelopes_continuous {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) :
    Continuous (featureEnvelope (d := d) k O a) ∧
    Continuous (featureFirstEnvelope (d := d) k O a) ∧
    Continuous (featureSecondEnvelope (d := d) k O a) := by
  unfold featureFirstEnvelope featureSecondEnvelope featureEnvelope
  constructor
  · fun_prop
  constructor <;> fun_prop

theorem featureEnvelope_mul_norm_pow_bound {d h : Nat} (k j : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (z : Weight d) :
    (norm z)^j * featureEnvelope k O a z ≤
      activationJetMass k O a * (1+norm z)^(hermiteJetOrder k O+j) := by
  unfold featureEnvelope
  calc
    _ ≤ (1+norm z)^j * (activationJetMass k O a*(1+norm z)^(hermiteJetOrder k O)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (by linarith) j)
        (mul_nonneg (activationJetMass_nonneg k O a) (pow_nonneg (by positivity) _))
    _ = _ := by rw [pow_add]; ring

theorem featureFirstEnvelope_polynomial_bound {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (z : Weight d) :
    featureFirstEnvelope k O a z ≤
      activationJetMass (k+1) O a*(1+norm z)^(hermiteJetOrder (k+1) O+1) := by
  simpa only [featureFirstEnvelope, pow_one] using featureEnvelope_mul_norm_pow_bound (k+1) 1 O a z

theorem featureSecondEnvelope_polynomial_bound {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (z : Weight d) :
    featureSecondEnvelope k O a z ≤
      (activationJetMass (k+2) O a+activationJetMass (k+1) O a) *
        (1+norm z)^(max (hermiteJetOrder (k+2) O+2) (hermiteJetOrder (k+1) O+1)) := by
  have h1 := featureEnvelope_mul_norm_pow_bound (k+2) 2 O a z
  have h2 := featureFirstEnvelope_polynomial_bound k O a z
  have hb : 1 ≤ 1+norm z := by linarith [norm_nonneg z]
  have h1' := h1.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hb
      (le_max_left (hermiteJetOrder (k+2) O+2) (hermiteJetOrder (k+1) O+1)))
    (activationJetMass_nonneg (k+2) O a))
  have h2' := h2.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hb
      (le_max_right (hermiteJetOrder (k+2) O+2) (hermiteJetOrder (k+1) O+1)))
    (activationJetMass_nonneg (k+1) O a))
  simpa only [featureSecondEnvelope, featureFirstEnvelope, add_mul] using add_le_add h1' h2'

theorem featureEnvelopes_gaussian_pow_integrable {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (q : Nat) :
    Integrable (fun z : Weight d => (featureEnvelope k O a z)^q) (stdGaussian (Weight d)) ∧
    Integrable (fun z : Weight d => (featureFirstEnvelope k O a z)^q) (stdGaussian (Weight d)) ∧
    Integrable (fun z : Weight d => (featureSecondEnvelope k O a z)^q) (stdGaussian (Weight d)) := by
  have hc := featureEnvelopes_continuous (d := d) k O a
  have h0 := gaussian_of_polynomial_bound (featureEnvelope (d := d) k O a) hc.1.stronglyMeasurable
    (activationJetMass k O a) (activationJetMass_nonneg k O a) (hermiteJetOrder k O) q
    (fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (featureEnvelope_nonneg k O a z)]; rfl)
  have h1 := gaussian_of_polynomial_bound (featureFirstEnvelope (d := d) k O a) hc.2.1.stronglyMeasurable
    (activationJetMass (k+1) O a) (activationJetMass_nonneg (k+1) O a) (hermiteJetOrder (k+1) O+1) q
    (fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (featureFirstEnvelope_nonneg k O a z)];
                 exact featureFirstEnvelope_polynomial_bound k O a z)
  have h2 := gaussian_of_polynomial_bound (featureSecondEnvelope (d := d) k O a) hc.2.2.stronglyMeasurable
    (activationJetMass (k+2) O a+activationJetMass (k+1) O a)
    (add_nonneg (activationJetMass_nonneg (k+2) O a) (activationJetMass_nonneg (k+1) O a))
    (max (hermiteJetOrder (k+2) O+2) (hermiteJetOrder (k+1) O+1)) q
    (fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (featureSecondEnvelope_nonneg k O a z)];
                 exact featureSecondEnvelope_polynomial_bound k O a z)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (featureEnvelope_nonneg k O a _),
    abs_of_nonneg (featureFirstEnvelope_nonneg k O a _),
    abs_of_nonneg (featureSecondEnvelope_nonneg k O a _)] using And.intro h0 (And.intro h1 h2)

end PaperFormalization.MatrixFactorization
