import PaperFormalization.MatrixFactorization.GeneralRetractionDifferential
import PaperFormalization.MatrixFactorization.SphericalFeatureBounds

/-! # MF10: actual feature derivatives along normalized retraction

The activation is the original finite normalized-Hermite activation at order
zero. Both derivatives below follow the actual normalized point and its velocity.
The second derivative retains the full acceleration of this actual path. At
zero that acceleration is the same radial sphere acceleration as for EXP.
-/
open MeasureTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def retractedFeatureJet {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (z : Weight d) (t : Real) : Weight h :=
  finiteHermiteActivationJet k O a (inner Real (sphericalRetract w v hv t).val z)

noncomputable def retractedFeatureFirst {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (z : Weight d) (t : Real) : Weight h :=
  inner Real (sphericalRetractVelocity w v t) z • retractedFeatureJet (k+1) O a w v hv z t

noncomputable def retractedFeatureSecond {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (z : Weight d) (t : Real) : Weight h :=
  (inner Real (sphericalRetractVelocity w v t) z)^2 • retractedFeatureJet (k+2) O a w v hv z t +
    inner Real (sphericalRetractAcceleration w v t) z • retractedFeatureJet (k+1) O a w v hv z t

@[simp] theorem retractedFeatureJet_zero_order {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (z : Weight d) (t : Real) :
    retractedFeatureJet 0 O a w v hv z t =
      finiteHermiteActivation O a (inner Real (sphericalRetract w v hv t).val z) := by
  simp only [retractedFeatureJet, finiteHermiteActivationJet_zero]

theorem retractedFeatureJet_hasDerivAt {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (z : Weight d) (t : Real) :
    HasDerivAt (retractedFeatureJet k O a w v hv z)
      (retractedFeatureFirst k O a w v hv z t) t := by
  have hd : HasDerivAt (fun s => inner Real (sphericalRetract w v hv s).val z)
      (inner Real (sphericalRetractVelocity w v t) z) t := by
    simpa only [sphericalRetract, inner_zero_right, zero_add] using
      (sphericalRetractVector_hasDerivAt w v hv t).inner Real (hasDerivAt_const t z)
  exact (finiteHermiteActivationJet_hasDerivAt k O a _).scomp t hd

theorem retractedFeatureFirst_hasDerivAt {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (z : Weight d) (t : Real) :
    HasDerivAt (retractedFeatureFirst k O a w v hv z)
      (retractedFeatureSecond k O a w v hv z t) t := by
  have hd : HasDerivAt (fun s => inner Real (sphericalRetractVelocity w v s) z)
      (inner Real (sphericalRetractAcceleration w v t) z) t := by
    simpa only [inner_zero_right, zero_add] using
      (sphericalRetractVelocity_hasDerivAt w v hv t).inner Real (hasDerivAt_const t z)
  have hi := hd.smul (retractedFeatureJet_hasDerivAt (k+1) O a w v hv z t)
  apply hi.congr_deriv
  simp only [retractedFeatureFirst, retractedFeatureSecond, Nat.add_assoc]
  module

theorem retractedFeatureJet_second_derivative {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (z : Weight d) (t : Real) :
    HasDerivAt (deriv (retractedFeatureJet k O a w v hv z))
      (retractedFeatureSecond k O a w v hv z t) t := by
  have he : deriv (retractedFeatureJet k O a w v hv z) = retractedFeatureFirst k O a w v hv z := by
    funext s
    exact (retractedFeatureJet_hasDerivAt k O a w v hv z s).deriv
  rw [he]
  exact retractedFeatureFirst_hasDerivAt k O a w v hv z t

@[simp] theorem retractedFeatureJet_at_zero {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (z : Weight d) :
    retractedFeatureJet k O a w v hv z 0 = finiteHermiteActivationJet k O a (inner Real w.val z) := by
  simp only [retractedFeatureJet, sphericalRetract_zero]

@[simp] theorem retractedFeatureFirst_at_zero {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (z : Weight d) :
    retractedFeatureFirst k O a w v hv z 0 =
      inner Real v z • finiteHermiteActivationJet (k+1) O a (inner Real w.val z) := by
  simp only [retractedFeatureFirst, sphericalRetractVelocity_zero, retractedFeatureJet_at_zero]

@[simp] theorem retractedFeatureSecond_at_zero {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (z : Weight d) :
    retractedFeatureSecond k O a w v hv z 0 =
      (inner Real v z)^2 • finiteHermiteActivationJet (k+2) O a (inner Real w.val z) -
        ((norm v)^2 * inner Real w.val z) • finiteHermiteActivationJet (k+1) O a (inner Real w.val z) := by
  simp only [retractedFeatureSecond, sphericalRetractVelocity_zero, retractedFeatureJet_at_zero,
    sphericalRetractAcceleration_zero, real_inner_smul_left]
  module


theorem retractedFeatureJet_bound {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (z : Weight d) (t : Real) :
    norm (retractedFeatureJet k O a w v hv z t) ≤ featureEnvelope k O a z :=
  finiteHermiteActivationJet_sphere_bound k O a (sphericalRetract w v hv t) z

theorem retractedFeatureFirst_bound {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (z : Weight d) (t : Real) :
    norm (retractedFeatureFirst k O a w v hv z t) ≤ 2*norm v*featureFirstEnvelope k O a z := by
  have hi : abs (inner Real (sphericalRetractVelocity w v t) z) ≤ (2*norm v)*norm z :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (sphericalRetractVelocity_norm_le w v hv t) (norm_nonneg z))
  rw [retractedFeatureFirst, norm_smul, Real.norm_eq_abs]
  have hb := mul_le_mul hi (retractedFeatureJet_bound (k+1) O a w v hv z t)
    (norm_nonneg _) (by positivity)
  simpa only [featureFirstEnvelope, mul_assoc] using hb

theorem retractedFeatureSecond_bound {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (z : Weight d) (t : Real) :
    norm (retractedFeatureSecond k O a w v hv z t) ≤
      6*norm v^2*featureSecondEnvelope k O a z := by
  have hi : abs (inner Real (sphericalRetractVelocity w v t) z) ≤ (2*norm v)*norm z :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (sphericalRetractVelocity_norm_le w v hv t) (norm_nonneg z))
  have ha : abs (inner Real (sphericalRetractAcceleration w v t) z) ≤ (6*norm v^2)*norm z :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (sphericalRetractAcceleration_norm_le w v hv t) (norm_nonneg z))
  have h1 := mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hi 2)
    (retractedFeatureJet_bound (k+2) O a w v hv z t) (norm_nonneg _) (sq_nonneg _)
  have h2 := mul_le_mul ha (retractedFeatureJet_bound (k+1) O a w v hv z t)
    (norm_nonneg _) (by positivity)
  unfold retractedFeatureSecond
  calc
    _ ≤ norm ((inner Real (sphericalRetractVelocity w v t) z)^2 • retractedFeatureJet (k+2) O a w v hv z t) +
        norm (inner Real (sphericalRetractAcceleration w v t) z • retractedFeatureJet (k+1) O a w v hv z t) :=
      norm_add_le _ _
    _ ≤ ((2*norm v)*norm z)^2*featureEnvelope (k+2) O a z +
        ((6*norm v^2)*norm z)*featureEnvelope (k+1) O a z := by
      simpa only [norm_smul, Real.norm_eq_abs, abs_pow] using add_le_add h1 h2
    _ ≤ _ := by
      have hn := mul_nonneg (mul_nonneg (sq_nonneg (norm v)) (sq_nonneg (norm z)))
        (featureEnvelope_nonneg (k+2) O a z)
      unfold featureSecondEnvelope
      nlinarith

theorem retractedFeatureJet_continuous {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (v : UnitSphere d → Weight d)
    (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) :
    Continuous (fun p : (Real × Weight d) × UnitSphere d =>
      retractedFeatureJet k O a p.2 (v p.2) (hv p.2) p.1.2 p.1.1) := by
  have hg : Continuous (fun p : (Real × Weight d) × UnitSphere d =>
      (sphericalRetractFamily v hv p.1.1 p.2).val) :=
    continuous_subtype_val.comp ((sphericalRetractFamily_continuous v hv hc).comp
      (f := fun p : (Real × Weight d) × UnitSphere d => (p.1.1,p.2)) (by fun_prop))
  exact (finiteHermiteActivationJet_continuous k O a).comp
    (hg.inner (𝕜 := Real) (continuous_snd.comp continuous_fst))

theorem retractedFeatureFirst_continuous {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (v : UnitSphere d → Weight d)
    (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) :
    Continuous (fun p : (Real × Weight d) × UnitSphere d =>
      retractedFeatureFirst k O a p.2 (v p.2) (hv p.2) p.1.2 p.1.1) := by
  have hg : Continuous (fun p : (Real × Weight d) × UnitSphere d =>
      sphericalRetractVelocity p.2 (v p.2) p.1.1) :=
    (sphericalRetractVelocity_continuous v hv hc).comp
      (f := fun p : (Real × Weight d) × UnitSphere d => (p.1.1,p.2)) (by fun_prop)
  exact (hg.inner (𝕜 := Real) (continuous_snd.comp continuous_fst)).smul
    (retractedFeatureJet_continuous (k+1) O a v hv hc)

theorem retractedFeatureSecond_continuous {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (v : UnitSphere d → Weight d)
    (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) :
    Continuous (fun p : (Real × Weight d) × UnitSphere d =>
      retractedFeatureSecond k O a p.2 (v p.2) (hv p.2) p.1.2 p.1.1) := by
  have hv' : Continuous (fun p : (Real × Weight d) × UnitSphere d =>
      sphericalRetractVelocity p.2 (v p.2) p.1.1) :=
    (sphericalRetractVelocity_continuous v hv hc).comp
      (f := fun p : (Real × Weight d) × UnitSphere d => (p.1.1,p.2)) (by fun_prop)
  have ha' : Continuous (fun p : (Real × Weight d) × UnitSphere d =>
      sphericalRetractAcceleration p.2 (v p.2) p.1.1) :=
    (sphericalRetractAcceleration_continuous v hv hc).comp
      (f := fun p : (Real × Weight d) × UnitSphere d => (p.1.1,p.2)) (by fun_prop)
  exact (((hv'.inner (𝕜 := Real) (continuous_snd.comp continuous_fst)).pow 2).smul
    (retractedFeatureJet_continuous (k+2) O a v hv hc)).add
    ((ha'.inner (𝕜 := Real) (continuous_snd.comp continuous_fst)).smul
      (retractedFeatureJet_continuous (k+1) O a v hv hc))

end PaperFormalization.MatrixFactorization
