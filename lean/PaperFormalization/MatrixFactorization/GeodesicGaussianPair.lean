import PaperFormalization.MatrixFactorization.GaussianOrthogonalPair
import PaperFormalization.MatrixFactorization.SphericalFeatureDifferential

/-! # Actual Gaussian observations along spherical EXP

The normalized nonzero velocity is a unit tangent at the actual current EXP
point. Its pair of observations has the independent standard Gaussian law.
The feature factorizations retain the radial acceleration term, and the
stationary case is proved separately without dividing by its zero speed.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- At nonzero speed, the actual position and normalized velocity give an
independent standard real Gaussian pair at every signed time. -/
theorem geodesic_gaussian_normalized_pair_law {d : Nat} (w : UnitSphere d)
    (v : Weight d) (hv : inner Real w.val v = 0) (hn : v ≠ 0) (t : Real) :
    (stdGaussian (Weight d)).map (fun z =>
      (inner Real (geodesicPoint w v hv t).val z,
        inner Real (sphereExpVelocity w v t) z / norm v)) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  have hn' : norm v ≠ 0 := norm_ne_zero_iff.mpr hn
  let u : UnitSphere d := ⟨(norm v)⁻¹ • sphereExpVelocity w v t, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_nonneg (norm_nonneg v), sphereExpVelocity_norm w v hv t,
      inv_mul_cancel₀ hn']⟩
  have hu : inner Real (geodesicPoint w v hv t).val u.val = 0 := by
    change inner Real (geodesicPoint w v hv t).val
      ((norm v)⁻¹ • sphereExpVelocity w v t) = 0
    rw [inner_smul_right, geodesicVelocity_tangent w v hv t, mul_zero]
  have h := stdGaussian_map_orthogonal_unit_pair (geodesicPoint w v hv t) u hu
  simpa only [u, real_inner_smul_left, div_eq_mul_inv, mul_comm] using h

/-- The first actual feature jet is the speed times the source first Gaussian
jet evaluated at the normalized pair. -/
theorem sphericalFeatureFirst_gaussian_pair_factorization {d h : Nat} (k : Nat)
    (O : Finset Nat) (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (hn : v ≠ 0) (z : Weight d) (t : Real) :
    sphericalFeatureFirst k O a w v hv z t = norm v •
      ((inner Real (sphereExpVelocity w v t) z / norm v) •
        finiteHermiteActivationJet (k+1) O a (inner Real (geodesicPoint w v hv t).val z)) := by
  have hn' : norm v ≠ 0 := norm_ne_zero_iff.mpr hn
  simp only [sphericalFeatureFirst, sphericalFeatureJet, smul_smul]
  congr 1
  field_simp

/-- The second actual feature jet has the exact squared-speed factor. The
subtracted radial term remains inside the combined source second jet. -/
theorem sphericalFeatureSecond_gaussian_pair_factorization {d h : Nat} (k : Nat)
    (O : Finset Nat) (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (hn : v ≠ 0) (z : Weight d) (t : Real) :
    sphericalFeatureSecond k O a w v hv z t = (norm v)^2 •
      ((inner Real (sphereExpVelocity w v t) z / norm v)^2 •
        finiteHermiteActivationJet (k+2) O a (inner Real (geodesicPoint w v hv t).val z) -
       inner Real (geodesicPoint w v hv t).val z •
        finiteHermiteActivationJet (k+1) O a (inner Real (geodesicPoint w v hv t).val z)) := by
  have hn' : norm v ≠ 0 := norm_ne_zero_iff.mpr hn
  simp only [sphericalFeatureSecond, sphericalFeatureJet, smul_sub, smul_smul]
  congr 2
  field_simp

/-- Both actual feature derivatives vanish along a stationary EXP path,
including every Gaussian input and every signed time. -/
theorem sphericalFeature_derivatives_zero_velocity {d h : Nat} (k : Nat)
    (O : Finset Nat) (a : Nat → Weight h) (w : UnitSphere d)
    (hv : inner Real w.val (0 : Weight d) = 0) (z : Weight d) (t : Real) :
    sphericalFeatureFirst k O a w 0 hv z t = 0 ∧
      sphericalFeatureSecond k O a w 0 hv z t = 0 := by
  simp [sphericalFeatureFirst, sphericalFeatureSecond, sphereExpVelocity]

end PaperFormalization.MatrixFactorization
