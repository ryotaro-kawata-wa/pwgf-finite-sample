import PaperFormalization.MatrixFactorization.GaussianHermiteCovariance
import PaperFormalization.MatrixFactorization.GaussianVisibility
import PaperFormalization.MatrixFactorization.WeightedTransverseMoment

/-! # The source Gaussian transverse pairing in the degree-one case

The teacher remains its original probability measure. Its first spherical
moment is integrated directly, and standard Gaussian covariance evaluates the
actual activation pairing. This file does not claim arbitrary-degree Hermite
orthogonality.
-/

open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def sphereBarycenter {d : Nat} (teacher : Measure (UnitSphere d)) : Weight d :=
  ∫ w, w.val ∂teacher

theorem sphereBarycenter_integrable {d : Nat} (teacher : Measure (UnitSphere d))
    [IsFiniteMeasure teacher] : Integrable (fun w : UnitSphere d => w.val) teacher :=
  sphere_integrable teacher _ (by fun_prop)

/-- The original mean feature is linear only because the active set here is
exactly the first Hermite degree. No finite-moment injectivity is used. -/
theorem meanFeature_singleton_one {d h : Nat} (a : Nat → Weight h)
    (teacher : Measure (UnitSphere d)) [IsFiniteMeasure teacher] (z : Weight d) :
    meanFeature (finiteHermiteActivation {1} a) teacher z =
      inner Real (sphereBarycenter teacher) z • a 1 := by
  simp only [meanFeature, finiteHermiteActivation_singleton_one]
  rw [integral_smul_const]
  congr 1
  calc
    _ = ∫ w : UnitSphere d, inner Real z w.val ∂teacher :=
      integral_congr_ae (Filter.Eventually.of_forall (fun w => real_inner_comm _ _))
    _ = inner Real z (sphereBarycenter teacher) :=
      integral_inner (sphereBarycenter_integrable teacher) z
    _ = _ := real_inner_comm _ _

/-- Integrating the actual teacher pairing gives its spherical first moment.
The one-half factor is inherited from the source transverse field. -/
theorem gaussian_teacher_pairing_singleton_one {d h : Nat} (a : Nat → Weight h)
    (pole : UnitSphere d) (s : Weight d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] :
    (∫ z : Weight d, inner Real
      (meanFeature (finiteHermiteActivation {1} a) teacher z)
      (transverseFeature {1} a pole s z) ∂stdGaussian (Weight d)) =
      (1/2 : Real)*‖a 1‖^2*inner Real (sphereBarycenter teacher) s := by
  simp only [meanFeature_singleton_one, transverseFeature,
    finiteHermiteActivationJet_singleton_one, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  calc
    _ = ((1/2 : Real)*‖a 1‖^2) *
        (∫ z : Weight d, inner Real (sphereBarycenter teacher) z * inner Real s z
          ∂stdGaussian (Weight d)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by ring)
    _ = _ := by rw [gaussian_inner_mul]

/-- The Gaussian visibility vector has its actual mean identified in the
first-degree model, before any positivity assumption is used. -/
theorem gaussianTransverseMean_singleton_one {d h : Nat} (a : Nat → Weight h)
    (pole : UnitSphere d) (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    gaussianTransverseMean {1} a pole teacher =
      ((1/2 : Real)*‖a 1‖^2) • transverseProjection pole (sphereBarycenter teacher) := by
  apply ext_inner_left Real
  intro s
  rw [gaussianTransverseMean,
    ← integral_inner (gaussianTransverseVector_integrable {1} a pole teacher)]
  simp only [gaussianTransverseVector, meanFeature_singleton_one,
    finiteHermiteActivationJet_singleton_one, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, transverseProjection, inner_sub_right]
  let m := sphereBarycenter teacher
  let C := (1/2 : Real)*‖a 1‖^2
  calc
    _ = C * ((∫ z : Weight d, inner Real m z * inner Real s z ∂stdGaussian (Weight d)) -
        (∫ z : Weight d, inner Real m z * inner Real pole.val z ∂stdGaussian (Weight d)) *
          inner Real s pole.val) := by
      rw [← integral_mul_const, ← integral_sub (gaussian_inner_mul_integrable m s)
        ((gaussian_inner_mul_integrable m pole.val).mul_const _), ← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by dsimp [m, C]; ring)
    _ = _ := by
      rw [gaussian_inner_mul, gaussian_inner_mul]
      dsimp [m, C]
      rw [real_inner_comm (sphereBarycenter teacher) s,
        real_inner_comm (sphereBarycenter teacher) pole.val]

/-- In degree one the manuscript's latitude weight is exactly constant. -/
@[simp] theorem activeLatitudeWeight_singleton_one {h : Nat} (a : Nat → Weight h) (r : Real) :
    activeLatitudeWeight {1} a r = (1/2 : Real)*‖a 1‖^2 := by
  simp [activeLatitudeWeight]

/-- The source weighted moment is the transverse part of its actual first moment. -/
theorem weightedTransverseMoment_singleton_one {d h : Nat} (a : Nat → Weight h)
    (pole : UnitSphere d) (teacher : Measure (UnitSphere d)) [IsFiniteMeasure teacher] :
    weightedTransverseMoment {1} a pole teacher =
      ((1/2 : Real)*‖a 1‖^2) • transverseProjection pole (sphereBarycenter teacher) := by
  simp only [weightedTransverseMoment, activeLatitudeWeight_singleton_one]
  rw [integral_smul]
  congr 1
  simp only [teacherTransverseProjection, transverseProjection, sphereBarycenter]
  rw [integral_sub (sphereBarycenter_integrable teacher)
    ((sphereBarycenter_integrable teacher).const_inner pole.val |>.smul_const pole.val),
    integral_smul_const, integral_inner (sphereBarycenter_integrable teacher)]

/-- The Gaussian-to-teacher bridge is completely proved for the first degree.
It has no visibility, covariance, or moment-identity hypothesis. -/
theorem gaussianTransverseMean_eq_weightedMoment_singleton_one {d h : Nat}
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] :
    gaussianTransverseMean {1} a pole teacher = weightedTransverseMoment {1} a pole teacher := by
  rw [gaussianTransverseMean_singleton_one, weightedTransverseMoment_singleton_one]

end PaperFormalization.MatrixFactorization
