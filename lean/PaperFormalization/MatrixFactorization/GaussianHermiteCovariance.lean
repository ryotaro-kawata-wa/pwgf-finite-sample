import PaperFormalization.MatrixFactorization.TransverseFeatureSignal

/-! # Actual Gaussian covariance for the first Hermite degree

These lemmas use the covariance of the existing standard Gaussian measure.
The degree-one endpoint is stated explicitly; no orthogonality identity for
arbitrary Hermite degrees is introduced as an assumption.
-/

open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Gaussian linear observations have every finite moment needed below. -/
theorem gaussian_inner_memLp {d : Nat} (v : Weight d) (p : ENNReal) (hp : p ≠ ⊤) :
    MemLp (fun z : Weight d => inner Real v z) p (stdGaussian (Weight d)) :=
  (IsGaussian.memLp_id (stdGaussian (Weight d)) p hp).const_inner v

/-- The product covariance is integrable before its value is evaluated. -/
theorem gaussian_inner_mul_integrable {d : Nat} (u v : Weight d) :
    Integrable (fun z : Weight d => inner Real u z * inner Real v z)
      (stdGaussian (Weight d)) :=
  (gaussian_inner_memLp u 2 (by simp)).integrable_mul
    (gaussian_inner_memLp v 2 (by simp))

/-- This is the actual expectation of two Gaussian linear observations. -/
theorem gaussian_inner_mul {d : Nat} (u v : Weight d) :
    (∫ z : Weight d, inner Real u z * inner Real v z ∂stdGaussian (Weight d)) =
      inner Real u v := by
  have hc := covarianceBilin_apply
    (IsGaussian.memLp_two_id (μ := stdGaussian (Weight d))) u v
  simp only [id_eq, integral_id_stdGaussian, sub_zero, covarianceBilin_stdGaussian] at hc
  exact hc.symm

@[simp] theorem normalizedHermiteJet_one_one (x : Real) :
    normalizedHermiteJet 1 1 x = 1 := by
  norm_num [normalizedHermiteJet, hermiteRealPolynomial, Polynomial.hermite_one]

@[simp] theorem finiteHermiteActivation_singleton_one {h : Nat}
    (a : Nat → Weight h) (x : Real) :
    finiteHermiteActivation {1} a x = x • a 1 := by
  simp [finiteHermiteActivation]

@[simp] theorem finiteHermiteActivationJet_singleton_one {h : Nat}
    (a : Nat → Weight h) (x : Real) :
    finiteHermiteActivationJet 1 {1} a x = a 1 := by
  simp [finiteHermiteActivationJet]

/-- For the first active degree the original finite activation has its exact
Gaussian transverse pairing, with the prescribed one-half normalization. -/
theorem gaussian_transverse_pairing_singleton_one {d h : Nat}
    (a : Nat → Weight h) (pole w : UnitSphere d) (s : Weight d) :
    (∫ z : Weight d, inner Real
      (finiteHermiteActivation {1} a (inner Real w.val z))
      (transverseFeature {1} a pole s z) ∂stdGaussian (Weight d)) =
      (1/2 : Real) * ‖a 1‖^2 * inner Real w.val s := by
  simp only [finiteHermiteActivation_singleton_one, transverseFeature,
    finiteHermiteActivationJet_singleton_one, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  calc
    _ = ((1/2 : Real)*‖a 1‖^2) *
        (∫ z : Weight d, inner Real w.val z * inner Real s z ∂stdGaussian (Weight d)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by ring)
    _ = _ := by rw [gaussian_inner_mul]

end PaperFormalization.MatrixFactorization
