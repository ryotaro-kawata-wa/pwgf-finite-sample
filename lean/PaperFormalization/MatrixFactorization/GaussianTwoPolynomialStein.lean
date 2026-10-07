import PaperFormalization.MatrixFactorization.GaussianMultivariateStein
import PaperFormalization.MatrixFactorization.GaussianLinearPolynomial

/-! # Gaussian integration by parts for polynomial linear observations

This module connects the proved coordinate polynomial identity to the actual
Euclidean inner products used by the finite Hermite activation. Both polynomial
integrability and integration by parts are outputs, not model assumptions.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Evaluation of the algebraic lift at actual Euclidean coordinates. -/
theorem gaussianPolynomialLift_eval_weight {d : Nat} (P : Polynomial Real)
    (u z : Weight d) :
    MvPolynomial.eval (fun i => z i) (gaussianPolynomialLift P u) = P.eval (inner Real u z) := by
  exact gaussianPolynomialLift_eval P u (fun i => z i)

/-- Two arbitrary scalar polynomial linear observations are integrable. -/
theorem gaussian_two_polynomial_integrable {d : Nat} (u v : Weight d)
    (P Q : Polynomial Real) :
    Integrable (fun z : Weight d => P.eval (inner Real u z) * Q.eval (inner Real v z))
      (stdGaussian (Weight d)) := by
  have hi := gaussian_mvPolynomial_integrable (gaussianPolynomialLift P u * gaussianPolynomialLift Q v)
  simpa only [map_mul, gaussianPolynomialLift_eval_weight] using hi

/-- The coordinate-weighted product required for Gaussian integration by parts
is integrable under the same source law. -/
theorem gaussian_two_polynomial_weighted_integrable {d : Nat} (s u v : Weight d)
    (P Q : Polynomial Real) :
    Integrable (fun z : Weight d => inner Real s z * P.eval (inner Real u z) *
      Q.eval (inner Real v z)) (stdGaussian (Weight d)) := by
  have hi := gaussian_mvPolynomial_integrable
    ((gaussianPolynomialLift Polynomial.X s * gaussianPolynomialLift P u) * gaussianPolynomialLift Q v)
  simpa only [map_mul, gaussianPolynomialLift_eval_weight, Polynomial.eval_X] using hi

/-- The actual Gaussian directional identity, valid for arbitrary input
vectors and arbitrary real polynomials. -/
theorem gaussian_two_polynomial_stein {d : Nat} (s u v : Weight d)
    (P Q : Polynomial Real) :
    (∫ z : Weight d, inner Real s z * P.eval (inner Real u z) * Q.eval (inner Real v z)
      ∂stdGaussian (Weight d)) =
      inner Real s u * (∫ z : Weight d, P.derivative.eval (inner Real u z) *
        Q.eval (inner Real v z) ∂stdGaussian (Weight d)) +
      inner Real s v * (∫ z : Weight d, P.eval (inner Real u z) *
        Q.derivative.eval (inner Real v z) ∂stdGaussian (Weight d)) := by
  have hi1 := gaussian_two_polynomial_integrable u v P.derivative Q
  have hi2 := gaussian_two_polynomial_integrable u v P Q.derivative
  have hd := gaussian_mvPolynomial_directional_stein s
    (gaussianPolynomialLift P u * gaussianPolynomialLift Q v)
  simp only [map_mul, gaussianPolynomialLift_eval_weight,
    gaussianPolynomialLift_product_pderiv, map_add, MvPolynomial.eval_C] at hd
  have hsplit (i : Fin d) :
      (∫ z : Weight d, u i * (P.derivative.eval (inner Real u z) * Q.eval (inner Real v z)) +
          v i * (P.eval (inner Real u z) * Q.derivative.eval (inner Real v z))
        ∂stdGaussian (Weight d)) =
      u i * (∫ z : Weight d, P.derivative.eval (inner Real u z) * Q.eval (inner Real v z)
        ∂stdGaussian (Weight d)) +
      v i * (∫ z : Weight d, P.eval (inner Real u z) * Q.derivative.eval (inner Real v z)
        ∂stdGaussian (Weight d)) := by
    rw [integral_add (hi1.const_mul (u i)) (hi2.const_mul (v i)), integral_const_mul, integral_const_mul]
  simp_rw [hsplit] at hd
  have hinner (x : Weight d) : inner Real s x = ∑ i, s i*x i := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  simpa only [hinner, Finset.sum_mul, Finset.sum_add_distrib, mul_add, mul_assoc] using hd

end PaperFormalization.MatrixFactorization
