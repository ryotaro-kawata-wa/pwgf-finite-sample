import PaperFormalization.MatrixFactorization.HermiteDerivatives
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! # Polynomial encoding of Gaussian linear observations

The multivariate polynomial represents the actual Euclidean inner product.
Its partial derivatives and the univariate composition chain rule are purely
algebraic consequences of the existing polynomial derivation API.
-/
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def gaussianLinearPolynomial {d : Nat} (u : Weight d) : MvPolynomial (Fin d) Real :=
  ∑ i, MvPolynomial.C (u i)*MvPolynomial.X i

theorem gaussianLinearPolynomial_eval {d : Nat} (u : Weight d) (x : Fin d → Real) :
    MvPolynomial.eval x (gaussianLinearPolynomial u) = inner Real u (WithLp.toLp 2 x) := by
  simp only [gaussianLinearPolynomial, map_sum, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro i hi
  change u i*x i = x i*u i
  ring

theorem gaussianLinearPolynomial_pderiv {d : Nat} (u : Weight d) (i : Fin d) :
    MvPolynomial.pderiv i (gaussianLinearPolynomial u) = MvPolynomial.C (u i) := by
  classical
  simp [gaussianLinearPolynomial, MvPolynomial.pderiv_C_mul, Pi.single_apply]

noncomputable def gaussianPolynomialLift {d : Nat} (P : Polynomial Real) (u : Weight d) :
    MvPolynomial (Fin d) Real := Polynomial.aeval (gaussianLinearPolynomial u) P

theorem gaussianPolynomialLift_eval {d : Nat} (P : Polynomial Real) (u : Weight d)
    (x : Fin d → Real) :
    MvPolynomial.eval x (gaussianPolynomialLift P u) = P.eval (inner Real u (WithLp.toLp 2 x)) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simpa only [gaussianPolynomialLift, map_add, Polynomial.eval_add] using congrArg₂ (· + ·) hP hQ
  | monomial n c =>
      simp [gaussianPolynomialLift, Polynomial.aeval_monomial, gaussianLinearPolynomial_eval]

theorem gaussianPolynomialLift_pderiv {d : Nat} (P : Polynomial Real) (u : Weight d) (i : Fin d) :
    MvPolynomial.pderiv i (gaussianPolynomialLift P u) =
      MvPolynomial.C (u i)*gaussianPolynomialLift P.derivative u := by
  simp only [gaussianPolynomialLift, Derivation.map_aeval,
    gaussianLinearPolynomial_pderiv, smul_eq_mul]
  ring

theorem gaussianPolynomialLift_product_pderiv {d : Nat} (P Q : Polynomial Real)
    (u v : Weight d) (i : Fin d) :
    MvPolynomial.pderiv i (gaussianPolynomialLift P u * gaussianPolynomialLift Q v) =
      MvPolynomial.C (u i)*(gaussianPolynomialLift P.derivative u*gaussianPolynomialLift Q v) +
      MvPolynomial.C (v i)*(gaussianPolynomialLift P u*gaussianPolynomialLift Q.derivative v) := by
  rw [MvPolynomial.pderiv_mul, gaussianPolynomialLift_pderiv, gaussianPolynomialLift_pderiv]
  ring

end PaperFormalization.MatrixFactorization
