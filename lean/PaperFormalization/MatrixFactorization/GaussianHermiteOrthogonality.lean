import PaperFormalization.MatrixFactorization.GaussianPolynomialStein

/-! # MF09: exact normalized Hermite orthogonality under N(0,1)

The raising recurrence is combined with proved Gaussian polynomial integration
by parts. Thus arbitrary-degree orthogonality is derived for the actual
Mathlib Hermite polynomials and the source sqrt(n!) normalization.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def gaussianPolynomialMean (P : Polynomial Real) : Real :=
  ∫ x : Real, P.eval x ∂gaussianReal 0 1

theorem gaussianPolynomialMean_add (P Q : Polynomial Real) :
    gaussianPolynomialMean (P+Q) = gaussianPolynomialMean P + gaussianPolynomialMean Q := by
  simp only [gaussianPolynomialMean, Polynomial.eval_add]
  exact integral_add (gaussianReal_polynomial_integrable P) (gaussianReal_polynomial_integrable Q)

theorem gaussianPolynomialMean_sub (P Q : Polynomial Real) :
    gaussianPolynomialMean (P-Q) = gaussianPolynomialMean P - gaussianPolynomialMean Q := by
  simp only [gaussianPolynomialMean, Polynomial.eval_sub]
  exact integral_sub (gaussianReal_polynomial_integrable P) (gaussianReal_polynomial_integrable Q)

@[simp] theorem gaussianPolynomialMean_C (c : Real) :
    gaussianPolynomialMean (Polynomial.C c) = c := by simp [gaussianPolynomialMean]

@[simp] theorem gaussianPolynomialMean_zero : gaussianPolynomialMean 0 = 0 := by
  simp [gaussianPolynomialMean]

theorem gaussianPolynomialMean_C_mul (c : Real) (P : Polynomial Real) :
    gaussianPolynomialMean (Polynomial.C c*P) = c*gaussianPolynomialMean P := by
  simp only [gaussianPolynomialMean, Polynomial.eval_mul, Polynomial.eval_C, integral_const_mul]

theorem gaussianPolynomialMean_X_mul (P : Polynomial Real) :
    gaussianPolynomialMean (Polynomial.X*P) = gaussianPolynomialMean P.derivative := by
  simpa only [gaussianPolynomialMean, Polynomial.eval_mul, Polynomial.eval_X] using
    gaussianReal_polynomial_stein P

@[simp] theorem hermiteRealPolynomial_zero : hermiteRealPolynomial 0 = 1 := by
  simp [hermiteRealPolynomial, Polynomial.hermite_zero]

theorem hermiteRealPolynomial_succ (n : Nat) :
    hermiteRealPolynomial (n+1) = Polynomial.X*hermiteRealPolynomial n -
      (hermiteRealPolynomial n).derivative := by
  simp [hermiteRealPolynomial, Polynomial.hermite_succ, Polynomial.derivative_map]

/-- The derivative factor n+1 is derived from the raising recurrence. -/
theorem hermiteRealPolynomial_derivative_succ (n : Nat) :
    (hermiteRealPolynomial (n+1)).derivative = Polynomial.C (n+1 : Real)*hermiteRealPolynomial n := by
  induction n with
  | zero => simp [hermiteRealPolynomial_succ]
  | succ n ih =>
    rw [hermiteRealPolynomial_succ (n+1), Polynomial.derivative_sub, Polynomial.derivative_mul]
    simp only [Polynomial.derivative_X, one_mul, ih, Polynomial.derivative_mul,
      Polynomial.derivative_C, zero_mul, zero_add]
    rw [hermiteRealPolynomial_succ n]
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_one]
    ring

/-- Gaussian integration by parts transfers one Hermite degree to P'. -/
theorem gaussianPolynomialMean_hermite_succ_mul (n : Nat) (P : Polynomial Real) :
    gaussianPolynomialMean (hermiteRealPolynomial (n+1)*P) =
      gaussianPolynomialMean (hermiteRealPolynomial n*P.derivative) := by
  rw [hermiteRealPolynomial_succ, sub_mul, mul_assoc, gaussianPolynomialMean_sub]
  have h := gaussianPolynomialMean_X_mul (hermiteRealPolynomial n*P)
  rw [Polynomial.derivative_mul, gaussianPolynomialMean_add] at h
  linarith

@[simp] theorem gaussianPolynomialMean_hermite_succ (n : Nat) :
    gaussianPolynomialMean (hermiteRealPolynomial (n+1)) = 0 := by
  simpa only [mul_one, Polynomial.derivative_one, mul_zero, gaussianPolynomialMean_zero] using
    gaussianPolynomialMean_hermite_succ_mul n 1

/-- The unnormalized diagonal is exactly n!, and off-diagonal terms vanish. -/
theorem gaussianPolynomialMean_hermite_mul (n m : Nat) :
    gaussianPolynomialMean (hermiteRealPolynomial n*hermiteRealPolynomial m) =
      if n=m then (n.factorial : Real) else 0 := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => simp [gaussianPolynomialMean]
    | succ m => simp
  | succ n ih =>
    cases m with
    | zero => simp
    | succ m =>
      rw [gaussianPolynomialMean_hermite_succ_mul, hermiteRealPolynomial_derivative_succ]
      have he : hermiteRealPolynomial n*(Polynomial.C (m+1 : Real)*hermiteRealPolynomial m) =
          Polynomial.C (m+1 : Real)*(hermiteRealPolynomial n*hermiteRealPolynomial m) := by ring
      rw [he, gaussianPolynomialMean_C_mul, ih]
      by_cases hnm : n=m
      · subst m
        simp [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      · simp [hnm]

/-- Orthogonality uses exactly the source's normalized Hermite functions. -/
theorem normalizedHermite_gaussian_inner (n m : Nat) :
    (∫ x : Real, normalizedHermite n x * normalizedHermite m x ∂gaussianReal 0 1) =
      if n=m then 1 else 0 := by
  have he (x : Real) : normalizedHermite n x * normalizedHermite m x =
      (hermiteRealPolynomial n*hermiteRealPolynomial m).eval x /
        (Real.sqrt (n.factorial : Real)*Real.sqrt (m.factorial : Real)) := by
    simp only [normalizedHermite_eval, hermiteRealPolynomial, Polynomial.eval_mul, Polynomial.eval_map]
    ring
  simp_rw [he]
  rw [integral_div]
  change gaussianPolynomialMean (hermiteRealPolynomial n*hermiteRealPolynomial m) / _ = _
  rw [gaussianPolynomialMean_hermite_mul]
  by_cases hnm : n=m
  · subst m
    simp only [if_true]
    rw [← sq, Real.sq_sqrt (by positivity)]
    exact div_self (by exact_mod_cast (Nat.factorial_ne_zero n))
  · simp [hnm]

end PaperFormalization.MatrixFactorization
