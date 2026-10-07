import PaperFormalization.MatrixFactorization.GaussianTwoPolynomialStein
import PaperFormalization.MatrixFactorization.GaussianHermiteOrthogonality

/-! # MF09: correlated Hermite observations of the actual Gaussian

The covariance recurrence follows from the proved multivariate polynomial
Stein identity. Both directions are actual unit vectors and their correlation
is their Euclidean inner product. No Hermite contraction formula is assumed.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The raising recurrence cancels the derivative in the unit first direction,
leaving the actual correlation times the derivative in the second direction. -/
theorem gaussian_hermite_succ_cross_polynomial {d : Nat} (n : Nat)
    (P : Polynomial Real) (u v : UnitSphere d) :
    (∫ z : Weight d, (hermiteRealPolynomial (n+1)).eval (inner Real u.val z)*
      P.eval (inner Real v.val z) ∂stdGaussian (Weight d)) =
      inner Real u.val v.val * ∫ z : Weight d,
        (hermiteRealPolynomial n).eval (inner Real u.val z)*
          P.derivative.eval (inner Real v.val z) ∂stdGaussian (Weight d) := by
  have hi := gaussian_two_polynomial_integrable u.val v.val
    (Polynomial.X*hermiteRealPolynomial n) P
  have hd := gaussian_two_polynomial_integrable u.val v.val
    (hermiteRealPolynomial n).derivative P
  simp only [Polynomial.eval_mul, Polynomial.eval_X] at hi
  have hs := gaussian_two_polynomial_stein u.val u.val v.val (hermiteRealPolynomial n) P
  have hu : norm u.val = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using u.property
  simp only [real_inner_self_eq_norm_sq, hu, one_pow, one_mul] at hs
  simp only [hermiteRealPolynomial_succ, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_X, sub_mul]
  rw [integral_sub hi hd]
  linarith

theorem gaussian_hermite_unit_mean_succ {d : Nat} (n : Nat) (u : UnitSphere d) :
    (∫ z : Weight d, (hermiteRealPolynomial (n+1)).eval (inner Real u.val z)
      ∂stdGaussian (Weight d)) = 0 := by
  simpa only [Polynomial.eval_one, mul_one, Polynomial.derivative_one,
    Polynomial.eval_zero, mul_zero, integral_zero] using gaussian_hermite_succ_cross_polynomial n 1 u u

/-- The unnormalized covariance has its exact factorial and correlation power. -/
theorem gaussian_hermite_cross_covariance {d : Nat} (n m : Nat) (u v : UnitSphere d) :
    (∫ z : Weight d, (hermiteRealPolynomial n).eval (inner Real u.val z)*
      (hermiteRealPolynomial m).eval (inner Real v.val z) ∂stdGaussian (Weight d)) =
      if n=m then (n.factorial : Real)*(inner Real u.val v.val)^n else 0 := by
  induction n generalizing m with
  | zero =>
      cases m with
      | zero => simp
      | succ m => simp only [hermiteRealPolynomial_zero, Polynomial.eval_one, one_mul,
          gaussian_hermite_unit_mean_succ, Nat.zero_ne_add_one, if_false]
  | succ n ih =>
      cases m with
      | zero => simp only [hermiteRealPolynomial_zero, Polynomial.eval_one, mul_one,
          gaussian_hermite_unit_mean_succ, Nat.add_one_ne_zero, if_false]
      | succ m =>
          rw [gaussian_hermite_succ_cross_polynomial, hermiteRealPolynomial_derivative_succ]
          simp only [Polynomial.eval_mul, Polynomial.eval_C]
          have he (z : Weight d) :
              (hermiteRealPolynomial n).eval (inner Real u.val z)*
                ((m+1 : Real)*(hermiteRealPolynomial m).eval (inner Real v.val z)) =
              (m+1 : Real)*((hermiteRealPolynomial n).eval (inner Real u.val z)*
                (hermiteRealPolynomial m).eval (inner Real v.val z)) := by ring
          simp_rw [he]
          rw [integral_const_mul, ih]
          by_cases hnm : n=m
          · subst m
            simp only [if_true, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
            ring
          · simp [hnm]

theorem normalizedHermite_gaussian_covariance {d : Nat} (n m : Nat) (u v : UnitSphere d) :
    (∫ z : Weight d, normalizedHermite n (inner Real u.val z)*
      normalizedHermite m (inner Real v.val z) ∂stdGaussian (Weight d)) =
      if n=m then (inner Real u.val v.val)^n else 0 := by
  have he (z : Weight d) : normalizedHermite n (inner Real u.val z)*
      normalizedHermite m (inner Real v.val z) =
      ((hermiteRealPolynomial n).eval (inner Real u.val z)*
        (hermiteRealPolynomial m).eval (inner Real v.val z)) /
        (Real.sqrt (n.factorial : Real)*Real.sqrt (m.factorial : Real)) := by
    simp only [normalizedHermite_eval, hermiteRealPolynomial, Polynomial.eval_map]
    ring
  simp_rw [he]
  rw [integral_div, gaussian_hermite_cross_covariance]
  by_cases hnm : n=m
  · subst m
    simp only [if_true]
    rw [← sq, Real.sq_sqrt (by positivity)]
    field_simp
  · simp [hnm]

/-- The tangent observation removes the second-direction Stein term. -/
theorem gaussian_hermite_transverse_pairing {d : Nat} (n m : Nat)
    (w pole : UnitSphere d) (s : Weight d) (hs : inner Real pole.val s = 0) :
    (∫ z : Weight d, (hermiteRealPolynomial n).eval (inner Real w.val z)*inner Real s z*
      (hermiteRealPolynomial m).derivative.eval (inner Real pole.val z) ∂stdGaussian (Weight d)) =
      if n=m then (n : Real)*(n.factorial : Real)*(inner Real w.val pole.val)^(n-1)*inner Real w.val s else 0 := by
  have hsp : inner Real s pole.val = 0 := by rw [real_inner_comm, hs]
  have he : (fun z : Weight d => (hermiteRealPolynomial n).eval (inner Real w.val z)*inner Real s z*
      (hermiteRealPolynomial m).derivative.eval (inner Real pole.val z)) =
      (fun z : Weight d => inner Real s z*(hermiteRealPolynomial n).eval (inner Real w.val z)*
        (hermiteRealPolynomial m).derivative.eval (inner Real pole.val z)) := by
    funext z
    ring
  rw [he, gaussian_two_polynomial_stein, hsp, zero_mul, add_zero]
  cases n with
  | zero => simp
  | succ n =>
      cases m with
      | zero => simp
      | succ m =>
          simp only [hermiteRealPolynomial_derivative_succ, Polynomial.eval_mul, Polynomial.eval_C]
          have hp (z : Weight d) :
              ((n+1 : Real)*(hermiteRealPolynomial n).eval (inner Real w.val z))*
                ((m+1 : Real)*(hermiteRealPolynomial m).eval (inner Real pole.val z)) =
              ((n+1 : Real)*(m+1))*((hermiteRealPolynomial n).eval (inner Real w.val z)*
                (hermiteRealPolynomial m).eval (inner Real pole.val z)) := by ring
          simp_rw [hp]
          rw [integral_const_mul, gaussian_hermite_cross_covariance]
          by_cases hnm : n=m
          · subst m
            simp only [if_true, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
              Nat.add_one_sub_one, real_inner_comm s w.val]
            ring
          · simp [hnm]

/-- Exact normalized derivative pairing for arbitrary finite Hermite degrees.
This is the scalar identity used by the original activation assembly. -/
theorem normalizedHermite_gaussian_transverse_pairing {d : Nat} (n m : Nat)
    (w pole : UnitSphere d) (s : Weight d) (hs : inner Real pole.val s = 0) :
    (∫ z : Weight d, normalizedHermite n (inner Real w.val z)*inner Real s z*
      normalizedHermiteJet 1 m (inner Real pole.val z) ∂stdGaussian (Weight d)) =
      if n=m then (n : Real)*(inner Real w.val pole.val)^(n-1)*inner Real w.val s else 0 := by
  have he (z : Weight d) : normalizedHermite n (inner Real w.val z)*inner Real s z*
      normalizedHermiteJet 1 m (inner Real pole.val z) =
      ((hermiteRealPolynomial n).eval (inner Real w.val z)*inner Real s z*
        (hermiteRealPolynomial m).derivative.eval (inner Real pole.val z)) /
        (Real.sqrt (n.factorial : Real)*Real.sqrt (m.factorial : Real)) := by
    simp only [normalizedHermite_eval, normalizedHermiteJet, Function.iterate_one,
      hermiteRealPolynomial, Polynomial.eval_map]
    ring
  simp_rw [he]
  rw [integral_div, gaussian_hermite_transverse_pairing n m w pole s hs]
  by_cases hnm : n=m
  · subst m
    simp only [if_true]
    rw [← sq, Real.sq_sqrt (by positivity)]
    field_simp
  · simp [hnm]

end PaperFormalization.MatrixFactorization
