import PaperFormalization.MatrixFactorization.GaussianPolynomialStein
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.Algebra.MvPolynomial

/-! # Coordinate Stein identities for the actual product Gaussian

Finite products of one-dimensional Gaussian measures are the source of the
existing finite-dimensional standard Gaussian. Polynomial integrability is
proved from monomials before coordinate integration by parts is used.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Actual monomial evaluation uses the finite product over all coordinates. -/
theorem gaussian_monomial_eval {ι : Type*} [Fintype ι]
    (n : ι →₀ Nat) (c : Real) (x : ι → Real) :
    MvPolynomial.eval x (MvPolynomial.monomial n c) = c * ∏ i, x i ^ n i := by
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype]
  intro i
  exact pow_zero _

/-- Every real multivariate polynomial is integrable under the original
independent coordinate Gaussian law. -/
theorem gaussianPi_polynomial_integrable {ι : Type*} [Fintype ι]
    (P : MvPolynomial ι Real) :
    Integrable (fun x : ι → Real => MvPolynomial.eval x P)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial n c =>
      simp only [gaussian_monomial_eval]
      apply Integrable.const_mul
      apply Integrable.fintype_prod
      intro i
      convert! gaussianReal_polynomial_integrable (Polynomial.X ^ n i) using 1
      funext x
      simp only [Polynomial.eval_pow, Polynomial.eval_X]
      generalize n i = k
      induction k with
      | zero => rfl
      | succ k ih => simpa [npowRec, pow_succ] using congrArg (fun y : Real => y*x) ih
  | add P Q hP hQ =>
      convert! hP.add hQ using 1
      funext x
      simp

/-- A coordinate-weighted multivariate polynomial is integrable as well. -/
theorem gaussianPi_coordinate_polynomial_integrable {ι : Type*} [Fintype ι]
    (i : ι) (P : MvPolynomial ι Real) :
    Integrable (fun x : ι → Real => x i * MvPolynomial.eval x P)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  convert! gaussianPi_polynomial_integrable (MvPolynomial.X i * P) using 1
  funext x
  simp

/-- Factoring one selected coordinate is an application of finite-product
Fubini; this identity itself needs no model-specific hypothesis. -/
theorem gaussianPi_integral_coordinate_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (f : ι → Real → Real) :
    (∫ x : ι → Real, f i (x i) * ∏ j ∈ Finset.univ.erase i, f j (x j)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
    (∫ x : Real, f i x ∂gaussianReal 0 1) *
      ∏ j ∈ Finset.univ.erase i, ∫ x : Real, f j x ∂gaussianReal 0 1 := by
  simp_rw [Finset.mul_prod_erase (Finset.univ : Finset ι) (fun j => f j _) (Finset.mem_univ i)]
  rw [integral_fintype_prod_eq_prod]
  exact (Finset.mul_prod_erase (Finset.univ : Finset ι) _ (Finset.mem_univ i)).symm

/-- Coordinate integration by parts for a separated polynomial product. -/
theorem gaussianPi_product_stein {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (P : ι → Polynomial Real) :
    (∫ x : ι → Real, x i * ∏ j, (P j).eval (x j)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
    (∫ x : Real, (P i).derivative.eval x ∂gaussianReal 0 1) *
      ∏ j ∈ Finset.univ.erase i, ∫ x : Real, (P j).eval x ∂gaussianReal 0 1 := by
  let Q : ι → Real → Real := fun j x => if j = i then x*(P j).eval x else (P j).eval x
  have hQ (x : ι → Real) :
      x i * ∏ j, (P j).eval (x j) = Q i (x i) * ∏ j ∈ Finset.univ.erase i, Q j (x j) := by
    rw [← Finset.mul_prod_erase (Finset.univ : Finset ι) (fun j => (P j).eval (x j))
      (Finset.mem_univ i)]
    simp only [Q, if_pos rfl, mul_assoc]
    congr 1
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    simp only [if_neg (Finset.mem_erase.mp hj).1]
  simp_rw [hQ]
  rw [gaussianPi_integral_coordinate_product]
  dsimp only [Q]
  simp only [ite_true, eq_self]
  rw [gaussianReal_polynomial_stein]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp only [if_neg (Finset.mem_erase.mp hj).1]

/-- Stein's identity for a monomial under the genuine product Gaussian law. -/
theorem gaussianPi_monomial_stein {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (n : ι →₀ Nat) (c : Real) :
    (∫ x : ι → Real, x i * MvPolynomial.eval x (MvPolynomial.monomial n c)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
    ∫ x : ι → Real, MvPolynomial.eval x
      (MvPolynomial.pderiv i (MvPolynomial.monomial n c))
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  have he (x : ι → Real) :
      MvPolynomial.eval x (MvPolynomial.pderiv i (MvPolynomial.monomial n c)) =
      c * ((n i : Real) * x i^(n i-1)) * ∏ j ∈ Finset.univ.erase i, x j^n j := by
    rw [MvPolynomial.pderiv_monomial, gaussian_monomial_eval]
    rw [← Finset.mul_prod_erase (Finset.univ : Finset ι)
      (fun j => x j ^ (n - Finsupp.single i 1 : ι →₀ Nat) j) (Finset.mem_univ i)]
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
    have hrest : (∏ j ∈ Finset.univ.erase i, x j ^ (n j - Finsupp.single i 1 j)) =
        ∏ j ∈ Finset.univ.erase i, x j^n j := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [(Finset.mem_erase.mp hj).1]
    rw [hrest]
    ring
  simp only [gaussian_monomial_eval]
  calc
    _ = c * (∫ x : ι → Real, x i * ∏ j, x j^n j
        ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by ring)
    _ = c * ((∫ x : Real, ((Polynomial.X ^ n i : Polynomial Real).derivative).eval x
        ∂gaussianReal 0 1) *
        ∏ j ∈ Finset.univ.erase i, ∫ x : Real, x^n j ∂gaussianReal 0 1) := by
      congr 1
      simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
        gaussianPi_product_stein i (fun j => Polynomial.X ^ n j)
    _ = _ := by
      simp_rw [he]
      simp only [Polynomial.derivative_X_pow, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      have hf := gaussianPi_integral_coordinate_product i
        (fun j x => if j = i then (n i : Real)*x^(n i-1) else x^n j)
      simp only [ite_true, eq_self] at hf
      have hr : (∏ j ∈ Finset.univ.erase i,
          ∫ x : Real, (if j = i then (n i : Real)*x^(n i-1) else x^n j) ∂gaussianReal 0 1) =
          ∏ j ∈ Finset.univ.erase i, ∫ x : Real, x^n j ∂gaussianReal 0 1 := by
        apply Finset.prod_congr rfl
        intro j hj
        simp only [if_neg (Finset.mem_erase.mp hj).1]
      rw [hr] at hf
      rw [← hf]
      rw [← integral_const_mul]
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun x => ?_)
      simp only [ite_true, eq_self]
      have hrest : (∏ j ∈ Finset.univ.erase i,
          (if j = i then (n i : Real)*x j^(n i-1) else x j^n j)) =
          ∏ j ∈ Finset.univ.erase i, x j^n j := by
        exact Finset.prod_congr rfl (fun j hj => if_neg (Finset.mem_erase.mp hj).1)
      rw [hrest]
      ring

/-- Coordinate Stein's identity for every real multivariate polynomial. -/
theorem gaussianPi_polynomial_stein {ι : Type*} [Fintype ι] (i : ι)
    (P : MvPolynomial ι Real) :
    (∫ x : ι → Real, x i * MvPolynomial.eval x P
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
    ∫ x : ι → Real, MvPolynomial.eval x (MvPolynomial.pderiv i P)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial n c => exact gaussianPi_monomial_stein i n c
  | add P Q hP hQ =>
      simp only [map_add, mul_add]
      rw [integral_add (gaussianPi_coordinate_polynomial_integrable i P)
        (gaussianPi_coordinate_polynomial_integrable i Q),
        integral_add (gaussianPi_polynomial_integrable (MvPolynomial.pderiv i P))
          (gaussianPi_polynomial_integrable (MvPolynomial.pderiv i Q)), hP, hQ]

/-- The existing standard Gaussian is used via its proved product-coordinate
representation, so this is an integrability result for the actual input law. -/
theorem gaussian_mvPolynomial_integrable {d : Nat} (P : MvPolynomial (Fin d) Real) :
    Integrable (fun z : Weight d => MvPolynomial.eval (fun i => z i) P)
      (stdGaussian (Weight d)) := by
  rw [← map_pi_eq_stdGaussian]
  have hc : Continuous (fun z : Weight d => MvPolynomial.eval (fun i => z i) P) :=
    P.continuous_eval.comp (by fun_prop)
  apply (integrable_map_measure hc.aestronglyMeasurable (by fun_prop)).mpr
  simpa only [Function.comp_def, PiLp.toLp_apply] using gaussianPi_polynomial_integrable P

/-- Equality of polynomial expectations under the actual Gaussian and its
independent coordinate representation. -/
theorem gaussian_mvPolynomial_integral {d : Nat} (P : MvPolynomial (Fin d) Real) :
    (∫ z : Weight d, MvPolynomial.eval (fun i => z i) P ∂stdGaussian (Weight d)) =
    ∫ x : Fin d → Real, MvPolynomial.eval x P
      ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1) := by
  have hc : Continuous (fun z : Weight d => MvPolynomial.eval (fun i => z i) P) :=
    P.continuous_eval.comp (by fun_prop)
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) hc.aestronglyMeasurable]

/-- Actual standard-Gaussian coordinate Stein identity for any polynomial. -/
theorem gaussian_mvPolynomial_coordinate_stein {d : Nat} (i : Fin d)
    (P : MvPolynomial (Fin d) Real) :
    (∫ z : Weight d, z i * MvPolynomial.eval (fun j => z j) P ∂stdGaussian (Weight d)) =
    ∫ z : Weight d, MvPolynomial.eval (fun j => z j) (MvPolynomial.pderiv i P)
      ∂stdGaussian (Weight d) := by
  have he := gaussian_mvPolynomial_integral (MvPolynomial.X i * P)
  simp only [map_mul, MvPolynomial.eval_X] at he
  rw [he, gaussianPi_polynomial_stein, ← gaussian_mvPolynomial_integral]

/-- Directional Gaussian integration by parts, with a finite sum of the
actual polynomial partial derivatives. -/
theorem gaussian_mvPolynomial_directional_stein {d : Nat} (s : Weight d)
    (P : MvPolynomial (Fin d) Real) :
    (∫ z : Weight d, inner Real s z * MvPolynomial.eval (fun j => z j) P
      ∂stdGaussian (Weight d)) =
    ∑ i, s i * ∫ z : Weight d, MvPolynomial.eval (fun j => z j) (MvPolynomial.pderiv i P)
      ∂stdGaussian (Weight d) := by
  have hinner (z : Weight d) : inner Real s z = ∑ i, s i*z i := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  simp_rw [hinner, Finset.sum_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    have hiint := gaussian_mvPolynomial_coordinate_stein i P
    simp_rw [mul_assoc]
    rw [integral_const_mul, hiint]
  · intro i hi
    have hint := gaussian_mvPolynomial_integrable (MvPolynomial.X i * P)
    simp only [map_mul, MvPolynomial.eval_X] at hint
    simpa only [mul_assoc] using hint.const_mul (s i)

end PaperFormalization.MatrixFactorization
