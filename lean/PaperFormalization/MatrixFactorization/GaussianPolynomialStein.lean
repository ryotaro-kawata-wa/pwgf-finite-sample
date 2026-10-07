import PaperFormalization.MatrixFactorization.HermiteDerivatives
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # MF09: polynomial integration by parts for the actual standard Gaussian

All polynomial integrability and the Gaussian density derivative are proved
before integration by parts. This is an analytic foundation for Hermite
orthogonality, not an orthogonality assumption on the model.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

theorem gaussianReal_polynomial_integrable (P : Polynomial Real) :
    Integrable (fun x => P.eval x) (gaussianReal 0 1) := by
  have hpow (n : Nat) : Integrable (fun x : Real => x^n) (gaussianReal 0 1) := by
    by_cases hn : n = 0
    · simp [hn]
    · have hm := (memLp_id_gaussianReal' (μ := (0 : Real)) (v := (1 : NNReal))
        (n : ENNReal) (by simp)).integrable_norm_pow hn
      apply hm.mono' (by fun_prop)
      exact Filter.Eventually.of_forall (fun x => by simp)
  have hsum := integrable_finsetSum (Finset.range (P.natDegree+1))
    (fun n _ => (hpow n).const_mul (P.coeff n))
  simpa only [Polynomial.eval_eq_sum_range] using hsum

theorem gaussianReal_density_polynomial_integrable (P : Polynomial Real) :
    Integrable (fun x : Real => gaussianPDFReal 0 1 x * P.eval x) := by
  have hi := gaussianReal_polynomial_integrable P
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : NNReal) ≠ 0)] at hi
  have hh := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1) (Filter.Eventually.of_forall (fun x => gaussianPDF_lt_top))).mp hi
  simpa only [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _), smul_eq_mul] using hh

theorem standardGaussianDensity_hasDerivAt (x : Real) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have hd := (((((hasDerivAt_id x).pow 2).neg).div_const 2).exp).const_mul
    ((Real.sqrt (2*Real.pi))⁻¹)
  have he : gaussianPDFReal 0 1 = fun y : Real => (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-(y^2)/2) := by
    funext y
    simp [gaussianPDFReal]
  rw [he]
  apply hd.congr_deriv
  simp only [Pi.neg_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  ring

/-- Stein's identity, derived for every real polynomial under N(0,1). -/
theorem gaussianReal_polynomial_stein (P : Polynomial Real) :
    (∫ x : Real, x * P.eval x ∂gaussianReal 0 1) =
      ∫ x : Real, P.derivative.eval x ∂gaussianReal 0 1 := by
  have hP := gaussianReal_density_polynomial_integrable P
  have hdP := gaussianReal_density_polynomial_integrable P.derivative
  have hxP := gaussianReal_density_polynomial_integrable (Polynomial.X*P)
  simp only [Polynomial.eval_mul, Polynomial.eval_X] at hxP
  have hd (x : Real) : HasDerivAt (fun y => gaussianPDFReal 0 1 y * P.eval y)
      (gaussianPDFReal 0 1 x * P.derivative.eval x - gaussianPDFReal 0 1 x * (x*P.eval x)) x := by
    exact ((standardGaussianDensity_hasDerivAt x).mul (P.hasDerivAt x)).congr_deriv (by ring)
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable hd (hdP.sub hxP) hP
  rw [integral_sub hdP hxP] at hz
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0),
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  simp only [smul_eq_mul]
  linarith

end PaperFormalization.MatrixFactorization
