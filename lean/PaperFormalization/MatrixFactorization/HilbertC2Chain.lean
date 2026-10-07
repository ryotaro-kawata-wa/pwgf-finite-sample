import Mathlib

/-! # MF36: C2 chain rule in the actual real Hilbert norm

The Hessian is the derivative of the Riesz gradient, an operator on the same
Hilbert space. The second chain rule retains the acceleration pairing.
-/
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

noncomputable def hilbertGradient (J : E → Real) (x : E) : E :=
  (InnerProductSpace.toDual Real E).symm (fderiv Real J x)

noncomputable def hilbertHessian (J : E → Real) (x : E) : E →L[Real] E :=
  fderiv Real (hilbertGradient J) x

/-- The Riesz gradient uses precisely the ambient Hilbert differential. -/
theorem hilbertGradient_pairing (J : E → Real) (x v : E) :
    inner Real (hilbertGradient J x) v = fderiv Real J x v :=
  InnerProductSpace.toDual_symm_apply

theorem hilbertGradient_contDiff (J : E → Real) (hJ : ContDiff Real 2 J) :
    ContDiff Real 1 (hilbertGradient J) := by
  have hd : ContDiff Real 1 (fderiv Real J) :=
    (contDiff_succ_iff_fderiv (n := (1 : WithTop ℕ∞))).mp hJ |>.2.2
  exact (InnerProductSpace.toDual Real E).symm.toContinuousLinearEquiv.contDiff.comp hd

theorem hilbertHessian_continuous (J : E → Real) (hJ : ContDiff Real 2 J) :
    Continuous (hilbertHessian J) :=
  (hilbertGradient_contDiff J hJ).continuous_fderiv (by decide)

/-- Continuity of the operator norm is taken before any concrete Hilbert-space instantiation. -/
theorem hilbertHessian_norm_continuous (J : E → Real) (hJ : ContDiff Real 2 J) :
    Continuous (fun x => ‖hilbertHessian J x‖) := (hilbertHessian_continuous J hJ).norm

theorem hilbertHessian_norm_nonneg (J : E → Real) (x : E) :
    0 ≤ ‖hilbertHessian J x‖ := norm_nonneg _

theorem hilbert_first_chain (J : E → Real) (hJ : Differentiable Real J)
    {theta : Real → E} {v : E} {t : Real} (htheta : HasDerivAt theta v t) :
    HasDerivAt (fun s => J (theta s)) (inner Real (hilbertGradient J (theta t)) v) t := by
  rw [hilbertGradient_pairing]
  exact (hJ (theta t)).hasFDerivAt.comp_hasDerivAt t htheta

/-- The actual scalar second derivative includes both Hessian and acceleration. -/
theorem hilbert_second_chain (J : E → Real) (hJ : ContDiff Real 2 J)
    {theta velocity : Real → E} (htheta : ∀ s, HasDerivAt theta (velocity s) s)
    {acceleration : E} {t : Real} (hvelocity : HasDerivAt velocity acceleration t) :
    HasDerivAt (deriv (fun s => J (theta s)))
      (inner Real (hilbertHessian J (theta t) (velocity t)) (velocity t) +
       inner Real (hilbertGradient J (theta t)) acceleration) t := by
  have he : deriv (fun s => J (theta s)) =
      (fun s => inner Real (hilbertGradient J (theta s)) (velocity s)) := by
    funext s
    exact (hilbert_first_chain J (hJ.differentiable (by decide)) (htheta s)).deriv
  rw [he]
  have hg := (((hilbertGradient_contDiff J hJ).differentiable (by decide)) (theta t)).hasFDerivAt.comp_hasDerivAt t (htheta t)
  simpa only [Function.comp_def, hilbertHessian, add_comm] using hg.inner (𝕜 := Real) hvelocity

/-- Operator norm control is in the same Hilbert space as the two curve jets. -/
theorem hilbert_second_chain_lower (J : E → Real) (hJ : ContDiff Real 2 J)
    {theta velocity : Real → E} (htheta : ∀ s, HasDerivAt theta (velocity s) s)
    {acceleration : E} {t : Real} (hvelocity : HasDerivAt velocity acceleration t) :
    -(‖hilbertHessian J (theta t)‖ * ‖velocity t‖ ^ 2) -
      ‖hilbertGradient J (theta t)‖ * ‖acceleration‖ ≤
        deriv (deriv (fun s => J (theta s))) t := by
  rw [(hilbert_second_chain J hJ htheta hvelocity).deriv]
  have h1 := neg_le_of_abs_le (abs_real_inner_le_norm (hilbertHessian J (theta t) (velocity t)) (velocity t))
  have h2 := neg_le_of_abs_le (abs_real_inner_le_norm (hilbertGradient J (theta t)) acceleration)
  have h3 := mul_le_mul_of_nonneg_right ((hilbertHessian J (theta t)).le_opNorm (velocity t)) (norm_nonneg (velocity t))
  nlinarith

end PaperFormalization.MatrixFactorization
