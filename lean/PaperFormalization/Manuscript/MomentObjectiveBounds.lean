import PaperFormalization.Manuscript.MomentGradientField
import PaperFormalization.Manuscript.FeatureRegularityBounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic

/-! # Objective derivative bounds on a convex feasible moment region

Smoothness is required only on an open neighborhood U. Only the feasible
region S is assumed convex. The actual gradient and Riesz Hessian inherit
norm and difference estimates from the scalar objective's Frechet derivatives;
no uniform bound on lower derivatives is silently added.
-/

open Set

namespace PaperFormalization.Manuscript

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The Riesz representation does not change the Hessian operator norm. -/
theorem norm_momentObjectiveHessian_eq (G : H → ℝ) (theta : H) :
    ‖momentObjectiveHessian G theta‖ = ‖fderiv ℝ (fderiv ℝ G) theta‖ := by
  exact (InnerProductSpace.toDual ℝ H).symm.toLinearIsometry.norm_toContinuousLinearMap_comp

/-- Riesz representation preserves differences of the actual Hessians too. -/
theorem norm_momentObjectiveHessian_sub_eq (G : H → ℝ) (theta theta' : H) :
    ‖momentObjectiveHessian G theta - momentObjectiveHessian G theta'‖ =
      ‖fderiv ℝ (fderiv ℝ G) theta - fderiv ℝ (fderiv ℝ G) theta'‖ := by
  unfold momentObjectiveHessian
  rw [← ContinuousLinearMap.comp_sub]
  exact (InnerProductSpace.toDual ℝ H).symm.toLinearIsometry.norm_toContinuousLinearMap_comp

/-- Riesz representation preserves actual gradient differences. -/
theorem norm_gradient_sub_eq_fderiv (G : H → ℝ) (theta theta' : H) :
    ‖gradient G theta - gradient G theta'‖ = ‖fderiv ℝ G theta - fderiv ℝ G theta'‖ := by
  unfold gradient
  rw [← map_sub, LinearIsometryEquiv.norm_map]

set_option maxSynthPendingDepth 8 in
/-- A bound on the actual third Frechet derivative on the convex feasible
region gives the actual Hessian Lipschitz constant. U need not be convex. -/
theorem momentObjectiveHessian_sub_le_of_third_bound
    (G : H → ℝ) (S U : Set H) (hS : Convex ℝ S) (hSU : S ⊆ U)
    (hU : IsOpen U) (hG : ContDiffOn ℝ 3 G U) (C3 : ℝ)
    (hthird : ∀ theta ∈ S, ‖iteratedFDeriv ℝ 3 G theta‖ ≤ C3)
    (theta theta' : H) (htheta : theta ∈ S) (htheta' : theta' ∈ S) :
    ‖momentObjectiveHessian G theta - momentObjectiveHessian G theta'‖ ≤ C3 * ‖theta - theta'‖ := by
  rw [norm_momentObjectiveHessian_sub_eq]
  apply hS.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := fderiv ℝ (fderiv ℝ G)) _ _ htheta' htheta
  · intro x hx
    exact (((hG.contDiffAt (hU.mem_nhds (hSU hx))).fderiv_right (m := 2) (by norm_num)).fderiv_right
      (m := 1) (by norm_num)).differentiableAt_one
  · intro x hx
    rw [norm_third_fderiv_eq_iterated]
    exact hthird x hx

/-- A Hessian bound on S gives the actual gradient Lipschitz estimate, with
only local C2 smoothness on its open neighborhood. -/
theorem gradient_sub_le_of_momentObjectiveHessian_bound
    (G : H → ℝ) (S U : Set H) (hS : Convex ℝ S) (hSU : S ⊆ U)
    (hU : IsOpen U) (hG : ContDiffOn ℝ 2 G U) (B : ℝ)
    (hHess : ∀ theta ∈ S, ‖momentObjectiveHessian G theta‖ ≤ B)
    (theta theta' : H) (htheta : theta ∈ S) (htheta' : theta' ∈ S) :
    ‖gradient G theta - gradient G theta'‖ ≤ B * ‖theta - theta'‖ := by
  rw [norm_gradient_sub_eq_fderiv]
  apply hS.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) _ _ htheta' htheta
  · intro x hx
    exact ((hG.contDiffAt (hU.mem_nhds (hSU hx))).fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  · intro x hx
    simpa only [norm_momentObjectiveHessian_eq] using hHess x hx

/-- The Hessian magnitude follows from one finite anchor norm and the third
derivative bound, rather than a new uniform second derivative assumption. -/
theorem momentObjectiveHessian_norm_le_anchor
    (G : H → ℝ) (S U : Set H) (hS : Convex ℝ S) (hSU : S ⊆ U)
    (hU : IsOpen U) (hG : ContDiffOn ℝ 3 G U) (C3 : ℝ)
    (hthird : ∀ theta ∈ S, ‖iteratedFDeriv ℝ 3 G theta‖ ≤ C3)
    (theta theta0 : H) (htheta : theta ∈ S) (htheta0 : theta0 ∈ S) :
    ‖momentObjectiveHessian G theta‖ ≤
      ‖momentObjectiveHessian G theta0‖ + C3 * ‖theta - theta0‖ := by
  have hd := momentObjectiveHessian_sub_le_of_third_bound G S U hS hSU hU hG C3 hthird
    theta theta0 htheta htheta0
  have ht := norm_add_le (momentObjectiveHessian G theta - momentObjectiveHessian G theta0)
    (momentObjectiveHessian G theta0)
  rw [sub_add_cancel] at ht
  linarith

/-- On a feasible region with radius R from the fixed anchor, the original
third derivative bound supplies the exact source intermediate constants Q R
and Q R^2. Q uses only the source anchor derivative norms and C3. This proof
uses a coarser gradient-anchor estimate than the optional half-quadratic one,
but gives the same final source constants without any new uniform bound. -/
theorem source_momentObjective_bounds_from_anchor
    (G : H → ℝ) (S U : Set H) (hS : Convex ℝ S) (hSU : S ⊆ U)
    (hU : IsOpen U) (hG : ContDiffOn ℝ 3 G U) (C3 : ℝ)
    (hthird : ∀ theta ∈ S, ‖iteratedFDeriv ℝ 3 G theta‖ ≤ C3)
    (theta0 : H) (htheta0 : theta0 ∈ S) (Q R : ℝ) (hR : 1 ≤ R)
    (hQ : Q = 1 + ‖fderiv ℝ G theta0‖ + ‖iteratedFDeriv ℝ 2 G theta0‖ + C3)
    (hradius : ∀ theta ∈ S, ‖theta - theta0‖ ≤ R) :
    1 ≤ Q ∧ ∀ theta ∈ S,
      ‖gradient G theta‖ ≤ Q * R ^ 2 ∧ ‖momentObjectiveHessian G theta‖ ≤ Q * R := by
  have hC3 : 0 ≤ C3 := (norm_nonneg _).trans (hthird theta0 htheta0)
  have hR0 : 0 ≤ R := by linarith
  have hgrad0 : ‖gradient G theta0‖ = ‖fderiv ℝ G theta0‖ := by
    exact (InnerProductSpace.toDual ℝ H).symm.norm_map _
  have hHess0 : ‖momentObjectiveHessian G theta0‖ = ‖iteratedFDeriv ℝ 2 G theta0‖ := by
    rw [norm_momentObjectiveHessian_eq, norm_second_fderiv_eq_iterated]
  have hbound : ∀ theta ∈ S,
      ‖momentObjectiveHessian G theta‖ ≤ ‖momentObjectiveHessian G theta0‖ + C3 * R := by
    intro theta htheta
    exact (momentObjectiveHessian_norm_le_anchor G S U hS hSU hU hG C3 hthird
      theta theta0 htheta htheta0).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hradius theta htheta) hC3))
  have hG2 : ContDiffOn ℝ 2 G U := hG.of_le (by norm_num)
  have hQ' : Q = 1 + ‖gradient G theta0‖ + ‖momentObjectiveHessian G theta0‖ + C3 := by
    simpa only [hgrad0, hHess0] using hQ
  constructor
  · rw [hQ']
    linarith [norm_nonneg (gradient G theta0), norm_nonneg (momentObjectiveHessian G theta0)]
  intro theta htheta
  have hgdiff := gradient_sub_le_of_momentObjectiveHessian_bound G S U hS hSU hU hG2
    (‖momentObjectiveHessian G theta0‖ + C3 * R) hbound theta theta0 htheta htheta0
  have hg : ‖gradient G theta‖ ≤ ‖gradient G theta0‖ +
      (‖momentObjectiveHessian G theta0‖ + C3 * R) * R := by
    have ht := norm_add_le (gradient G theta - gradient G theta0) (gradient G theta0)
    rw [sub_add_cancel] at ht
    have hm := mul_le_mul_of_nonneg_left (hradius theta htheta)
      (add_nonneg (norm_nonneg (momentObjectiveHessian G theta0)) (mul_nonneg hC3 hR0))
    linarith
  have hR2 : 1 ≤ R ^ 2 := by nlinarith
  have hRR2 : R ≤ R ^ 2 := by nlinarith
  constructor
  · calc
      ‖gradient G theta‖ ≤ ‖gradient G theta0‖ +
          (‖momentObjectiveHessian G theta0‖ + C3 * R) * R := hg
      _ ≤ ‖gradient G theta0‖ * R ^ 2 +
          ‖momentObjectiveHessian G theta0‖ * R ^ 2 + C3 * R ^ 2 := by
        have h1 := mul_le_mul_of_nonneg_left hR2 (norm_nonneg (gradient G theta0))
        have h2 := mul_le_mul_of_nonneg_left hRR2 (norm_nonneg (momentObjectiveHessian G theta0))
        nlinarith
      _ ≤ Q * R ^ 2 := by rw [hQ']; nlinarith [sq_nonneg R]
  · calc
      ‖momentObjectiveHessian G theta‖ ≤ ‖momentObjectiveHessian G theta0‖ + C3 * R :=
        hbound theta htheta
      _ ≤ ‖momentObjectiveHessian G theta0‖ * R + C3 * R := by
        have h := mul_le_mul_of_nonneg_left hR (norm_nonneg (momentObjectiveHessian G theta0))
        linarith
      _ ≤ Q * R := by
        rw [hQ']
        nlinarith [mul_nonneg (norm_nonneg (gradient G theta0)) hR0]

end PaperFormalization.Manuscript
