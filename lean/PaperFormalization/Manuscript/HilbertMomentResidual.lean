import PaperFormalization.Manuscript.WeightedFeatureDerivatives
import PaperFormalization.Manuscript.LocalMomentHessian

/-! # The literal residual controls actual Hilbert moment differences

The scaled Hilbert difference is compared directly with the original weighted
l1 residual. This preserves L=0 and does not divide by the local constant.
The two measure-Hessian errors each use half of the same literal residual.
Identification of the supplied coordinate paths with a conditional population
law is a separate probability obligation.
-/

open scoped NNReal

set_option maxSynthPendingDepth 8

namespace PaperFormalization.Manuscript

variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

omit [∀ n, CompleteSpace (H n)] in
/-- Exact scaled coordinate norms of an encoded Hilbert difference. -/
theorem scaled_moment_difference_coordinate_norm
    (c p : ℝ) (L : ℝ≥0) (Z P : ∀ n, ℝ → H n) (t : ℝ)
    (z w : lp H 2)
    (hz : ∀ n, z n = sourceFeatureScale c p n • Z n t)
    (hw : ∀ n, w n = sourceFeatureScale c p n • P n t) (n : ℕ) :
    ‖((L : ℝ) • (z - w)) n‖ =
      momentResidualTerm (featureResidualWeight c p L) Z P n t := by
  change ‖(L : ℝ) • (z n - w n)‖ = _
  rw [hz n, hw n, ← smul_sub, norm_smul, norm_smul,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg L.coe_nonneg,
    abs_of_pos (sourceFeatureScale_pos c p n)]
  change (L : ℝ) * (sourceFeatureScale c p n * ‖Z n t - P n t‖) =
    ((L : ℝ) * sourceFeatureScale c p n) * ‖Z n t - P n t‖
  ring

omit [∀ n, CompleteSpace (H n)] in
/-- The literal source residual bounds L times the actual Hilbert distance;
no positivity of L beyond its original nonnegativity is needed. -/
theorem scaled_moment_difference_le_residual
    (c p : ℝ) (L : ℝ≥0) (Z P : ∀ n, ℝ → H n) (t : ℝ)
    (z w : lp H 2)
    (hz : ∀ n, z n = sourceFeatureScale c p n • Z n t)
    (hw : ∀ n, w n = sourceFeatureScale c p n • P n t)
    (hsum : Summable (fun n => momentResidualTerm (featureResidualWeight c p L) Z P n t)) :
    (L : ℝ) * ‖z - w‖ ≤ momentResidual (featureResidualWeight c p L) Z P t := by
  have h := norm_hilbertSum_le_of_hasSum_coordinate_majorant
    ((L : ℝ) • (z - w)) _ _ hsum.hasSum
    (fun n => (scaled_moment_difference_coordinate_norm c p L Z P t z w hz hw n).le)
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg L.coe_nonneg, momentResidual] using h

/-- The actual signed field and both measure-Hessian blocks are controlled by
the same literal Gamma, with a half-Gamma budget for each Hessian block. -/
theorem source_moment_measure_bounds_by_residual
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (c p : ℝ) (L : ℝ≥0) (Z P : ∀ n, ℝ → H n) (t : ℝ)
    (theta theta' : lp H 2)
    (hz : ∀ n, theta n = sourceFeatureScale c p n • Z n t)
    (hw : ∀ n, theta' n = sourceFeatureScale c p n • P n t)
    (hsum : Summable (fun n => momentResidualTerm (featureResidualWeight c p L) Z P n t))
    (dφ : E → E →L[ℝ] lp H 2) (gradG : lp H 2 → lp H 2) (x y : E)
    (ddφ : E →L[ℝ] (E →L[ℝ] (lp H 2))) (B B' : (lp H 2) →L[ℝ] (lp H 2))
    (Q R : ℝ) (hQ : 1 ≤ Q) (hR : 1 ≤ R) (hL : (L : ℝ) = 4 * Q * R ^ 3)
    (hx : ‖dφ x‖ ≤ R) (hy : ‖dφ y‖ ≤ R) (hdd : ‖ddφ‖ ≤ R)
    (hg : ‖gradG theta - gradG theta'‖ ≤ Q * R * ‖theta - theta'‖)
    (hB : ‖B - B'‖ ≤ Q * ‖theta - theta'‖) :
    ‖momentGradientField dφ gradG (theta, x) - momentGradientField dφ gradG (theta', x)‖ ≤
        momentResidual (featureResidualWeight c p L) Z P t ∧
    ‖momentSpatialHessian ddφ (gradG theta) - momentSpatialHessian ddφ (gradG theta')‖ ≤
        momentResidual (featureResidualWeight c p L) Z P t / 2 ∧
    ‖momentIntegralHessian (dφ x) (dφ y) B - momentIntegralHessian (dφ x) (dφ y) B'‖ ≤
        momentResidual (featureResidualWeight c p L) Z P t / 2 := by
  have hres := scaled_moment_difference_le_residual c p L Z P t theta theta' hz hw hsum
  rw [hL] at hres
  obtain ⟨hf, hs, hi⟩ := source_moment_measure_bounds dφ gradG theta theta' x y ddφ B B'
    Q R ‖theta - theta'‖ hQ hR hx hy hdd le_rfl hg hB
  exact ⟨hf.trans hres, by linarith, by linarith⟩

end PaperFormalization.Manuscript
