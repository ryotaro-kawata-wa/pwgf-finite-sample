import PaperFormalization.Manuscript.MomentRegionGeometry
import PaperFormalization.Manuscript.WeightedFeatureSpatial

/-! # Actual feature derivatives bounded by the literal source moment radius

The already proved derivative series envelope is dominated by exactly the
same R used for feasible moments. Third-derivative existence and growth are
needed only for the second derivative's spatial difference, not its magnitude.
-/

set_option maxSynthPendingDepth 8

namespace PaperFormalization.Manuscript

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]
variable (c C g p q K D alpha : ℝ) (φ : ∀ n, E → H n)
  (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (hD : 1 ≤ D)
  (hφ : ∀ n, ContDiff ℝ 2 (φ n))
  (hgrowth : ∀ n x k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) x‖ ≤
    featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1 - k)))

include hc hC hp hq hK hD hφ hgrowth

/-- J0 and both actual derivative norms share the literal source radius R. -/
theorem source_feature_norms_le_radius (x : E) (hx : ‖x‖ ≤ D) :
    ‖sourceWeightedFeatureMap c p φ x‖ ≤ sourceMomentRadius c C g p q K D alpha ∧
    ‖fderiv ℝ (sourceWeightedFeatureMap c p φ) x‖ ≤ sourceMomentRadius c C g p q K D alpha ∧
    ‖fderiv ℝ (fderiv ℝ (sourceWeightedFeatureMap c p φ)) x‖ ≤
      sourceMomentRadius c C g p q K D alpha := by
  have hr := source_feature_envelope_le_radius c C g p q K D alpha hc hC hp hq hK hD
  exact ⟨(norm_sourceWeightedFeatureMap_le c C g p q φ hc hC hp hq hgrowth D hD x hx).trans
      (hr.1.trans hr.2),
    (norm_fderiv_sourceWeightedFeatureMap_le c C g p q φ hc hC hp hq hφ hgrowth D hD x hx).trans
      (hr.1.trans hr.2),
    (norm_second_fderiv_sourceWeightedFeatureMap_le c C g p q φ hc hC hp hq hφ hgrowth D hD x hx).trans
      (hr.1.trans hr.2)⟩

/-- The actual first feature derivative is locally R-Lipschitz. -/
theorem source_feature_fderiv_sub_le_radius (x y : E) (hx : ‖x‖ ≤ D) (hy : ‖y‖ ≤ D) :
    ‖fderiv ℝ (sourceWeightedFeatureMap c p φ) x - fderiv ℝ (sourceWeightedFeatureMap c p φ) y‖ ≤
      sourceMomentRadius c C g p q K D alpha * ‖x - y‖ := by
  have hr := source_feature_envelope_le_radius c C g p q K D alpha hc hC hp hq hK hD
  exact (norm_fderiv_sourceWeightedFeatureMap_sub_le c C g p q φ hc hC hp hq hφ hgrowth
    D hD x y hx hy).trans (mul_le_mul_of_nonneg_right (hr.1.trans hr.2) (norm_nonneg _))

/-- The actual second feature derivative is locally R-Lipschitz from the
source's existing third derivative and its growth; D3 continuity is not used. -/
theorem source_feature_second_fderiv_sub_le_radius
    (hthird : ∀ n z, DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ (φ n))) z)
    (hgrowth₃ : ∀ n z, ‖iteratedFDeriv ℝ 3 (φ n) z‖ ≤
      featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1 - 3)))
    (x y : E) (hx : ‖x‖ ≤ D) (hy : ‖y‖ ≤ D) :
    ‖fderiv ℝ (fderiv ℝ (sourceWeightedFeatureMap c p φ)) x -
      fderiv ℝ (fderiv ℝ (sourceWeightedFeatureMap c p φ)) y‖ ≤
      sourceMomentRadius c C g p q K D alpha * ‖x - y‖ := by
  have hr := source_feature_envelope_le_radius c C g p q K D alpha hc hC hp hq hK hD
  exact (norm_second_fderiv_sourceWeightedFeatureMap_sub_le c C g p q φ hc hC hp hq hφ hgrowth
    hthird hgrowth₃ D hD x y hx hy).trans
      (mul_le_mul_of_nonneg_right (hr.1.trans hr.2) (norm_nonneg _))

end PaperFormalization.Manuscript
