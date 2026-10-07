import PaperFormalization.Manuscript.SourceFeatureRadius
import PaperFormalization.Manuscript.SourceRegionObjective
import PaperFormalization.Manuscript.LocalMomentHessian

/-! # Actual source field and Hessian bounds on the feasible moment hull

These corollaries use the constructed weighted Hilbert feature map and its
actual Frechet derivatives, together with the actual gradient and Hessian of
G. The comparison coefficient is the existing literal source L=4 Q R^3.
The source generator bounds supply the moment radius; no lower derivative
bound or comparison estimate is assumed. The anchor's feature estimate is
derived from order-zero growth at zero.

The moment arguments lie in the ordinary convex hull of the supplied encoded
generators, contained in the original open G-domain. Identifying this hull
with the original measure classes remains a separate theorem. Only the last
corollary uses existence and growth of third feature derivatives, without
assuming their continuity.
-/

set_option maxSynthPendingDepth 8

open Set

namespace PaperFormalization.Manuscript

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

variable (c C g p q K D alpha C3 : ℝ) (φ : ∀ n, E → H n)
  (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (hD : 1 ≤ D)
  (hφ : ∀ n, ContDiff ℝ 2 (φ n))
  (hgrowth : ∀ n x k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) x‖ ≤
    featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1 - k)))
  (Z : Set (lp H 2))
  (hZ : ∀ z ∈ Z, ∀ n, ‖z n‖ ≤ featureWeight c C g p q n * (1 + D ^ (n + 1)) ∨
    ‖z n‖ ≤ featureWeight c C g p q n *
      (1 + K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha)))
  (hanchor : sourceWeightedFeatureMap c p φ 0 ∈ convexHull ℝ Z)
  (G : lp H 2 → ℝ) (U : Set (lp H 2))
  (hU : IsOpen U) (hZU : convexHull ℝ Z ⊆ U) (hG : ContDiffOn ℝ 3 G U)
  (hthirdG : ∀ theta ∈ convexHull ℝ Z, ‖iteratedFDeriv ℝ 3 G theta‖ ≤ C3)

include hc hC hp hq hK hD hφ hgrowth hZ hanchor hU hZU hG hthirdG

/-- The actual signed field and both positive Hessian blocks have magnitude
at most the source comparison coefficient on the radius-D particle ball. -/
theorem source_local_field_magnitude_bounds
    (theta : lp H 2) (htheta : theta ∈ convexHull ℝ Z)
    (x y : E) (hx : ‖x‖ ≤ D) (hy : ‖y‖ ≤ D) :
    let J := sourceWeightedFeatureMap c p φ
    let L := sourceComparisonEnvelope c C g p q K D alpha C3 φ G
    ‖momentGradientField (fderiv ℝ J) (gradient G) (theta, x)‖ ≤ L ∧
    ‖momentSpatialHessian (fderiv ℝ (fderiv ℝ J) x) (gradient G theta)‖ ≤ L ∧
    ‖momentIntegralHessian (fderiv ℝ J x) (fderiv ℝ J y)
      (momentObjectiveHessian G theta)‖ ≤ L := by
  have hzero : ∀ n, ‖φ n 0‖ ≤ featureGrowth C g q n := by
    intro n
    simpa only [norm_iteratedFDeriv_zero, Nat.sub_zero, norm_zero,
      zero_pow (Nat.succ_ne_zero n), add_zero, mul_one] using hgrowth n 0 0 (by omega)
  have hb := source_region_objective_bounds c C g p q K D alpha C3 φ
    hc hC hp hq hK hD hzero Z hZ hanchor G U hU hZU hG hthirdG
  have hxJ := source_feature_norms_le_radius c C g p q K D alpha φ
    hc hC hp hq hK hD hφ hgrowth x hx
  have hyJ := source_feature_norms_le_radius c C g p q K D alpha φ
    hc hC hp hq hK hD hφ hgrowth y hy
  exact source_moment_magnitude_bounds (fderiv ℝ (sourceWeightedFeatureMap c p φ))
    (gradient G) theta x y (fderiv ℝ (fderiv ℝ (sourceWeightedFeatureMap c p φ)) x)
    (momentObjectiveHessian G theta) (sourceObjectiveAnchorFactor c p C3 φ G)
    (sourceMomentRadius c C g p q K D alpha) hb.1
    (one_le_sourceMomentRadius c C g p q K D alpha hC hK.le (by linarith))
    hxJ.2.1 hyJ.2.1 hxJ.2.2 (hb.2 theta htheta).1 (hb.2 theta htheta).2

/-- Actual moment-argument differences have coefficients L, L/2 and L/2.
The distance is the Hilbert norm of the two encoded moment vectors. -/
theorem source_local_field_measure_bounds
    (theta theta' : lp H 2) (htheta : theta ∈ convexHull ℝ Z)
    (htheta' : theta' ∈ convexHull ℝ Z)
    (x y : E) (hx : ‖x‖ ≤ D) (hy : ‖y‖ ≤ D) :
    let J := sourceWeightedFeatureMap c p φ
    let L := sourceComparisonEnvelope c C g p q K D alpha C3 φ G
    ‖momentGradientField (fderiv ℝ J) (gradient G) (theta, x) -
      momentGradientField (fderiv ℝ J) (gradient G) (theta', x)‖ ≤ L * ‖theta - theta'‖ ∧
    ‖momentSpatialHessian (fderiv ℝ (fderiv ℝ J) x) (gradient G theta) -
      momentSpatialHessian (fderiv ℝ (fderiv ℝ J) x) (gradient G theta')‖ ≤
        (L / 2) * ‖theta - theta'‖ ∧
    ‖momentIntegralHessian (fderiv ℝ J x) (fderiv ℝ J y) (momentObjectiveHessian G theta) -
      momentIntegralHessian (fderiv ℝ J x) (fderiv ℝ J y) (momentObjectiveHessian G theta')‖ ≤
        (L / 2) * ‖theta - theta'‖ := by
  have hzero : ∀ n, ‖φ n 0‖ ≤ featureGrowth C g q n := by
    intro n
    simpa only [norm_iteratedFDeriv_zero, Nat.sub_zero, norm_zero,
      zero_pow (Nat.succ_ne_zero n), add_zero, mul_one] using hgrowth n 0 0 (by omega)
  have hb := source_region_objective_bounds c C g p q K D alpha C3 φ
    hc hC hp hq hK hD hzero Z hZ hanchor G U hU hZU hG hthirdG
  have hxJ := source_feature_norms_le_radius c C g p q K D alpha φ
    hc hC hp hq hK hD hφ hgrowth x hx
  have hyJ := source_feature_norms_le_radius c C g p q K D alpha φ
    hc hC hp hq hK hD hφ hgrowth y hy
  exact source_moment_measure_bounds (fderiv ℝ (sourceWeightedFeatureMap c p φ))
    (gradient G) theta theta' x y (fderiv ℝ (fderiv ℝ (sourceWeightedFeatureMap c p φ)) x)
    (momentObjectiveHessian G theta) (momentObjectiveHessian G theta')
    (sourceObjectiveAnchorFactor c p C3 φ G) (sourceMomentRadius c C g p q K D alpha)
    ‖theta - theta'‖ hb.1
    (one_le_sourceMomentRadius c C g p q K D alpha hC hK.le (by linarith))
    hxJ.2.1 hyJ.2.1 hxJ.2.2 le_rfl
    (source_region_gradient_sub_le c C g p q K D alpha C3 φ
      hc hC hp hq hK hD hzero Z hZ hanchor G U hU hZU hG hthirdG theta theta' htheta htheta')
    (source_region_momentObjectiveHessian_sub_le c p C3 φ Z G U
      hU hZU hG hthirdG theta theta' htheta htheta')

/-- Actual spatial differences have the source coefficient L, preserving
the sum of distances in the two distinct kernel slots. Only the spatial
Hessian estimate uses the existing third feature derivative and its growth. -/
theorem source_local_field_spatial_bounds
    (hthirdφ : ∀ n z, DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ (φ n))) z)
    (hgrowth₃ : ∀ n z, ‖iteratedFDeriv ℝ 3 (φ n) z‖ ≤
      featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1 - 3)))
    (theta : lp H 2) (htheta : theta ∈ convexHull ℝ Z)
    (x x' y y' : E) (hx : ‖x‖ ≤ D) (hx' : ‖x'‖ ≤ D)
    (hy : ‖y‖ ≤ D) (hy' : ‖y'‖ ≤ D) :
    let J := sourceWeightedFeatureMap c p φ
    let L := sourceComparisonEnvelope c C g p q K D alpha C3 φ G
    ‖momentGradientField (fderiv ℝ J) (gradient G) (theta, x) -
      momentGradientField (fderiv ℝ J) (gradient G) (theta, x')‖ ≤ L * ‖x - x'‖ ∧
    ‖momentSpatialHessian (fderiv ℝ (fderiv ℝ J) x) (gradient G theta) -
      momentSpatialHessian (fderiv ℝ (fderiv ℝ J) x') (gradient G theta)‖ ≤ L * ‖x - x'‖ ∧
    ‖momentIntegralHessian (fderiv ℝ J x) (fderiv ℝ J y) (momentObjectiveHessian G theta) -
      momentIntegralHessian (fderiv ℝ J x') (fderiv ℝ J y') (momentObjectiveHessian G theta)‖ ≤
        L * (‖x - x'‖ + ‖y - y'‖) := by
  have hzero : ∀ n, ‖φ n 0‖ ≤ featureGrowth C g q n := by
    intro n
    simpa only [norm_iteratedFDeriv_zero, Nat.sub_zero, norm_zero,
      zero_pow (Nat.succ_ne_zero n), add_zero, mul_one] using hgrowth n 0 0 (by omega)
  have hb := source_region_objective_bounds c C g p q K D alpha C3 φ
    hc hC hp hq hK hD hzero Z hZ hanchor G U hU hZU hG hthirdG
  have hxJ := source_feature_norms_le_radius c C g p q K D alpha φ
    hc hC hp hq hK hD hφ hgrowth x' hx'
  have hyJ := source_feature_norms_le_radius c C g p q K D alpha φ
    hc hC hp hq hK hD hφ hgrowth y hy
  exact source_moment_spatial_bounds (fderiv ℝ (sourceWeightedFeatureMap c p φ))
    (gradient G) theta x x' y y'
    (fderiv ℝ (fderiv ℝ (sourceWeightedFeatureMap c p φ)) x)
    (fderiv ℝ (fderiv ℝ (sourceWeightedFeatureMap c p φ)) x')
    (momentObjectiveHessian G theta) (sourceObjectiveAnchorFactor c p C3 φ G)
    (sourceMomentRadius c C g p q K D alpha) hb.1
    (one_le_sourceMomentRadius c C g p q K D alpha hC hK.le (by linarith))
    hxJ.2.1 hyJ.2.1
    (source_feature_fderiv_sub_le_radius c C g p q K D alpha φ
      hc hC hp hq hK hD hφ hgrowth x x' hx hx')
    (source_feature_fderiv_sub_le_radius c C g p q K D alpha φ
      hc hC hp hq hK hD hφ hgrowth y y' hy hy')
    (source_feature_second_fderiv_sub_le_radius c C g p q K D alpha φ
      hc hC hp hq hK hD hφ hgrowth hthirdφ hgrowth₃ x x' hx hx')
    (hb.2 theta htheta).1 (hb.2 theta htheta).2

end PaperFormalization.Manuscript
