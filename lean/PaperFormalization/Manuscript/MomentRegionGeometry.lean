import PaperFormalization.Manuscript.WeightedFeatureDerivatives
import Mathlib.Analysis.Convex.Hull

/-! # The exact source moment radius and finite-convex-hull geometry

The radius is the literal source series, with m=n+1. Generator coordinates
are actual scaled lp2 coordinates. A generator may obey either source
coordinate amplitude envelope. The norm estimate is extended to the ordinary
convexHull (finite convex combinations), without replacing it by a closure.
Identification of a generator with a particular measure class remains separate.
-/

open Set
open scoped BigOperators

namespace PaperFormalization.Manuscript

/-- The exact source radius, retaining every localization and moment factor. -/
noncomputable def sourceMomentRadius (c C g p q K D alpha : ℝ) : ℝ :=
  1 + ∑' n, featureWeight c C g p q n *
    (2 + D ^ (n + 1) + K ^ (n + 1) *
      ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha))

/-- The literal radius series converges under the original decay separation. -/
theorem summable_sourceMomentRadius_summand (c C g p q K D alpha : ℝ)
    (hc : 0 < c) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (hD : 1 ≤ D) :
    Summable (fun n : ℕ => featureWeight c C g p q n *
      (2 + D ^ (n + 1) + K ^ (n + 1) *
        ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha))) :=
  summable_feature_amplitude c C g p q K D alpha hc hp hq hK (by linarith)

/-- Source positivity implies R>=1; no bound independent of K,D is asserted. -/
theorem one_le_sourceMomentRadius (c C g p q K D alpha : ℝ)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hD : 0 ≤ D) :
    1 ≤ sourceMomentRadius c C g p q K D alpha := by
  unfold sourceMomentRadius
  have hsum : 0 ≤ ∑' n, featureWeight c C g p q n *
      (2 + D ^ (n + 1) + K ^ (n + 1) *
        ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha)) := by
    apply tsum_nonneg
    intro n
    exact mul_nonneg (featureWeight_nonneg c C g p q hC n) (by positivity)
  linarith

/-- The common feature derivative envelope is at most R-1, hence at most R. -/
theorem source_feature_envelope_le_radius (c C g p q K D alpha : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (hD : 1 ≤ D) :
    (∑' n, featureWeight c C g p q n * (1 + D ^ (n + 1))) ≤
        sourceMomentRadius c C g p q K D alpha - 1 ∧
    sourceMomentRadius c C g p q K D alpha - 1 ≤ sourceMomentRadius c C g p q K D alpha := by
  constructor
  · unfold sourceMomentRadius
    rw [add_sub_cancel_left]
    apply Summable.tsum_le_tsum _
      (summable_feature_regularity_envelope c C g p q D hc hp hq hD)
      (summable_sourceMomentRadius_summand c C g p q K D alpha hc hp hq hK hD)
    intro n
    apply mul_le_mul_of_nonneg_left _ (featureWeight_nonneg c C g p q hC n)
    have hh : 0 ≤ K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha) := by positivity
    linarith
  · linarith

/-- A generator norm bound extends to the ordinary finite convex hull. -/
theorem norm_sub_le_on_convexHull {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Z : Set V) (anchor : V) (R : ℝ) (hZ : ∀ z ∈ Z, ‖z - anchor‖ ≤ R)
    (theta : V) (htheta : theta ∈ convexHull ℝ Z) : ‖theta - anchor‖ ≤ R := by
  have hz : Z ⊆ Metric.closedBall anchor R := by
    intro z hz
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hZ z hz
  have ht := convexHull_min hz (convex_closedBall anchor R) htheta
  simpa only [Metric.mem_closedBall, dist_eq_norm] using ht

/-- Every affine segment between feasible convex-hull points remains feasible. -/
theorem affine_segment_mem_convexHull {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Z : Set V) (theta theta' : V) (htheta : theta ∈ convexHull ℝ Z)
    (htheta' : theta' ∈ convexHull ℝ Z) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    theta + s • (theta' - theta) ∈ convexHull ℝ Z :=
  (convex_convexHull ℝ Z).add_smul_sub_mem htheta htheta' hs

variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)]

omit [∀ n, InnerProductSpace ℝ (H n)] in
/-- Each source encoded generator is at distance at most R-1 from an encoded
anchor with coordinate norms bounded by a_m L_m. The either/or coordinate
premise is weaker than requiring the entire generator to come from one class. -/
theorem encoded_moment_norm_sub_anchor_le_radius
    (c C g p q K D alpha : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (hD : 1 ≤ D)
    (z anchor : lp H 2)
    (hanchor : ∀ n, ‖anchor n‖ ≤ featureWeight c C g p q n)
    (hz : ∀ n, ‖z n‖ ≤ featureWeight c C g p q n * (1 + D ^ (n + 1)) ∨
      ‖z n‖ ≤ featureWeight c C g p q n *
        (1 + K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha))) :
    ‖z - anchor‖ ≤ sourceMomentRadius c C g p q K D alpha - 1 := by
  unfold sourceMomentRadius
  rw [add_sub_cancel_left]
  apply norm_hilbertSum_le_of_hasSum_coordinate_majorant _ _ _
    (summable_sourceMomentRadius_summand c C g p q K D alpha hc hp hq hK hD).hasSum
  intro n
  change ‖z n - anchor n‖ ≤ _
  have ht := (norm_sub_le (z n) (anchor n)).trans (add_le_add le_rfl (hanchor n))
  have hw := featureWeight_nonneg c C g p q hC n
  have hpop : 0 ≤ K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha) := by positivity
  have hdp : 0 ≤ D ^ (n + 1) := by positivity
  rcases hz n with h | h
  · nlinarith [mul_nonneg hw hpop]
  · nlinarith [mul_nonneg hw hdp]

/-- The exact source anchor radius on any finite convex hull of admissible
encoded generators; its defining series and all scale dependence are retained. -/
theorem convexHull_encoded_moments_anchor_radius
    (c C g p q K D alpha : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (hD : 1 ≤ D)
    (Z : Set (lp H 2)) (anchor : lp H 2)
    (hanchor : ∀ n, ‖anchor n‖ ≤ featureWeight c C g p q n)
    (hZ : ∀ z ∈ Z, ∀ n, ‖z n‖ ≤ featureWeight c C g p q n * (1 + D ^ (n + 1)) ∨
      ‖z n‖ ≤ featureWeight c C g p q n *
        (1 + K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha)))
    (theta : lp H 2) (htheta : theta ∈ convexHull ℝ Z) :
    ‖theta - anchor‖ ≤ sourceMomentRadius c C g p q K D alpha - 1 ∧
      sourceMomentRadius c C g p q K D alpha - 1 ≤ sourceMomentRadius c C g p q K D alpha := by
  constructor
  · exact norm_sub_le_on_convexHull Z anchor _
      (fun z hz => encoded_moment_norm_sub_anchor_le_radius c C g p q K D alpha
        hc hC hp hq hK hD z anchor hanchor (hZ z hz)) theta htheta
  · linarith

/-- The actual encoded source anchor J0(0) has coordinate norm at most a_m L_m.
Only the feature values at zero are required; differentiability plays no role. -/
theorem source_feature_anchor_coordinate_norm_le
    {E : Type*} [Zero E] [∀ n, CompleteSpace (H n)]
    (c C g p q : ℝ) (φ : ∀ n, E → H n)
    (hc : 0 < c) (hp : 1 < p) (hq : q < p)
    (hzero : ∀ n, ‖φ n 0‖ ≤ featureGrowth C g q n) (n : ℕ) :
    ‖sourceWeightedFeatureMap c p φ 0 n‖ ≤ featureWeight c C g p q n := by
  have hb : ∀ i, sourceFeatureScale c p i * ‖φ i 0‖ ≤ featureWeight c C g p q i := by
    intro i
    exact mul_le_mul_of_nonneg_left (hzero i) (sourceFeatureScale_pos c p i).le
  have hs : Summable (fun i => sourceFeatureScale c p i * ‖φ i 0‖) :=
    Summable.of_nonneg_of_le
      (fun i => mul_nonneg (sourceFeatureScale_pos c p i).le (norm_nonneg _)) hb
      (summable_featureWeight c C g p q hc hp hq)
  change ‖weightedHilbertSum (sourceFeatureScale c p) (fun i => φ i 0) n‖ ≤ _
  rw [weightedHilbertSum_apply _ (fun i => (sourceFeatureScale_pos c p i).le) _ hs,
    norm_smul, Real.norm_eq_abs, abs_of_pos (sourceFeatureScale_pos c p n)]
  exact hb n

/-- The source-shaped finite convex hull has radius R-1 around the actual
encoded J0(0), not an abstract replacement anchor. Actual probability-measure
class membership is left to the generator construction. -/
theorem source_moment_convexHull_anchor_radius
    {E : Type*} [Zero E] [∀ n, CompleteSpace (H n)]
    (c C g p q K D alpha : ℝ) (φ : ∀ n, E → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (hD : 1 ≤ D)
    (hzero : ∀ n, ‖φ n 0‖ ≤ featureGrowth C g q n)
    (Z : Set (lp H 2))
    (hZ : ∀ z ∈ Z, ∀ n, ‖z n‖ ≤ featureWeight c C g p q n * (1 + D ^ (n + 1)) ∨
      ‖z n‖ ≤ featureWeight c C g p q n *
        (1 + K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha)))
    (theta : lp H 2) (htheta : theta ∈ convexHull ℝ Z) :
    ‖theta - sourceWeightedFeatureMap c p φ 0‖ ≤ sourceMomentRadius c C g p q K D alpha - 1 ∧
      sourceMomentRadius c C g p q K D alpha - 1 ≤ sourceMomentRadius c C g p q K D alpha := by
  exact convexHull_encoded_moments_anchor_radius c C g p q K D alpha hc hC hp hq hK hD Z
    (sourceWeightedFeatureMap c p φ 0)
    (source_feature_anchor_coordinate_norm_le c C g p q φ hc hp hq hzero) hZ theta htheta

end PaperFormalization.Manuscript
