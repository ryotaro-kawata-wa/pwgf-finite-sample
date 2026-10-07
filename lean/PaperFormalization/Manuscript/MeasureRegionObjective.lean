import PaperFormalization.Manuscript.MeasureMomentRegion
import PaperFormalization.Manuscript.SourceRegionObjective

/-! # Source objective estimates on the actual measure moment region

The supplied population class P is kept unchanged. Genuine moment hypotheses
on its members and bounded support on the other class derive the concrete
radius. The original open G-domain contains precisely that region, not an
enlarged class of measures. No uniform lower derivative bound is assumed.
-/

open MeasureTheory Set

namespace PaperFormalization.Manuscript

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
  [BorelSpace E] [SecondCountableTopology E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]
variable (c C g p q K D alpha C3 : ℝ) (φ : ∀ n, E → H n) (P : Set (Measure E))
  (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (hD : 1 ≤ D)
  (hφ : ∀ n, Continuous (φ n))
  (hPprob : ∀ μ ∈ P, IsProbabilityMeasure μ)
  (hPmoment : ∀ μ ∈ P, ∀ n, Integrable (fun x : E => ‖x‖ ^ (n + 1)) μ)
  (hPmean : ∀ μ ∈ P, ∀ n, (∫ x : E, ‖x‖ ^ (n + 1) ∂μ) ≤
    K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha))
  (hgrowth : ∀ n x, ‖φ n x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1)))
  (G : lp H 2 → ℝ) (U : Set (lp H 2))
  (hU : IsOpen U) (hSU : measureMomentRegion (sourceWeightedFeatureMap c p φ) P D ⊆ U)
  (hG : ContDiffOn ℝ 3 G U)
  (hthird : ∀ theta ∈ measureMomentRegion (sourceWeightedFeatureMap c p φ) P D,
    ‖iteratedFDeriv ℝ 3 G theta‖ ≤ C3)

include hc hC hp hq hK hD hφ hPprob hPmoment hPmean hgrowth hU hSU hG hthird

/-- The actual measure-generated finite convex hull supplies the exact source
objective bounds and Q>=1 from its derived anchor radius. -/
theorem source_measure_region_objective_bounds :
    1 ≤ sourceObjectiveAnchorFactor c p C3 φ G ∧
      ∀ theta ∈ measureMomentRegion (sourceWeightedFeatureMap c p φ) P D,
        ‖gradient G theta‖ ≤ sourceObjectiveAnchorFactor c p C3 φ G *
          (sourceMomentRadius c C g p q K D alpha) ^ 2 ∧
        ‖momentObjectiveHessian G theta‖ ≤ sourceObjectiveAnchorFactor c p C3 φ G *
          sourceMomentRadius c C g p q K D alpha := by
  apply source_momentObjective_bounds_from_anchor G
    (measureMomentRegion (sourceWeightedFeatureMap c p φ) P D) U
    (convex_measureMomentRegion _ _ _) hSU hU hG C3 hthird
    (sourceWeightedFeatureMap c p φ 0)
    (zero_anchor_mem_measureMomentRegion _ _ _ (by linarith))
    (sourceObjectiveAnchorFactor c p C3 φ G) (sourceMomentRadius c C g p q K D alpha)
    (one_le_sourceMomentRadius c C g p q K D alpha hC hK.le (by linarith)) rfl
  intro theta htheta
  have hr := source_measureMomentRegion_anchor_radius c C g p q K D alpha φ P
    hc hC hp hq hK hD hφ hPprob hPmoment hPmean hgrowth theta htheta
  exact hr.1.trans hr.2

/-- Actual gradient and Hessian differences on the same measure-generated
region retain QR and Q, without assuming those difference bounds. -/
theorem source_measure_region_objective_differences
    (theta theta' : lp H 2)
    (htheta : theta ∈ measureMomentRegion (sourceWeightedFeatureMap c p φ) P D)
    (htheta' : theta' ∈ measureMomentRegion (sourceWeightedFeatureMap c p φ) P D) :
    ‖gradient G theta - gradient G theta'‖ ≤
      sourceObjectiveAnchorFactor c p C3 φ G * sourceMomentRadius c C g p q K D alpha *
        ‖theta - theta'‖ ∧
    ‖momentObjectiveHessian G theta - momentObjectiveHessian G theta'‖ ≤
      sourceObjectiveAnchorFactor c p C3 φ G * ‖theta - theta'‖ := by
  constructor
  · apply gradient_sub_le_of_momentObjectiveHessian_bound G
      (measureMomentRegion (sourceWeightedFeatureMap c p φ) P D) U
      (convex_measureMomentRegion _ _ _) hSU hU (hG.of_le (by norm_num)) _ ?_
      theta theta' htheta htheta'
    intro z hz
    exact (source_measure_region_objective_bounds c C g p q K D alpha C3 φ P
      hc hC hp hq hK hD hφ hPprob hPmoment hPmean hgrowth G U hU hSU hG hthird).2 z hz |>.2
  · exact (momentObjectiveHessian_sub_le_of_third_bound G
      (measureMomentRegion (sourceWeightedFeatureMap c p φ) P D) U
      (convex_measureMomentRegion _ _ _) hSU hU hG C3 hthird theta theta' htheta htheta').trans
      (mul_le_mul_of_nonneg_right (third_bound_le_sourceObjectiveAnchorFactor c p C3 φ G)
        (norm_nonneg _))

/-- Scalar objective differences follow from the derived gradient bound on
the actual feasible segment, with the explicit coefficient QR². -/
theorem source_measure_region_objective_value_sub_le
    (theta theta' : lp H 2)
    (htheta : theta ∈ measureMomentRegion (sourceWeightedFeatureMap c p φ) P D)
    (htheta' : theta' ∈ measureMomentRegion (sourceWeightedFeatureMap c p φ) P D) :
    ‖G theta - G theta'‖ ≤
      sourceObjectiveAnchorFactor c p C3 φ G * (sourceMomentRadius c C g p q K D alpha) ^ 2 *
        ‖theta - theta'‖ := by
  apply (convex_measureMomentRegion (sourceWeightedFeatureMap c p φ) P D).norm_image_sub_le_of_norm_fderiv_le
    (𝕜 := ℝ) (f := G) ?_ ?_ htheta' htheta
  · intro z hz
    exact (hG.contDiffAt (hU.mem_nhds (hSU hz))).differentiableAt (by norm_num)
  · intro z hz
    have hb := (source_measure_region_objective_bounds c C g p q K D alpha C3 φ P
      hc hC hp hq hK hD hφ hPprob hPmoment hPmean hgrowth G U hU hSU hG hthird).2 z hz |>.1
    have hn : ‖gradient G z‖ = ‖fderiv ℝ G z‖ :=
      (InnerProductSpace.toDual ℝ (lp H 2)).symm.norm_map _
    rwa [← hn]

end PaperFormalization.Manuscript
