import PaperFormalization.Manuscript.PopulationTail
import PaperFormalization.Manuscript.WeightedClippedSampleMean

/-! # Countable population bias and actual sample unclipping -/
open MeasureTheory Set
open scoped BigOperators NNReal
namespace PaperFormalization.Manuscript
section Generic
variable {E : Type*} {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, NormedSpace ℝ (H n)] {N : ℕ}

/-- A genuine summable change of population centers controls the literal
countable sample residual and proves its convergence. -/
theorem weightedSampleResidual_change_center_le
    (w : ℕ → ℝ≥0) (φ : ∀ n, E → H n) (P Q : ∀ n, H n) (X : Fin N → E)
    (hQ : Summable (fun n => (w n : ℝ) * ‖(N : ℝ)⁻¹ • ∑ i, φ n (X i) - Q n‖))
    (hB : Summable (fun n => (w n : ℝ) * ‖P n - Q n‖)) :
    Summable (fun n => (w n : ℝ) * ‖(N : ℝ)⁻¹ • ∑ i, φ n (X i) - P n‖) ∧
    weightedSampleResidual w φ P X ≤ weightedSampleResidual w φ Q X +
      ∑' n, (w n : ℝ) * ‖P n - Q n‖ := by
  have hb (n : ℕ) : (w n : ℝ) * ‖(N : ℝ)⁻¹ • ∑ i, φ n (X i) - P n‖ ≤
      (w n : ℝ) * ‖(N : ℝ)⁻¹ • ∑ i, φ n (X i) - Q n‖ + (w n : ℝ) * ‖P n - Q n‖ := by
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ (w n).coe_nonneg
    simpa only [norm_sub_rev (Q n) (P n)] using
      norm_sub_le_norm_sub_add_norm_sub ((N : ℝ)⁻¹ • ∑ i, φ n (X i)) (Q n) (P n)
  have hs := (hQ.add hB).of_nonneg_of_le
    (fun n => mul_nonneg (w n).coe_nonneg (norm_nonneg _)) hb
  refine ⟨hs, ?_⟩
  exact (hs.tsum_le_tsum hb (hQ.add hB)).trans_eq (hQ.tsum_add hB)
end Generic

section Source
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)]

/-- Summing actual coordinate clipping errors gives the exact weighted source
bias under the unchanged population law, with convergence proved first. -/
theorem source_weighted_clipping_bias_le
    (C g q alpha K D : ℝ) (hC : 0 ≤ C) (hK : 0 < K) (hD : 0 ≤ D)
    (μ : Measure E) (hμ : μ ∈ sourceMomentClass alpha K) (w : ℕ → ℝ≥0)
    (φ : ∀ n, E → H n) (hc : ∀ n, Continuous (φ n))
    (hg : ∀ n x, ‖φ n x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1)))
    (hS : Summable (fun n => (w n : ℝ) * sourceCoordinateL2Envelope C g q alpha K n)) :
    Summable (fun n => (w n : ℝ) *
      ‖(∫ x, φ n x ∂μ) - ∫ x, φ n (sourceRadialClip D x) ∂μ‖) ∧
    (∑' n, (w n : ℝ) * ‖(∫ x, φ n x ∂μ) - ∫ x, φ n (sourceRadialClip D x) ∂μ‖) ≤
      2 * (∑' n, (w n : ℝ) * sourceCoordinateL2Envelope C g q alpha K n) *
        Real.sqrt (μ.real {x | D < ‖x‖}) := by
  let r := Real.sqrt (μ.real {x | D < ‖x‖})
  have hb (n : ℕ) : (w n : ℝ) * ‖(∫ x, φ n x ∂μ) - ∫ x, φ n (sourceRadialClip D x) ∂μ‖ ≤
      (2 * r) * ((w n : ℝ) * sourceCoordinateL2Envelope C g q alpha K n) := by
    have h := mul_le_mul_of_nonneg_left
      (source_coordinate_clipping_bias_le C g q alpha K D hC hK hD μ hμ n (φ n) (hc n) (hg n))
      (w n).coe_nonneg
    exact h.trans_eq (by dsimp [r]; ring)
  have hsum := hS.mul_left (2 * r)
  have hs := hsum.of_nonneg_of_le (fun n => mul_nonneg (w n).coe_nonneg (norm_nonneg _)) hb
  refine ⟨hs, (hs.tsum_le_tsum hb hsum).trans_eq ?_⟩
  rw [tsum_mul_left]
  dsimp [r]
  ring

/-- On the actual sample-ball event, only the empirical feature is unclipped;
the original population discrepancy is bounded by the clipped statistic plus
the exact unchanged-law bias. -/
theorem source_weighted_unclipping_le {N : ℕ} (hN : 0 < N)
    (C g q alpha K D : ℝ) (hC : 0 ≤ C) (hK : 0 < K) (hD : 0 ≤ D)
    (μ : Measure E) (hμ : μ ∈ sourceMomentClass alpha K) (w : ℕ → ℝ≥0)
    (φ : ∀ n, E → H n) (hc : ∀ n, Continuous (φ n))
    (hg : ∀ n x, ‖φ n x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1)))
    (hA : Summable (fun n => (w n : ℝ) * (featureGrowth C g q n * (1 + D ^ (n+1)))))
    (hS : Summable (fun n => (w n : ℝ) * sourceCoordinateL2Envelope C g q alpha K n))
    (X : Fin N → E) (hX : ∀ i, ‖X i‖ ≤ D) :
    weightedSampleResidual w φ (fun n => ∫ x, φ n x ∂μ) X ≤
      weightedClippedSampleResidual μ D w φ X +
      2 * (∑' n, (w n : ℝ) * sourceCoordinateL2Envelope C g q alpha K n) *
        Real.sqrt (μ.real {x | D < ‖x‖}) := by
  letI : IsProbabilityMeasure μ := hμ.1
  let f : ∀ n, E → H n := fun n x => φ n (sourceRadialClip D x)
  let P : ∀ n, H n := fun n => ∫ x, φ n x ∂μ
  let Q : ∀ n, H n := fun n => ∫ x, f n x ∂μ
  have hL (n : ℕ) : 0 ≤ featureGrowth C g q n := by unfold featureGrowth; positivity
  have hQ := weightedSampleResidual_summable hN w f Q
    (fun n => featureGrowth C g q n * (1 + D ^ (n+1))) hA
    (fun n => norm_clipped_feature_le D _ (n+1) hD (hL n) (φ n) (hg n))
    (fun n => (clipped_populationFeature_integrable_and_norm_le μ D hD
      (featureGrowth C g q) (fun n => n+1) hL φ hc hg n).2) X
  have hB := source_weighted_clipping_bias_le C g q alpha K D hC hK hD μ hμ w φ hc hg hS
  have hb := (weightedSampleResidual_change_center_le w f P Q X hQ hB.1).2
  have he : weightedSampleResidual w φ P X = weightedSampleResidual w f P X := by
    unfold weightedSampleResidual
    congr 1
    funext n
    dsimp [f]
    simp only [sourceRadialClip_of_norm_le D _ (hX _)]
  rw [he]
  exact hb.trans (add_le_add le_rfl hB.2)
end Source
end PaperFormalization.Manuscript
