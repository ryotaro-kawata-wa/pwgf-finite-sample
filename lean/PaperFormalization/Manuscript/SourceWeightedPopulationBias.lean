import PaperFormalization.Manuscript.WeightedClippingBias
import PaperFormalization.Manuscript.SourceMomentTail

/-! # Literal weighted source bias after actual sample unclipping -/
open MeasureTheory Set
open scoped BigOperators NNReal
namespace PaperFormalization.Manuscript
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)]

/-- The full original source residual is bounded by the actual clipped
statistic plus the literal exponential population bias on the sample event. -/
theorem source_weighted_unclipping_exp_le {N : ℕ} (hN : 0 < N)
    (C g q alpha K D c K₀ M : ℝ) (hC : 0 ≤ C) (hK : 0 < K) (hD : 0 ≤ D)
    (hc : 0 ≤ c) (hK₀ : 0 < K₀) (halpha : 0 ≤ alpha)
    (μ : Measure E) (hμ : μ ∈ sourceMomentClass alpha K)
    (hexp : Integrable (fun x => Real.exp (c * (‖x‖ / K₀) ^ alpha)) μ)
    (hM : (∫ x, Real.exp (c * (‖x‖ / K₀) ^ alpha) ∂μ) ≤ M)
    (w : ℕ → ℝ≥0) (φ : ∀ n, E → H n) (hφ : ∀ n, Continuous (φ n))
    (hg : ∀ n x, ‖φ n x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n+1)))
    (hA : Summable (fun n => (w n : ℝ) * (featureGrowth C g q n * (1 + D ^ (n+1)))))
    (hS : Summable (fun n => (w n : ℝ) * sourceCoordinateL2Envelope C g q alpha K n))
    (X : Fin N → E) (hX : ∀ i, ‖X i‖ ≤ D) :
    weightedSampleResidual w φ (fun n => ∫ x, φ n x ∂μ) X ≤
      weightedClippedSampleResidual μ D w φ X +
      2 * (∑' n, (w n : ℝ) * sourceCoordinateL2Envelope C g q alpha K n) *
        Real.sqrt M * Real.exp (-(c * (D/K₀)^alpha)/2) := by
  letI : IsProbabilityMeasure μ := hμ.1
  have hb := source_weighted_unclipping_le hN C g q alpha K D hC hK hD μ hμ w φ hφ hg hA hS X hX
  have ht := measureReal_norm_tail_le_exp_moment μ c K₀ alpha D M hc hK₀ halpha hD hexp hM
  have hM0 : 0 ≤ M := (integral_nonneg (fun x => (Real.exp_pos (c * (‖x‖/K₀)^alpha)).le)).trans hM
  have hs := sqrt_le_sqrt_mul_exp_half _ M _ hM0 ht
  have hS0 : 0 ≤ 2 * ∑' n, (w n : ℝ) * sourceCoordinateL2Envelope C g q alpha K n := by
    apply mul_nonneg (by norm_num)
    apply tsum_nonneg
    intro n
    unfold sourceCoordinateL2Envelope featureGrowth
    positivity
  exact hb.trans (add_le_add le_rfl ((mul_le_mul_of_nonneg_left hs hS0).trans_eq (by ring)))

/-- The moment-only source alternative retains the exact same weighted
residual and K, and needs no exponential-moment assumption. -/
theorem source_weighted_unclipping_moment_le {N : ℕ} (hN : 0 < N)
    (C g q alpha K D : ℝ) (hC : 0 ≤ C) (hK : 0 < K) (halpha : 0 < alpha)
    (hD : Real.exp 1 * K ≤ D) (μ : Measure E) (hμ : μ ∈ sourceMomentClass alpha K)
    (w : ℕ → ℝ≥0) (φ : ∀ n, E → H n) (hφ : ∀ n, Continuous (φ n))
    (hg : ∀ n x, ‖φ n x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n+1)))
    (hA : Summable (fun n => (w n : ℝ) * (featureGrowth C g q n * (1 + D ^ (n+1)))))
    (hS : Summable (fun n => (w n : ℝ) * sourceCoordinateL2Envelope C g q alpha K n))
    (X : Fin N → E) (hX : ∀ i, ‖X i‖ ≤ D) :
    weightedSampleResidual w φ (fun n => ∫ x, φ n x ∂μ) X ≤
      weightedClippedSampleResidual μ D w φ X +
      2 * (∑' n, (w n : ℝ) * sourceCoordinateL2Envelope C g q alpha K n) *
        Real.exp (-((D/(Real.exp 1 * K))^alpha)/2) := by
  letI : IsProbabilityMeasure μ := hμ.1
  have hD0 : 0 ≤ D := (mul_nonneg (Real.exp_pos 1).le hK.le).trans hD
  have hb := source_weighted_unclipping_le hN C g q alpha K D hC hK hD0 μ hμ w φ hφ hg hA hS X hX
  have ht := sourceMomentClass_norm_tail_exp_le alpha K D halpha hK hD μ hμ
  have hs := sqrt_le_sqrt_mul_exp_half (μ.real {x | D < ‖x‖}) 1
    ((D/(Real.exp 1*K))^alpha) (by norm_num) (by simpa only [one_mul] using ht)
  simp only [Real.sqrt_one, one_mul] at hs
  have hS0 : 0 ≤ 2 * ∑' n, (w n : ℝ) * sourceCoordinateL2Envelope C g q alpha K n := by
    apply mul_nonneg (by norm_num)
    apply tsum_nonneg
    intro n
    unfold sourceCoordinateL2Envelope featureGrowth
    positivity
  exact hb.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hs hS0))
end PaperFormalization.Manuscript
