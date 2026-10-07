import PaperFormalization.Manuscript.WeightedFeatureMap
import PaperFormalization.Manuscript.CoordinateMoments
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Actual Hilbert-valued feature moments under one fixed law

Summable weighted integrals of coordinate norms imply actual Bochner
integrability of the Hilbert-valued feature series. Its integral is the
weighted Hilbert sum of its coordinate integrals. All integrals use the same
supplied measure; no conditioning or change of probability law is asserted.
AE strong measurability is proved by an AE limit of finite sums, without any
separability assumption on the entire Hilbert target. Source moment bounds
below accompany genuine integrability of the corresponding powers.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace PaperFormalization.Manuscript

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Absolute summability of the integrals of norms makes the actual pointwise
Banach series Bochner integrable. AE convergence supplies strong measurability. -/
theorem integrable_series_of_summable_integral_norm {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure Ω) (f : ℕ → Ω → F) (hf : ∀ n, Integrable (f n) μ)
    (hs : Summable (fun n => ∫ ω, ‖f n ω‖ ∂μ)) :
    Integrable (fun ω => ∑' n, f n ω) μ := by
  have hmeas n : AEMeasurable (fun ω => ‖f n ω‖ₑ) μ := (hf n).1.enorm
  have hnormint n : (∫⁻ ω, ‖f n ω‖ₑ ∂μ) = ‖∫ ω, ‖f n ω‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hf n).norm, ENNReal.coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg (fun ω => norm_nonneg (f n ω)))]
    simp only [coe_nnnorm]
  have hfinite : (∑' n, ∫⁻ ω, ‖f n ω‖ₑ ∂μ) ≠ ⊤ := by
    rw [funext hnormint]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hs.abs)
  have hsumint : (∫⁻ ω, ∑' n, ‖f n ω‖ₑ ∂μ) ≠ ⊤ := by
    rw [lintegral_tsum hmeas]
    exact hfinite
  have hsumae : ∀ᵐ ω ∂μ, Summable (fun n => ‖f n ω‖) := by
    filter_upwards [ae_lt_top' (AEMeasurable.tsum hmeas) hsumint] with ω hω
    exact tsum_enorm_ne_top_iff_summable_norm.1 hω.ne
  refine ⟨aestronglyMeasurable_of_tendsto_ae atTop
    (fun N => (Finset.range N).aestronglyMeasurable_fun_sum (fun n _ => (hf n).1)) ?_, ?_⟩
  · filter_upwards [hsumae] with ω hω
    exact hω.of_norm.hasSum.tendsto_sum_nat
  · change (∫⁻ ω, ‖∑' n, f n ω‖ₑ ∂μ) < ⊤
    exact (lintegral_mono (fun ω => enorm_tsum_le_tsum_enorm)).trans_lt hsumint.lt_top

variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

omit [∀ n, CompleteSpace (H n)] in
/-- Integrating the norm of one weighted insertion gives exactly its weighted
coordinate norm integral. -/
theorem integral_norm_weightedCoordinateEmbedding (μ : Measure Ω)
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (f : ∀ n, Ω → H n) (n : ℕ) :
    (∫ ω, ‖weightedCoordinateEmbedding a n (f n ω)‖ ∂μ) =
      a n * ∫ ω, ‖f n ω‖ ∂μ := by
  simp only [norm_weightedCoordinateEmbedding_of_nonneg a n (ha n), integral_const_mul]

omit [∀ n, CompleteSpace (H n)] in
/-- Each coordinate's integrability transfers through its bounded insertion. -/
theorem integrable_weightedCoordinateEmbedding (μ : Measure Ω)
    (a : ℕ → ℝ) (f : ∀ n, Ω → H n) (hf : ∀ n, Integrable (f n) μ) (n : ℕ) :
    Integrable (fun ω => weightedCoordinateEmbedding a n (f n ω)) μ :=
  (weightedCoordinateEmbedding a n).integrable_comp (hf n)

/-- Weighted coordinate L1 summability proves genuine integrability of the
actual Hilbert-sum-valued function. -/
theorem integrable_weightedHilbertSum (μ : Measure Ω)
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (f : ∀ n, Ω → H n)
    (hf : ∀ n, Integrable (f n) μ)
    (hs : Summable (fun n => a n * ∫ ω, ‖f n ω‖ ∂μ)) :
    Integrable (fun ω => weightedHilbertSum a (fun n => f n ω)) μ := by
  apply integrable_series_of_summable_integral_norm μ
    (fun n ω => weightedCoordinateEmbedding a n (f n ω))
    (integrable_weightedCoordinateEmbedding μ a f hf)
  simpa only [integral_norm_weightedCoordinateEmbedding μ a ha f] using hs

/-- Actual Hilbert integration commutes with the convergent weighted
coordinate series, under one and the same supplied measure. -/
theorem integral_weightedHilbertSum (μ : Measure Ω)
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (f : ∀ n, Ω → H n)
    (hf : ∀ n, Integrable (f n) μ)
    (hs : Summable (fun n => a n * ∫ ω, ‖f n ω‖ ∂μ)) :
    (∫ ω, weightedHilbertSum a (fun n => f n ω) ∂μ) =
      weightedHilbertSum a (fun n => ∫ ω, f n ω ∂μ) := by
  have hsum : Summable (fun n => ∫ ω, ‖weightedCoordinateEmbedding a n (f n ω)‖ ∂μ) := by
    simpa only [integral_norm_weightedCoordinateEmbedding μ a ha f] using hs
  change (∫ ω, ∑' n, weightedCoordinateEmbedding a n (f n ω) ∂μ) = _
  rw [← integral_tsum_of_summable_integral_norm
    (integrable_weightedCoordinateEmbedding μ a f hf) hsum]
  congr 1
  funext n
  exact (weightedCoordinateEmbedding a n).integral_comp_comm (hf n)

omit [∀ n, CompleteSpace (H n)] in
/-- The encoded coordinate integral is bounded by the exact weighted
integrals of coordinate norms. -/
theorem norm_weightedCoordinateIntegral_le (μ : Measure Ω)
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (f : ∀ n, Ω → H n)
    (hs : Summable (fun n => a n * ∫ ω, ‖f n ω‖ ∂μ)) :
    ‖weightedHilbertSum a (fun n => ∫ ω, f n ω ∂μ)‖ ≤
      ∑' n, a n * ∫ ω, ‖f n ω‖ ∂μ := by
  apply tsum_of_norm_bounded
    (f := fun n => weightedCoordinateEmbedding a n (∫ ω, f n ω ∂μ)) hs.hasSum
  intro n
  rw [norm_weightedCoordinateEmbedding_of_nonneg a n (ha n)]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (ha n)

/-- The actual integral has the same bound; its integrability is established
separately above, rather than inferred from a totalized integral inequality. -/
theorem norm_integral_weightedHilbertSum_le (μ : Measure Ω)
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (f : ∀ n, Ω → H n)
    (hf : ∀ n, Integrable (f n) μ)
    (hs : Summable (fun n => a n * ∫ ω, ‖f n ω‖ ∂μ)) :
    ‖∫ ω, weightedHilbertSum a (fun n => f n ω) ∂μ‖ ≤
      ∑' n, a n * ∫ ω, ‖f n ω‖ ∂μ := by
  rw [integral_weightedHilbertSum μ a ha f hf hs]
  exact norm_weightedCoordinateIntegral_le μ a ha f hs

/-- Decoding the actual Hilbert integral recovers the integral of its source
coordinate whenever the corresponding weight is nonzero. -/
theorem weightedCoordinateProjection_integral (μ : Measure Ω)
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (f : ∀ n, Ω → H n)
    (hf : ∀ n, Integrable (f n) μ)
    (hs : Summable (fun n => a n * ∫ ω, ‖f n ω‖ ∂μ)) (i : ℕ) (hi : a i ≠ 0) :
    weightedCoordinateProjection a i (∫ ω, weightedHilbertSum a (fun n => f n ω) ∂μ) =
      ∫ ω, f i ω ∂μ := by
  rw [integral_weightedHilbertSum μ a ha f hf hs]
  apply weightedCoordinateProjection_weightedHilbertSum a ha _ ?_ i hi
  exact Summable.of_nonneg_of_le
    (fun n => mul_nonneg (ha n) (norm_nonneg _))
    (fun n => mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (ha n)) hs


section FeatureGrowth

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- Genuine integrability and the source growth inequality bound the integral
of the coordinate norm, not merely the norm of a totalized coordinate integral. -/
theorem integral_norm_coordinate_feature_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → E) (φ : E → F) (m : ℕ) (L M : ℝ) (hL : 0 ≤ L)
    (hφX : Integrable (fun ω => φ (X ω)) μ)
    (hmoment : Integrable (fun ω => ‖X ω‖ ^ m) μ)
    (hmean : (∫ ω, ‖X ω‖ ^ m ∂μ) ≤ M)
    (hgrowth : ∀ x, ‖φ x‖ ≤ L * (1 + ‖x‖ ^ m)) :
    (∫ ω, ‖φ (X ω)‖ ∂μ) ≤ L * (1 + M) := by
  calc
    (∫ ω, ‖φ (X ω)‖ ∂μ) ≤ ∫ ω, L * (1 + ‖X ω‖ ^ m) ∂μ :=
      integral_mono hφX.norm (((integrable_const (1 : ℝ)).add hmoment).const_mul L)
        (fun ω => hgrowth (X ω))
    _ = L * (1 + ∫ ω, ‖X ω‖ ^ m ∂μ) := by
      rw [integral_const_mul, integral_add (integrable_const (1 : ℝ)) hmoment]
      simp
    _ ≤ L * (1 + M) := mul_le_mul_of_nonneg_left (add_le_add le_rfl hmean) hL

end FeatureGrowth

/-- The exact source population moment envelope is summable at each fixed scale. -/
theorem summable_sourceMomentEnvelope (c C g p q K alpha : ℝ)
    (hc : 0 < c) (hp : 1 < p) (hq : q < p) (hK : 0 < K) :
    Summable (fun n => featureWeight c C g p q n *
      (1 + K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha))) := by
  have h := (summable_featureWeight c C g p q hc hp hq).add
    (summable_featureWeight_moment c C g p q K alpha hc hp hq hK)
  apply h.congr
  intro n
  ring

section SourceMoments

variable {E : Type*} [NormedAddCommGroup E]
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E)
  (c C g p q K alpha : ℝ) (φ : ∀ n, E → H n)
  (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K)
  (hX : AEStronglyMeasurable X μ) (hφ : ∀ n, Continuous (φ n))
  (hmoment : ∀ n, Integrable (fun ω => ‖X ω‖ ^ (n + 1)) μ)
  (hmean : ∀ n, (∫ ω, ‖X ω‖ ^ (n + 1) ∂μ) ≤
    K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha))
  (hgrowth : ∀ n x, ‖φ n x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1)))

include hc hC hp hq hK hX hφ hmoment hmean hgrowth

omit [∀ n, CompleteSpace (H n)] [∀ n, InnerProductSpace ℝ (H n)] hc hC hp hq hK hmean in
/-- The source coordinate features are genuinely integrable under the fixed law. -/
theorem integrable_sourceCoordinateFeature (n : ℕ) : Integrable (fun ω => φ n (X ω)) μ :=
  coordinate_feature_integrable μ X (φ n) (n + 1) (featureGrowth C g q n)
    hX (hφ n) (hmoment n) (hgrowth n)

omit [∀ n, CompleteSpace (H n)] [∀ n, InnerProductSpace ℝ (H n)] hc hp hq hK in
/-- Each weighted coordinate norm integral is bounded by the literal source envelope. -/
theorem source_weighted_integral_norm_le (n : ℕ) :
    sourceFeatureScale c p n * (∫ ω, ‖φ n (X ω)‖ ∂μ) ≤
      featureWeight c C g p q n *
        (1 + K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha)) := by
  have h := integral_norm_coordinate_feature_le μ X (φ n) (n + 1)
    (featureGrowth C g q n)
    (K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha))
    (featureGrowth_nonneg C g q hC n)
    (integrable_sourceCoordinateFeature μ X C g q φ hX hφ hmoment hgrowth n)
    (hmoment n) (hmean n) (hgrowth n)
  have hw := mul_le_mul_of_nonneg_left h (sourceFeatureScale_pos c p n).le
  simpa only [sourceFeatureScale, featureWeight, featureGrowth, mul_assoc] using hw

omit [∀ n, CompleteSpace (H n)] [∀ n, InnerProductSpace ℝ (H n)] in
/-- Source coordinate moment bounds imply weighted L1 summability, rather
than assuming convergence of the Hilbert-valued population moment. -/
theorem summable_source_weighted_integral_norm :
    Summable (fun n => sourceFeatureScale c p n * ∫ ω, ‖φ n (X ω)‖ ∂μ) := by
  exact Summable.of_nonneg_of_le
    (fun n => mul_nonneg (sourceFeatureScale_pos c p n).le (integral_nonneg (fun _ => norm_nonneg _)))
    (source_weighted_integral_norm_le μ X c C g p q K alpha φ hC hX hφ hmoment hmean hgrowth)
    (summable_sourceMomentEnvelope c C g p q K alpha hc hp hq hK)

/-- The actual source Hilbert-valued feature is Bochner integrable under the
same fixed probability law as all of its coordinates. -/
theorem integrable_sourceWeightedFeatureMap_of_moments :
    Integrable (fun ω => sourceWeightedFeatureMap c p φ (X ω)) μ :=
  integrable_weightedHilbertSum μ (sourceFeatureScale c p)
    (fun n => (sourceFeatureScale_pos c p n).le) (fun n ω => φ n (X ω))
    (integrable_sourceCoordinateFeature μ X C g q φ hX hφ hmoment hgrowth)
    (summable_source_weighted_integral_norm μ X c C g p q K alpha φ
      hc hC hp hq hK hX hφ hmoment hmean hgrowth)

/-- The integral of the actual source feature map is precisely the encoded
vector of coordinate moments, all with respect to the original fixed law. -/
theorem integral_sourceWeightedFeatureMap_of_moments :
    (∫ ω, sourceWeightedFeatureMap c p φ (X ω) ∂μ) =
      weightedHilbertSum (sourceFeatureScale c p) (fun n => ∫ ω, φ n (X ω) ∂μ) :=
  integral_weightedHilbertSum μ (sourceFeatureScale c p)
    (fun n => (sourceFeatureScale_pos c p n).le) (fun n ω => φ n (X ω))
    (integrable_sourceCoordinateFeature μ X C g q φ hX hφ hmoment hgrowth)
    (summable_source_weighted_integral_norm μ X c C g p q K alpha φ
      hc hC hp hq hK hX hφ hmoment hmean hgrowth)

omit [∀ n, CompleteSpace (H n)] in
/-- The actual encoded source moment vector has the exact population series
bound, with all dependence on the fixed moment scale K retained. -/
theorem norm_sourceCoordinateMoment_le :
    ‖weightedHilbertSum (sourceFeatureScale c p) (fun n => ∫ ω, φ n (X ω) ∂μ)‖ ≤
      ∑' n, featureWeight c C g p q n *
        (1 + K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha)) := by
  exact (norm_weightedCoordinateIntegral_le μ (sourceFeatureScale c p)
      (fun n => (sourceFeatureScale_pos c p n).le) (fun n ω => φ n (X ω))
      (summable_source_weighted_integral_norm μ X c C g p q K alpha φ
        hc hC hp hq hK hX hφ hmoment hmean hgrowth)).trans
    (Summable.tsum_le_tsum
      (source_weighted_integral_norm_le μ X c C g p q K alpha φ hC hX hφ hmoment hmean hgrowth)
      (summable_source_weighted_integral_norm μ X c C g p q K alpha φ
        hc hC hp hq hK hX hφ hmoment hmean hgrowth)
      (summable_sourceMomentEnvelope c C g p q K alpha hc hp hq hK))

/-- The source's positive weights recover each literal coordinate expectation
from the genuine Hilbert-valued Bochner integral. -/
theorem decoded_sourceWeightedMoment_of_moments (n : ℕ) :
    weightedCoordinateProjection (sourceFeatureScale c p) n
      (∫ ω, sourceWeightedFeatureMap c p φ (X ω) ∂μ) = ∫ ω, φ n (X ω) ∂μ :=
  weightedCoordinateProjection_integral μ (sourceFeatureScale c p)
    (fun n => (sourceFeatureScale_pos c p n).le) (fun n ω => φ n (X ω))
    (integrable_sourceCoordinateFeature μ X C g q φ hX hφ hmoment hgrowth)
    (summable_source_weighted_integral_norm μ X c C g p q K alpha φ
      hc hC hp hq hK hX hφ hmoment hmean hgrowth) n (sourceFeatureScale_pos c p n).ne'

end SourceMoments

end PaperFormalization.Manuscript
