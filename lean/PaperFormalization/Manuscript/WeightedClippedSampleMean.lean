import PaperFormalization.Manuscript.ClippedFeatures
import PaperFormalization.Manuscript.WeightedSampleSensitivity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # The actual countable weighted clipped sample residual

The coordinate centers are actual integrals under the original population law.
A summable amplitude bound proves convergence, continuity, genuine integrability,
and the dominated-convergence interchange before coordinate mean bounds are
summed. The result is an expected-error bound, not a concentration theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace PaperFormalization.Manuscript

section Generic

variable {E : Type*} [TopologicalSpace E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, NormedSpace ℝ (H n)] {N : ℕ}

omit [TopologicalSpace E] in
/-- The exact uniform summable majorant for each weighted residual coordinate. -/
theorem weightedSampleResidual_term_norm_le (hN : 0 < N)
    (w : ℕ → ℝ≥0) (φ : ∀ n, E → H n) (P : ∀ n, H n) (A : ℕ → ℝ)
    (hφ : ∀ n x, ‖φ n x‖ ≤ A n) (hP : ∀ n, ‖P n‖ ≤ A n)
    (X : Fin N → E) (n : ℕ) :
    ‖(w n : ℝ) * ‖(N : ℝ)⁻¹ • ∑ i, φ n (X i) - P n‖‖ ≤
      2 * ((w n : ℝ) * A n) := by
  rw [Real.norm_of_nonneg (mul_nonneg (w n).coe_nonneg (norm_nonneg _))]
  have hb := (norm_sub_le _ _).trans
    (add_le_add (norm_bounded_sampleMean_le hN φ A hφ X n) (hP n))
  nlinarith [mul_le_mul_of_nonneg_left hb (w n).coe_nonneg]

/-- Uniform summability turns the literal countable residual into a continuous
function of the actual finite sample configuration. -/
theorem continuous_weightedSampleResidual (hN : 0 < N)
    (w : ℕ → ℝ≥0) (φ : ∀ n, E → H n) (P : ∀ n, H n) (A : ℕ → ℝ)
    (hc : ∀ n, Continuous (φ n))
    (hA : Summable (fun n => (w n : ℝ) * A n))
    (hφ : ∀ n x, ‖φ n x‖ ≤ A n) (hP : ∀ n, ‖P n‖ ≤ A n) :
    Continuous (weightedSampleResidual w φ P : (Fin N → E) → ℝ) := by
  apply continuous_tsum (fun n => ?_) (hA.mul_left 2)
    (fun n X => weightedSampleResidual_term_norm_le hN w φ P A hφ hP X n)
  exact continuous_const.mul
    ((continuous_const.smul (continuous_finsetSum _ (fun i _ =>
      (hc n).comp (continuous_apply i)))).sub continuous_const).norm

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [TopologicalSpace.PseudoMetrizableSpace E]
variable {Ω : Type*} [MeasurableSpace Ω]

omit [TopologicalSpace.PseudoMetrizableSpace E] in
/-- The actual residual of measurable samples is genuinely integrable from its
uniform amplitude bound, before any expected-error inequality is applied. -/
theorem integrable_weightedSampleResidual (hN : 0 < N)
    (w : ℕ → ℝ≥0) (φ : ∀ n, E → H n) (P : ∀ n, H n) (A : ℕ → ℝ)
    (hc : ∀ n, Continuous (φ n))
    (hA : Summable (fun n => (w n : ℝ) * A n))
    (hφ : ∀ n x, ‖φ n x‖ ≤ A n) (hP : ∀ n, ‖P n‖ ≤ A n)
    (ν : Measure Ω) [IsFiniteMeasure ν] (Y : Fin N → Ω → E)
    (hY : ∀ i, AEMeasurable (Y i) ν) :
    Integrable (fun ω => weightedSampleResidual w φ P (fun i => Y i ω)) ν := by
  have hcF := continuous_weightedSampleResidual hN w φ P A hc hA hφ hP
  have hm := (hcF.measurable.comp_aemeasurable
    (aemeasurable_pi_lambda (fun ω i => Y i ω) hY)).aestronglyMeasurable
  apply (integrable_const (2 * ∑' n, (w n : ℝ) * A n)).mono' hm
  filter_upwards with ω
  change ‖weightedSampleResidual w φ P (fun i => Y i ω)‖ ≤ _
  have hn : 0 ≤ weightedSampleResidual w φ P (fun i => Y i ω) :=
    tsum_nonneg (fun n => mul_nonneg (w n).coe_nonneg (norm_nonneg _))
  rw [Real.norm_of_nonneg hn]
  exact weightedSampleResidual_le hN w φ P A hA hφ hP (fun i => Y i ω)

/-- Dominated convergence exchanges the actual countable residual and its
expectation, using the proved uniform 2w_n A_n majorant. -/
theorem hasSum_integral_weightedSampleResidual (hN : 0 < N)
    (w : ℕ → ℝ≥0) (φ : ∀ n, E → H n) (P : ∀ n, H n) (A : ℕ → ℝ)
    (hc : ∀ n, Continuous (φ n))
    (hA : Summable (fun n => (w n : ℝ) * A n))
    (hφ : ∀ n x, ‖φ n x‖ ≤ A n) (hP : ∀ n, ‖P n‖ ≤ A n)
    (ν : Measure Ω) [IsFiniteMeasure ν] (Y : Fin N → Ω → E)
    (hY : ∀ i, AEMeasurable (Y i) ν) :
    HasSum (fun n => ∫ ω, (w n : ℝ) *
      ‖(N : ℝ)⁻¹ • ∑ i, φ n (Y i ω) - P n‖ ∂ν)
      (∫ ω, weightedSampleResidual w φ P (fun i => Y i ω) ∂ν) := by
  apply hasSum_integral_of_dominated_convergence
    (fun n _ω => 2 * ((w n : ℝ) * A n))
  · intro n
    have hmean : AEStronglyMeasurable (fun ω =>
        (N : ℝ)⁻¹ • ∑ i, φ n (Y i ω)) ν := by
      exact (Finset.aestronglyMeasurable_fun_sum _ (fun i _ =>
        (hc n).comp_aestronglyMeasurable (hY i).aestronglyMeasurable)).const_smul _
    exact aestronglyMeasurable_const.mul (hmean.sub aestronglyMeasurable_const).norm
  · intro n
    exact Filter.Eventually.of_forall (fun ω =>
      weightedSampleResidual_term_norm_le hN w φ P A hφ hP (fun i => Y i ω) n)
  · exact Filter.Eventually.of_forall (fun _ => hA.mul_left 2)
  · exact integrable_const _
  · exact Filter.Eventually.of_forall (fun ω =>
      (weightedSampleResidual_summable hN w φ P A hA hφ hP (fun i => Y i ω)).hasSum)

end Generic

section Clipped

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)]
variable {N : ℕ}

/-- The actual source clipped statistic, centered at the original-law clipped
population feature integrals. Clipping acts on the function, not the law. -/
noncomputable def weightedClippedSampleResidual (μ : Measure E) (D : ℝ)
    (w : ℕ → ℝ≥0) (φ : ∀ n, E → H n) (X : Fin N → E) : ℝ :=
  weightedSampleResidual w (fun n x => φ n (sourceRadialClip D x))
    (fun n => ∫ x, φ n (sourceRadialClip D x) ∂μ) X

/-- Each clipped coordinate is integrable under the original law, and its
Bochner population center has the exact source amplitude bound. -/
theorem clipped_populationFeature_integrable_and_norm_le (μ : Measure E)
    [IsProbabilityMeasure μ] (D : ℝ) (hD : 0 ≤ D)
    (L : ℕ → ℝ) (m : ℕ → ℕ) (hL : ∀ n, 0 ≤ L n)
    (φ : ∀ n, E → H n) (hc : ∀ n, Continuous (φ n))
    (hgrowth : ∀ n x, ‖φ n x‖ ≤ L n * (1 + ‖x‖ ^ m n)) (n : ℕ) :
    Integrable (fun x => φ n (sourceRadialClip D x)) μ ∧
      ‖∫ x, φ n (sourceRadialClip D x) ∂μ‖ ≤ L n * (1 + D ^ m n) := by
  refine ⟨(clipped_feature_memLp_two μ D (L n) (m n) hD (hL n)
    (φ n) (hc n) (hgrowth n)).integrable (by norm_num), ?_⟩
  simpa using norm_integral_le_of_norm_le_const (μ := μ)
    (Filter.Eventually.of_forall (norm_clipped_feature_le D (L n) (m n) hD (hL n)
      (φ n) (hgrowth n)))

/-- The actual countable clipped statistic is continuous and hence measurable.
Convergence is supplied by the source weighted amplitude series. -/
theorem continuous_measurable_weightedClippedSampleResidual (hN : 0 < N)
    (μ : Measure E) [IsProbabilityMeasure μ] (D : ℝ) (hD : 0 ≤ D)
    (w : ℕ → ℝ≥0) (L : ℕ → ℝ) (m : ℕ → ℕ) (hL : ∀ n, 0 ≤ L n)
    (φ : ∀ n, E → H n) (hc : ∀ n, Continuous (φ n))
    (hgrowth : ∀ n x, ‖φ n x‖ ≤ L n * (1 + ‖x‖ ^ m n))
    (hsum : Summable (fun n => (w n : ℝ) * (L n * (1 + D ^ m n)))) :
    Continuous (weightedClippedSampleResidual μ D w φ : (Fin N → E) → ℝ) ∧
    Measurable (weightedClippedSampleResidual μ D w φ : (Fin N → E) → ℝ) := by
  have hcont : Continuous (weightedClippedSampleResidual μ D w φ : (Fin N → E) → ℝ) :=
    continuous_weightedSampleResidual hN w _ _ (fun n => L n * (1 + D ^ m n))
      (fun n => (hc n).comp (sourceRadialClip_continuous D hD)) hsum
      (fun n => norm_clipped_feature_le D (L n) (m n) hD (hL n) (φ n) (hgrowth n))
      (fun n => (clipped_populationFeature_integrable_and_norm_le μ D hD L m hL φ hc hgrowth n).2)
  exact ⟨hcont, hcont.measurable⟩

variable [∀ n, CompleteSpace (H n)]

/-- Summing the actual coordinate expected-error estimates yields the exact
weighted amplitude / sqrt N bound, under the unchanged common population law.
Only pairwise independence is required; the countable sum is handled by proved
dominated convergence rather than an assumed concentration statement. -/
theorem integrable_expected_weightedClippedSampleResidual_le
    {Ω : Type*} [MeasurableSpace Ω] (hN : 0 < N)
    (μ : Measure E) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (Y : Fin N → Ω → E) (hLaw : ∀ i, ν.map (Y i) = μ)
    (hind : Pairwise (fun i j => IndepFun (Y i) (Y j) ν))
    (D : ℝ) (hD : 0 ≤ D) (w : ℕ → ℝ≥0)
    (L : ℕ → ℝ) (m : ℕ → ℕ) (hL : ∀ n, 0 ≤ L n)
    (φ : ∀ n, E → H n) (hc : ∀ n, Continuous (φ n))
    (hgrowth : ∀ n x, ‖φ n x‖ ≤ L n * (1 + ‖x‖ ^ m n))
    (hsum : Summable (fun n => (w n : ℝ) * (L n * (1 + D ^ m n)))) :
    Integrable (fun ω => weightedClippedSampleResidual μ D w φ (fun i => Y i ω)) ν ∧
    (∫ ω, weightedClippedSampleResidual μ D w φ (fun i => Y i ω) ∂ν) ≤
      (∑' n, (w n : ℝ) * (L n * (1 + D ^ m n))) / Real.sqrt N := by
  let f : ∀ n, E → H n := fun n x => φ n (sourceRadialClip D x)
  let P : ∀ n, H n := fun n => ∫ x, f n x ∂μ
  let A : ℕ → ℝ := fun n => L n * (1 + D ^ m n)
  have hfc (n : ℕ) : Continuous (f n) := (hc n).comp (sourceRadialClip_continuous D hD)
  have hf (n : ℕ) (x : E) : ‖f n x‖ ≤ A n :=
    norm_clipped_feature_le D (L n) (m n) hD (hL n) (φ n) (hgrowth n) x
  have hP (n : ℕ) : ‖P n‖ ≤ A n :=
    (clipped_populationFeature_integrable_and_norm_le μ D hD L m hL φ hc hgrowth n).2
  have hY (i : Fin N) : AEMeasurable (Y i) ν :=
    aemeasurable_of_map_neZero (by rw [hLaw i]; infer_instance)
  refine ⟨integrable_weightedSampleResidual hN w f P A hfc hsum hf hP ν Y hY, ?_⟩
  have hs := hasSum_integral_weightedSampleResidual hN w f P A hfc hsum hf hP ν Y hY
  change (∫ ω, weightedSampleResidual w f P (fun i => Y i ω) ∂ν) ≤ _
  rw [← hs.tsum_eq]
  have hsumBound : Summable (fun n => ((w n : ℝ) * A n) / Real.sqrt N) := hsum.div_const _
  calc
    _ ≤ ∑' n, ((w n : ℝ) * A n) / Real.sqrt N := by
      apply hs.summable.tsum_le_tsum _ hsumBound
      intro n
      letI : MeasurableSpace (H n) := borel (H n)
      letI : BorelSpace (H n) := ⟨rfl⟩
      rw [integral_const_mul]
      have hb := expected_clipped_feature_sampleMean_error_le μ ν Y hN hLaw hind
        D (L n) (m n) hD (hL n) (φ n) (hc n) (hgrowth n)
      have hw := mul_le_mul_of_nonneg_left hb (w n).coe_nonneg
      simpa only [f, P, A, mul_div_assoc] using hw
    _ = _ := by rw [tsum_div_const]

end Clipped

end PaperFormalization.Manuscript
