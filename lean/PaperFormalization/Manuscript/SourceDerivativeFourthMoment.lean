import PaperFormalization.Manuscript.SourceKernelIntegrability

/-! # Genuine fourth moments of the actual source derivative series

The population class retains every real moment order. The enlarged moment
scale used below is only a summability majorant for L4 integrability, not a
replacement for any displayed source residual or local regularity constant.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

set_option maxSynthPendingDepth 8

namespace PaperFormalization.Manuscript

section Series
variable {Ω F : Type*} [MeasurableSpace Ω] [NormedAddCommGroup F] [CompleteSpace F]

/-- Pointwise sums of genuinely L4 functions remain L4 when the L4 norms
have a summable real majorant. No separability of the target is imposed. -/
theorem memLp_four_of_hasSum_norm_majorant (μ : Measure Ω)
    (f : ℕ → Ω → F) (g : Ω → F) (b : ℕ → ℝ)
    (hf : ∀ n, MemLp (f n) 4 μ) (hb : Summable b)
    (hbound : ∀ n, eLpNorm (f n) 4 μ ≤ ENNReal.ofReal (b n))
    (hsum : ∀ x, HasSum (fun n => f n x) (g x)) : MemLp g 4 μ := by
  letI : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
  let u : ℕ → Lp F 4 μ := fun n => (hf n).toLp (f n)
  have hnorm : (∑' n, ‖u n‖ₑ) ≠ ⊤ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun n => ?_)) hb.tsum_ofReal_lt_top
    simpa only [u, Lp.enorm_toLp] using hbound n
  have heq : (fun x => (∑' n, u n) x) =ᵐ[μ] g := by
    filter_upwards [Lp.hasSum_coeFn_tsum hnorm,
      ae_all_iff.mpr (fun n => (hf n).coeFn_toLp)] with x hx hfx
    have hseries : (fun n => u n x) = (fun n => f n x) := funext (fun n => hfx n)
    rw [hseries] at hx
    exact hx.unique (hsum x)
  exact (Lp.memLp (∑' n, u n)).ae_eq heq

end Series

section Moments
variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
  [BorelSpace E] [SecondCountableTopology E]

omit [BorelSpace E] [SecondCountableTopology E] in
/-- The L4 norm of the n-th norm power is finite with its exact order-4n
moment bound. The constant power at n=0 is treated explicitly. -/
theorem sourceMomentClass_eLpNorm_norm_pow_four_le
    (alpha K : ℝ) (hK : 0 < K) (μ : Measure E)
    (hμ : μ ∈ sourceMomentClass alpha K) (n : ℕ) :
    eLpNorm (fun x : E => ‖x‖ ^ n) 4 μ ≤
      ENNReal.ofReal ((K * (4 * (n : ℝ)) ^ (1 / alpha)) ^ n) := by
  letI : IsProbabilityMeasure μ := hμ.1
  rcases n with _ | n
  · simp only [pow_zero, ENNReal.ofReal_one]
    rw [eLpNorm_const (1 : ℝ) (by norm_num) (by exact NeZero.ne μ)]
    simp
  · have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have h4n : 1 ≤ 4 * ((n + 1 : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
    have hid := hμ.2 (4 * ((n + 1 : ℕ) : ℝ)) h4n
    have hp : (4 : ℝ≥0∞) * ENNReal.ofReal (((n + 1 : ℕ) : ℝ)) =
        ENNReal.ofReal (4 * ((n + 1 : ℕ) : ℝ)) := by
      rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4)]
      norm_num
    calc
      eLpNorm (fun x : E => ‖x‖ ^ (n + 1)) 4 μ =
          (eLpNorm (id : E → E) (ENNReal.ofReal (4 * ((n + 1 : ℕ) : ℝ))) μ) ^
            (((n + 1 : ℕ) : ℝ)) := by
        simpa only [id_eq, Real.rpow_natCast, hp] using
          (eLpNorm_norm_rpow (p := 4) (μ := μ) (id : E → E) hn)
      _ ≤ (ENNReal.ofReal (K * (4 * ((n + 1 : ℕ) : ℝ)) ^ (1 / alpha))) ^
            (((n + 1 : ℕ) : ℝ)) := ENNReal.rpow_le_rpow hid hn.le
      _ = ENNReal.ofReal ((K * (4 * ((n + 1 : ℕ) : ℝ)) ^ (1 / alpha)) ^ (n + 1)) := by
        rw [← Real.rpow_natCast]
        exact ENNReal.ofReal_rpow_of_nonneg (by positivity) hn.le

omit [SecondCountableTopology E] in
/-- All norm powers are genuinely L4, including the constant power. -/
theorem sourceMomentClass_memLp_norm_pow_four
    (alpha K : ℝ) (hK : 0 < K) (μ : Measure E)
    (hμ : μ ∈ sourceMomentClass alpha K) (n : ℕ) :
    MemLp (fun x : E => ‖x‖ ^ n) 4 μ := by
  exact ⟨(continuous_norm.pow n).aestronglyMeasurable,
    (sourceMomentClass_eLpNorm_norm_pow_four_le alpha K hK μ hμ n).trans_lt
      ENNReal.ofReal_lt_top⟩

omit [SecondCountableTopology E] in
/-- A weighted polynomial coordinate envelope is genuinely L4, with the
actual order-4n moment estimate rather than a totalized integral. -/
theorem sourceMomentClass_eLpNorm_weighted_envelope_four_le
    (alpha K : ℝ) (hK : 0 < K) (μ : Measure E)
    (hμ : μ ∈ sourceMomentClass alpha K) (w : ℝ) (hw : 0 ≤ w) (n : ℕ) :
    eLpNorm (fun x : E => w * (1 + ‖x‖ ^ n)) 4 μ ≤
      ENNReal.ofReal (w * (1 + (K * (4 * (n : ℝ)) ^ (1 / alpha)) ^ n)) := by
  letI : IsProbabilityMeasure μ := hμ.1
  have hconst : eLpNorm (fun _ : E => (1 : ℝ)) 4 μ = 1 := by
    rw [eLpNorm_const (1 : ℝ) (by norm_num) (by exact NeZero.ne μ)]
    simp
  have hsum : eLpNorm (fun x : E => 1 + ‖x‖ ^ n) 4 μ ≤
      ENNReal.ofReal (1 + (K * (4 * (n : ℝ)) ^ (1 / alpha)) ^ n) := by
    calc
      _ ≤ eLpNorm (fun _ : E => (1 : ℝ)) 4 μ +
          eLpNorm (fun x : E => ‖x‖ ^ n) 4 μ :=
        eLpNorm_add_le aestronglyMeasurable_const
          (continuous_norm.pow n).aestronglyMeasurable (by norm_num)
      _ ≤ 1 + ENNReal.ofReal ((K * (4 * (n : ℝ)) ^ (1 / alpha)) ^ n) := by
        rw [hconst]
        exact add_le_add le_rfl
          (sourceMomentClass_eLpNorm_norm_pow_four_le alpha K hK μ hμ n)
      _ = _ := by rw [ENNReal.ofReal_add (by positivity) (by positivity)]; simp
  calc
    _ = ENNReal.ofReal w * eLpNorm (fun x : E => 1 + ‖x‖ ^ n) 4 μ := by
      change eLpNorm (w • (fun x : E => 1 + ‖x‖ ^ n)) 4 μ = _
      rw [eLpNorm_const_smul, ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hw]
    _ ≤ ENNReal.ofReal w * ENNReal.ofReal
        (1 + (K * (4 * (n : ℝ)) ^ (1 / alpha)) ^ n) := mul_le_mul_right hsum _
    _ = _ := (ENNReal.ofReal_mul hw).symm

end Moments

/-- The previous-order L4 moment envelope is summable against the source
weights. The inflation 4^(1/alpha)K and then 1+that scale is only used here
to prove convergence, and does not alter any source residual constant. -/
theorem summable_source_derivative_L4_majorant
    (c C g p q alpha K : ℝ) (hc : 0 < c) (hC : 0 ≤ C)
    (hp : 1 < p) (hq : q < p) (halpha : 0 < alpha) (hK : 0 < K) :
    Summable (fun n : ℕ => featureWeight c C g p q n *
      (1 + (K * (4 * (n : ℝ)) ^ (1 / alpha)) ^ n)) := by
  let K₄ := (4 : ℝ) ^ (1 / alpha) * K
  have hK₄ : 0 ≤ K₄ := by dsimp [K₄]; positivity
  have hmajor := (summable_featureWeight c C g p q hc hp hq).add
    (summable_featureWeight_moment c C g p q (1 + K₄) alpha hc hp hq (by linarith))
  apply hmajor.of_nonneg_of_le
  · intro n
    exact mul_nonneg (featureWeight_nonneg c C g p q hC n) (by positivity)
  · intro n
    have hpow : (K * (4 * (n : ℝ)) ^ (1 / alpha)) ^ n ≤
        (K₄ * ((n + 1 : ℕ) : ℝ) ^ (1 / alpha)) ^ n := by
      apply pow_le_pow_left₀ (by positivity)
      calc
        _ ≤ K * (4 * ((n + 1 : ℕ) : ℝ)) ^ (1 / alpha) := by
          gcongr
          omega
        _ = _ := by
          rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4) (by positivity)]
          dsimp [K₄]
          ring
    have hprev := previous_moment_le_full K₄ alpha hK₄ halpha n
    have h := mul_le_mul_of_nonneg_left (hpow.trans hprev)
      (featureWeight_nonneg c C g p q hC n)
    change _ ≤ featureWeight c C g p q n + _
    nlinarith

section Derivative

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [BorelSpace E] [SecondCountableTopology E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

/-- The source map's actual first derivative is operator-valued L4 under the
original all-real-order population condition. The proof sums its genuine
coordinate derivative operators; it adds no separability assumption on their
target operator space and no support bound on the population law. -/
theorem sourceMomentClass_memLp_four_fderiv_sourceWeightedFeatureMap
    (c C g p q alpha K : ℝ) (φ : ∀ n, E → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (halpha : 0 < alpha) (hK : 0 < K)
    (hφ : ∀ n, ContDiff ℝ 2 (φ n))
    (hgrowth : ∀ n x k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) x‖ ≤
      featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1 - k)))
    (μ : Measure E) (hμ : μ ∈ sourceMomentClass alpha K) :
    MemLp (fderiv ℝ (sourceWeightedFeatureMap c p φ)) 4 μ := by
  let a := sourceFeatureScale c p
  let f : ℕ → E → (E →L[ℝ] lp H 2) := fun n x =>
    (weightedCoordinateEmbedding a n).comp (fderiv ℝ (φ n) x)
  let b : ℕ → ℝ := fun n => featureWeight c C g p q n *
    (1 + (K * (4 * (n : ℝ)) ^ (1 / alpha)) ^ n)
  have hpoint (n : ℕ) (x : E) : ‖f n x‖ ≤
      featureWeight c C g p q n * (1 + ‖x‖ ^ n) := by
    calc
      _ ≤ a n * ‖fderiv ℝ (φ n) x‖ :=
        norm_weightedCoordinateEmbedding_comp_le a n (sourceFeatureScale_pos c p n).le _
      _ ≤ a n * (featureGrowth C g q n * (1 + ‖x‖ ^ n)) := by
        apply mul_le_mul_of_nonneg_left _ (sourceFeatureScale_pos c p n).le
        simpa only [norm_iteratedFDeriv_one, Nat.add_sub_cancel] using hgrowth n x 1 (by omega)
      _ = _ := by simp only [a, sourceFeatureScale, featureGrowth, featureWeight, mul_assoc]
  have hbound (n : ℕ) : eLpNorm (f n) 4 μ ≤ ENNReal.ofReal (b n) := by
    exact (eLpNorm_mono_ae_real (Filter.Eventually.of_forall (hpoint n))).trans
      (sourceMomentClass_eLpNorm_weighted_envelope_four_le alpha K hK μ hμ
        (featureWeight c C g p q n) (featureWeight_nonneg c C g p q hC n) n)
  have hf (n : ℕ) : MemLp (f n) 4 μ := by
    refine ⟨?_, (hbound n).trans_lt ENNReal.ofReal_lt_top⟩
    exact (continuous_const.clm_comp ((hφ n).continuous_fderiv (by norm_num))).aestronglyMeasurable
  apply memLp_four_of_hasSum_norm_majorant μ f _ b hf
    (summable_source_derivative_L4_majorant c C g p q alpha K hc hC hp hq halpha hK) hbound
  intro x
  rw [fderiv_sourceWeightedFeatureMap_eq_weightedHilbertOperator c C g p q φ hc hC hp hq hφ hgrowth]
  exact (summable_weightedCoordinateEmbedding_comp a
    (fun n => (sourceFeatureScale_pos c p n).le) (fun n => fderiv ℝ (φ n) x)
    (summable_sourceFeatureScale_norm_fderiv c C g p q φ hc hC hp hq hgrowth x)).hasSum

/-- In particular the actual derivative's fourth power of its operator norm has a genuine
Bochner integral under the original population law. -/
theorem sourceMomentClass_integrable_norm_four_fderiv_sourceWeightedFeatureMap
    (c C g p q alpha K : ℝ) (φ : ∀ n, E → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (halpha : 0 < alpha) (hK : 0 < K)
    (hφ : ∀ n, ContDiff ℝ 2 (φ n))
    (hgrowth : ∀ n x k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) x‖ ≤
      featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1 - k)))
    (μ : Measure E) (hμ : μ ∈ sourceMomentClass alpha K) :
    Integrable (fun x => ‖fderiv ℝ (sourceWeightedFeatureMap c p φ) x‖ ^ 4) μ := by
  exact (sourceMomentClass_memLp_four_fderiv_sourceWeightedFeatureMap
    c C g p q alpha K φ hc hC hp hq halpha hK hφ hgrowth μ hμ).integrable_norm_pow (by norm_num)

end Derivative

end PaperFormalization.Manuscript
