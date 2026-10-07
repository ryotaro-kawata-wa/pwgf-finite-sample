import PaperFormalization.Manuscript.ClippingBias

/-! # Actual population exponential tails and clipping bias

The population measure is unchanged. Exponential integrability precedes Markov;
no support truncation or desired tail bound is inserted as a hypothesis.
-/
open MeasureTheory Set
namespace PaperFormalization.Manuscript
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Markov under a finite original measure, from a genuine exponential moment. -/
theorem measureReal_lt_le_exp_moment (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → ℝ) (hf : Integrable (fun x => Real.exp (f x)) μ)
    (M u : ℝ) (hM : (∫ x, Real.exp (f x) ∂μ) ≤ M) :
    μ.real {x | u < f x} ≤ M * Real.exp (-u) := by
  have hs : {x | u < f x} ⊆ {x | Real.exp u ≤ Real.exp (f x)} := by
    intro x hx
    exact Real.exp_le_exp.mpr (le_of_lt hx)
  have hb := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos (f x)).le)) hf (Real.exp u)
  have hprob := measureReal_mono (μ := μ) hs
  have hmul : Real.exp u * μ.real {x | u < f x} ≤ M :=
    (mul_le_mul_of_nonneg_left hprob (Real.exp_pos u).le).trans (hb.trans hM)
  have h : μ.real {x | u < f x} ≤ M / Real.exp u := (le_div_iff₀ (Real.exp_pos u)).mpr (by simpa only [mul_comm] using hmul)
  simpa only [div_eq_mul_inv, Real.exp_neg] using h

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]

/-- The actual norm event is bounded by the source fixed-scale exponential
moment, with c=0 and alpha=0 allowed at this generic layer. -/
theorem measureReal_norm_tail_le_exp_moment (μ : Measure E) [IsFiniteMeasure μ]
    (c K alpha D M : ℝ) (hc : 0 ≤ c) (hK : 0 < K)
    (halpha : 0 ≤ alpha) (hD : 0 ≤ D)
    (hf : Integrable (fun x => Real.exp (c * (‖x‖ / K) ^ alpha)) μ)
    (hM : (∫ x, Real.exp (c * (‖x‖ / K) ^ alpha) ∂μ) ≤ M) :
    μ.real {x | D < ‖x‖} ≤ M * Real.exp (-(c * (D / K) ^ alpha)) := by
  have hs : {x : E | D < ‖x‖} ⊆
      {x | Real.exp (c * (D / K) ^ alpha) ≤ Real.exp (c * (‖x‖ / K) ^ alpha)} := by
    intro x hx
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (div_nonneg hD hK.le) (div_le_div_of_nonneg_right hx.le hK.le) halpha) hc)
  have hb := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos (c * (‖x‖ / K) ^ alpha)).le))
    hf (Real.exp (c * (D / K) ^ alpha))
  have hm := (mul_le_mul_of_nonneg_left (measureReal_mono (μ := μ) hs)
    (Real.exp_pos (c * (D / K) ^ alpha)).le).trans (hb.trans hM)
  have h : μ.real {x | D < ‖x‖} ≤ M / Real.exp (c * (D / K) ^ alpha) :=
    (le_div_iff₀ (Real.exp_pos (c * (D / K) ^ alpha))).mpr
    (by simpa only [mul_comm] using hm)
  simpa only [div_eq_mul_inv, Real.exp_neg] using h

/-- Taking the square root preserves the exact exponential half-rate. -/
theorem sqrt_le_sqrt_mul_exp_half (p M u : ℝ) (hM : 0 ≤ M)
    (hp : p ≤ M * Real.exp (-u)) :
    Real.sqrt p ≤ Real.sqrt M * Real.exp (-u / 2) := by
  have he : Real.sqrt (Real.exp (-u)) = Real.exp (-u / 2) := by
    have heq : (Real.exp (-u / 2)) ^ 2 = Real.exp (-u) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [← heq, Real.sqrt_sq (Real.exp_pos _).le]
  simpa only [Real.sqrt_mul hM, he] using Real.sqrt_le_sqrt hp

section Source
variable [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The literal source exponential clipping-bias rate, under the original
moment law and actual fixed-scale population exponential moment. -/
theorem source_coordinate_clipping_bias_exp_le
    (C g q alpha K D c K₀ M : ℝ) (hC : 0 ≤ C) (hK : 0 < K) (hD : 0 ≤ D)
    (hc : 0 ≤ c) (hK₀ : 0 < K₀) (halpha : 0 ≤ alpha)
    (μ : Measure E) (hμ : μ ∈ sourceMomentClass alpha K)
    (hexp : Integrable (fun x => Real.exp (c * (‖x‖ / K₀) ^ alpha)) μ)
    (hM : (∫ x, Real.exp (c * (‖x‖ / K₀) ^ alpha) ∂μ) ≤ M)
    (n : ℕ) (φ : E → F) (hφ : Continuous φ)
    (hgrowth : ∀ x, ‖φ x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1))) :
    ‖(∫ x, φ x ∂μ) - ∫ x, φ (sourceRadialClip D x) ∂μ‖ ≤
      2 * sourceCoordinateL2Envelope C g q alpha K n * Real.sqrt M *
        Real.exp (-(c * (D / K₀) ^ alpha) / 2) := by
  letI : IsProbabilityMeasure μ := hμ.1
  have hb := source_coordinate_clipping_bias_le C g q alpha K D hC hK hD μ hμ n φ hφ hgrowth
  have ht := measureReal_norm_tail_le_exp_moment μ c K₀ alpha D M hc hK₀ halpha hD hexp hM
  have hM0 : 0 ≤ M := (integral_nonneg (fun x => (Real.exp_pos (c * (‖x‖ / K₀) ^ alpha)).le)).trans hM
  have hs := sqrt_le_sqrt_mul_exp_half _ M _ hM0 ht
  have hB : 0 ≤ 2 * sourceCoordinateL2Envelope C g q alpha K n := by
    unfold sourceCoordinateL2Envelope featureGrowth
    positivity
  exact (hb.trans (mul_le_mul_of_nonneg_left hs hB)).trans_eq (by ring)
end Source
end PaperFormalization.Manuscript
