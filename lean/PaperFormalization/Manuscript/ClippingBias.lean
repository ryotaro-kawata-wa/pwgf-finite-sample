import PaperFormalization.Manuscript.ClippedFeatures
import PaperFormalization.Manuscript.SourceFeatureSecondMoment

/-! # Genuine population clipping bias under the unchanged law -/
open MeasureTheory Set
open scoped ENNReal
namespace PaperFormalization.Manuscript

variable {Ω F : Type*} [MeasurableSpace Ω] [NormedAddCommGroup F]

/-- Cauchy--Schwarz on an actual restricted measure, bounded by the original
second moment and the true event probability. -/
theorem setIntegral_norm_le_sqrt_second_moment (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → F) (hf : MemLp f 2 μ) (s : Set Ω) :
    (∫ x in s, ‖f x‖ ∂μ) ≤
      Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) * Real.sqrt (μ.real s) := by
  have hf' : MemLp (fun x => ‖f x‖) (ENNReal.ofReal 2) (μ.restrict s) := by
    simpa using (hf.restrict s).norm
  have hg : MemLp (fun _x : Ω => (1 : ℝ)) (ENNReal.ofReal 2) (μ.restrict s) := memLp_const 1
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun x => norm_nonneg (f x)))
    (Filter.Eventually.of_forall (fun _ => zero_le_one)) hf' hg
  have hi : (∫ x in s, ‖f x‖ ^ 2 ∂μ) ≤ ∫ x, ‖f x‖ ^ 2 ∂μ :=
    integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall (fun x => sq_nonneg ‖f x‖))
      (hf.integrable_norm_pow (by norm_num))
  have hm : (μ.restrict s).real univ = μ.real s := by simp [measureReal_def]
  simp only [mul_one, Real.rpow_two, one_pow, integral_const, smul_eq_mul, mul_one,
    ← Real.sqrt_eq_rpow, hm] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hi) (Real.sqrt_nonneg _))

variable [NormedSpace ℝ F]

/-- An actual integral discrepancy supported on an event is controlled by
a genuine L2 envelope and the original event probability. -/
theorem norm_integral_sub_le_tail_L2 (μ : Measure Ω) [IsFiniteMeasure μ]
    (f g : Ω → F) (hf : Integrable f μ) (hg : Integrable g μ)
    (a : Ω → ℝ) (ha : MemLp a 2 μ) (ha0 : ∀ x, 0 ≤ a x)
    (s : Set Ω) (hs : MeasurableSet s)
    (herr : ∀ x, ‖f x - g x‖ ≤ s.indicator (fun x => 2 * a x) x) :
    ‖(∫ x, f x ∂μ) - ∫ x, g x ∂μ‖ ≤
      2 * Real.sqrt (∫ x, ‖a x‖ ^ 2 ∂μ) * Real.sqrt (μ.real s) := by
  rw [← integral_sub hf hg]
  have hi : Integrable (s.indicator (fun x => 2 * a x)) μ :=
    ((ha.integrable (by norm_num)).const_mul 2).indicator hs
  calc
    _ ≤ ∫ x, ‖f x - g x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, s.indicator (fun x => 2 * a x) x ∂μ :=
      integral_mono (hf.sub hg).norm hi herr
    _ = 2 * ∫ x in s, ‖a x‖ ∂μ := by
      rw [integral_indicator hs, integral_const_mul]
      congr 1
      exact setIntegral_congr_fun hs (fun x _ => (Real.norm_of_nonneg (ha0 x)).symm)
    _ ≤ 2 * (Real.sqrt (∫ x, ‖a x‖ ^ 2 ∂μ) * Real.sqrt (μ.real s)) :=
      mul_le_mul_of_nonneg_left (setIntegral_norm_le_sqrt_second_moment μ a ha s) (by norm_num)
    _ = _ := by ring

section Source
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The actual source clipping bias retains the exact original order-2m
Minkowski envelope and the untruncated population tail probability. -/
theorem source_coordinate_clipping_bias_le
    (C g q alpha K D : ℝ) (hC : 0 ≤ C) (hK : 0 < K) (hD : 0 ≤ D)
    (μ : Measure E) (hμ : μ ∈ sourceMomentClass alpha K)
    (n : ℕ) (φ : E → F) (hφ : Continuous φ)
    (hgrowth : ∀ x, ‖φ x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1))) :
    ‖(∫ x, φ x ∂μ) - ∫ x, φ (sourceRadialClip D x) ∂μ‖ ≤
      2 * sourceCoordinateL2Envelope C g q alpha K n *
        Real.sqrt (μ.real {x | D < ‖x‖}) := by
  letI : IsProbabilityMeasure μ := hμ.1
  let L := featureGrowth C g q n
  let a : E → ℝ := fun x => L * (1 + ‖x‖ ^ (n + 1))
  have hL : 0 ≤ L := by dsimp [L, featureGrowth]; positivity
  have ha0 (x : E) : 0 ≤ a x := by dsimp [a]; positivity
  have hac : Continuous a := continuous_const.mul (continuous_const.add (continuous_norm.pow _))
  have hag (x : E) : ‖a x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1)) := by
    rw [Real.norm_of_nonneg (ha0 x)]
  have ha := sourceMomentClass_memLp_coordinate_feature_two C g q alpha K hC hK μ hμ n a hac hag
  have hsec := (sourceMomentClass_coordinate_feature_second_moment_le
    C g q alpha K hC hK μ hμ n a hac hag).2
  have hb := norm_integral_sub_le_tail_L2 μ φ (fun x => φ (sourceRadialClip D x))
    ((sourceMomentClass_memLp_coordinate_feature_two C g q alpha K hC hK μ hμ n φ hφ hgrowth).integrable (by norm_num))
    ((clipped_feature_memLp_two μ D L (n+1) hD hL φ hφ hgrowth).integrable (by norm_num))
    a ha ha0 {x | D < ‖x‖} (measurableSet_lt measurable_const continuous_norm.measurable) (by
      intro x
      simpa only [Set.indicator_apply, Set.mem_setOf_eq, a, mul_assoc] using
        norm_feature_sub_clipped_le D L (n+1) hD hL φ hgrowth x)
  have hB : 0 ≤ sourceCoordinateL2Envelope C g q alpha K n := by
    unfold sourceCoordinateL2Envelope featureGrowth
    positivity
  have hsqrt := (Real.sqrt_le_sqrt hsec).trans_eq (Real.sqrt_sq hB)
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) (Real.sqrt_nonneg _))
end Source
end PaperFormalization.Manuscript
