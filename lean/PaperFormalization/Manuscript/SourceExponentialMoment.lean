import PaperFormalization.Manuscript.SourceMomentClass
import PaperFormalization.Manuscript.WeightedBochnerMoment
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! # The original moment class gives the exact source exponential moment

All integrals use the unchanged population law. Positive fractional orders
below one follow from probability Lp monotonicity, and the exponential is
integrated through its absolutely integrable nonnegative power series.
-/
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace PaperFormalization.Manuscript

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

/-- The original class also supplies genuine positive fractional moments.
The max-one factor exactly joins the Lyapunov and original q>=1 estimates. -/
theorem sourceMomentClass_positive_moment (alpha K : ℝ) (hK : 0 < K)
    (μ : Measure E) (hμ : μ ∈ sourceMomentClass alpha K) (q : ℝ) (hq : 0 < q) :
    Integrable (fun x : E => ‖x‖ ^ q) μ ∧
      (∫ x : E, ‖x‖ ^ q ∂μ) ≤ K ^ q * (max 1 q) ^ (q / alpha) := by
  by_cases hq1 : 1 ≤ q
  · rw [max_eq_right hq1]
    exact ⟨sourceMomentClass_integrable_norm_rpow alpha K μ hμ q hq1,
      sourceMomentClass_integral_norm_rpow_le alpha K hK μ hμ q hq1⟩
  letI : IsProbabilityMeasure μ := hμ.1
  have hbound : eLpNorm (id : E → E) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal K := by
    have hmono := eLpNorm_le_eLpNorm_of_exponent_le
      (f := (id : E → E)) (μ := μ)
      (show ENNReal.ofReal q ≤ ENNReal.ofReal 1 from ENNReal.ofReal_le_ofReal (by linarith))
      aestronglyMeasurable_id
    exact hmono.trans (by simpa using hμ.2 1 le_rfl)
  have hm : MemLp (id : E → E) (ENNReal.ofReal q) μ :=
    ⟨aestronglyMeasurable_id, hbound.trans_lt ENNReal.ofReal_lt_top⟩
  have hi : Integrable (fun x : E => ‖x‖ ^ q) μ := by
    simpa only [id_eq, ENNReal.toReal_ofReal hq.le] using
      hm.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top
  rw [hm.eLpNorm_eq_integral_rpow_norm
    (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top] at hbound
  have hroot : (∫ x : E, ‖x‖ ^ q ∂μ) ^ q⁻¹ ≤ K := by
    simpa only [id_eq, ENNReal.toReal_ofReal hq.le,
      ENNReal.ofReal_le_ofReal_iff hK.le] using hbound
  refine ⟨hi, ?_⟩
  rw [max_eq_left (le_of_not_ge hq1), Real.one_rpow, mul_one]
  exact (Real.rpow_inv_le_iff_of_pos
    (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg x) q)) hK.le hq).mp hroot

/-- Literal population exponential scale from the source Step 1. -/
noncomputable def sourcePopulationExponentialScale (alpha K : ℝ) : ℝ :=
  max 1 (K * (2 * Real.exp 1 * (1 + alpha)) ^ (1 / alpha))

/-- The max-one scale retains the exact 2e(1+alpha) power bound. -/
theorem sourcePopulationExponentialScale_rpow_ge (alpha K : ℝ)
    (halpha : 0 < alpha) (hK : 0 < K) :
    2 * Real.exp 1 * (1 + alpha) * K ^ alpha ≤
      (sourcePopulationExponentialScale alpha K) ^ alpha := by
  have hbase : 0 < 2 * Real.exp 1 * (1 + alpha) := by positivity
  have h := Real.rpow_le_rpow (by positivity : 0 ≤ K *
    (2 * Real.exp 1 * (1 + alpha)) ^ (1 / alpha))
    (le_max_right 1 _) halpha.le
  rw [Real.mul_rpow hK.le (Real.rpow_nonneg hbase.le _),
    ← Real.rpow_mul hbase.le, one_div_mul_cancel halpha.ne', Real.rpow_one] at h
  simpa only [sourcePopulationExponentialScale, mul_comm] using h

/-- The elementary factorial estimate needed in the source argument follows
from the nonnegative exponential series; no asymptotic Stirling premise. -/
theorem source_factorial_lower_bound (j : ℕ) :
    ((j : ℝ) / Real.exp 1) ^ j ≤ (j.factorial : ℝ) := by
  have h := Real.pow_div_factorial_le_exp (j : ℝ) (show (0 : ℝ) ≤ j by positivity) j
  have hf : (0 : ℝ) < j.factorial := by positivity
  rw [div_le_iff₀ hf] at h
  rw [div_pow]
  apply (div_le_iff₀ (pow_pos (Real.exp_pos 1) j)).mpr
  simpa only [← Real.exp_nat_mul, mul_one, mul_comm] using h

/-- The order alpha*j moment is genuinely integrable and has the precise
source max-one bound, before simplifying that bound for the series. -/
theorem sourceMomentClass_alpha_nat_moment (alpha K : ℝ)
    (halpha : 0 < alpha) (hK : 0 < K) (μ : Measure E)
    (hμ : μ ∈ sourceMomentClass alpha K) (j : ℕ) (hj : 1 ≤ j) :
    Integrable (fun x : E => ‖x‖ ^ (alpha * (j : ℝ))) μ ∧
      (∫ x : E, ‖x‖ ^ (alpha * (j : ℝ)) ∂μ) ≤
        (K ^ alpha) ^ j * (max 1 (alpha * (j : ℝ))) ^ j := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
  have h := sourceMomentClass_positive_moment alpha K hK μ hμ (alpha * j) (mul_pos halpha hj0)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  rw [Real.rpow_mul hK.le, Real.rpow_natCast]
  have he : alpha * (j : ℝ) / alpha = j := by field_simp
  rw [he, Real.rpow_natCast]

/-- Every literal term in the exponential series is genuinely integrable and
its integral is at most 2^(-j), including the constant term at j=0. -/
theorem sourceMomentClass_exponential_series_term
    (alpha K : ℝ) (halpha : 0 < alpha) (hK : 0 < K)
    (μ : Measure E) (hμ : μ ∈ sourceMomentClass alpha K) (j : ℕ) :
    let b := sourcePopulationExponentialScale alpha K
    Integrable (fun x : E => (‖x‖ ^ alpha / b ^ alpha) ^ j / (j.factorial : ℝ)) μ ∧
      (∫ x : E, (‖x‖ ^ alpha / b ^ alpha) ^ j / (j.factorial : ℝ) ∂μ) ≤ (1 / 2 : ℝ) ^ j := by
  letI : IsProbabilityMeasure μ := hμ.1
  let b := sourcePopulationExponentialScale alpha K
  have hb1 : 1 ≤ b := le_max_left _ _
  have hb : 0 < b := by linarith
  have hbpow : 0 < b ^ alpha := Real.rpow_pos_of_pos hb _
  have hf : 0 < (j.factorial : ℝ) := by positivity
  by_cases hj : j = 0
  · subst j
    simp
  have hj1 : 1 ≤ j := by omega
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  obtain ⟨hint, hmoment⟩ := sourceMomentClass_alpha_nat_moment alpha K halpha hK μ hμ j hj1
  have hid (x : E) : (‖x‖ ^ alpha / b ^ alpha) ^ j / (j.factorial : ℝ) =
      ‖x‖ ^ (alpha * (j : ℝ)) / ((b ^ alpha) ^ j * (j.factorial : ℝ)) := by
    rw [div_pow, ← Real.rpow_mul_natCast (norm_nonneg x)]
    ring
  have hmax : max 1 (alpha * (j : ℝ)) ≤ (1 + alpha) * j := by
    apply max_le <;> nlinarith
  have hscale := sourcePopulationExponentialScale_rpow_ge alpha K halpha hK
  have hratio : K ^ alpha * max 1 (alpha * (j : ℝ)) / b ^ alpha ≤
      (j : ℝ) / (2 * Real.exp 1) := by
    apply (div_le_div_iff₀ hbpow (by positivity : 0 < 2 * Real.exp 1)).mpr
    have h1 := mul_le_mul_of_nonneg_left hmax (Real.rpow_nonneg hK.le alpha)
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * Real.exp 1)
    have h3 := mul_le_mul_of_nonneg_right hscale (by positivity : (0 : ℝ) ≤ j)
    dsimp only [b] at *
    nlinarith
  have hratio0 : 0 ≤ K ^ alpha * max 1 (alpha * (j : ℝ)) / b ^ alpha := by positivity
  have hpower := pow_le_pow_left₀ hratio0 hratio j
  have hfactorial := source_factorial_lower_bound j
  have hscalar : (K ^ alpha) ^ j * (max 1 (alpha * (j : ℝ))) ^ j /
      ((b ^ alpha) ^ j * (j.factorial : ℝ)) ≤ (1 / 2 : ℝ) ^ j := by
    calc
      _ = (K ^ alpha * max 1 (alpha * (j : ℝ)) / b ^ alpha) ^ j / (j.factorial : ℝ) := by
        rw [div_pow, mul_pow]
        ring
      _ ≤ ((j : ℝ) / (2 * Real.exp 1)) ^ j / (j.factorial : ℝ) :=
        div_le_div_of_nonneg_right hpower hf.le
      _ ≤ (1 / 2 : ℝ) ^ j := by
        apply (div_le_iff₀ hf).mpr
        calc
          _ = (1 / 2 : ℝ) ^ j * ((j : ℝ) / Real.exp 1) ^ j := by rw [← mul_pow]; congr 1; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hfactorial (by positivity)
  have hintF : Integrable (fun x : E => (‖x‖ ^ alpha / b ^ alpha) ^ j / (j.factorial : ℝ)) μ := by
    simp_rw [hid]
    exact hint.div_const _
  refine ⟨hintF, ?_⟩
  change (∫ x : E, (‖x‖ ^ alpha / b ^ alpha) ^ j / (j.factorial : ℝ) ∂μ) ≤ (1 / 2 : ℝ) ^ j
  simp_rw [hid, integral_div]
  exact (div_le_div_of_nonneg_right hmoment (by positivity)).trans hscalar

/-- The original all-real-q population class implies the exact unconditional
exponential bound at the manuscript scale. Integrability is proved first, by
summable integrals of the norms of the actual exponential-series terms. -/
theorem sourceMomentClass_integrable_exp_and_integral_le_two
    (alpha K : ℝ) (halpha : 0 < alpha) (hK : 0 < K)
    (μ : Measure E) (hμ : μ ∈ sourceMomentClass alpha K) :
    let b := sourcePopulationExponentialScale alpha K
    Integrable (fun x : E => Real.exp (‖x‖ ^ alpha / b ^ alpha)) μ ∧
      (∫ x : E, Real.exp (‖x‖ ^ alpha / b ^ alpha) ∂μ) ≤ 2 := by
  let b := sourcePopulationExponentialScale alpha K
  let F : ℕ → E → ℝ := fun j x => (‖x‖ ^ alpha / b ^ alpha) ^ j / (j.factorial : ℝ)
  have hF (j : ℕ) := sourceMomentClass_exponential_series_term alpha K halpha hK μ hμ j
  have hb : 0 ≤ b := le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)
  have hnonneg (j : ℕ) (x : E) : 0 ≤ F j x := by dsimp [F]; positivity
  have hnorm (j : ℕ) : (∫ x, ‖F j x‖ ∂μ) = ∫ x, F j x ∂μ := by
    simp only [Real.norm_eq_abs, abs_of_nonneg (hnonneg j _)]
  have hs : Summable (fun j => ∫ x, F j x ∂μ) :=
    hasSum_geometric_two.summable.of_nonneg_of_le
      (fun j => integral_nonneg (hnonneg j)) (fun j => (hF j).2)
  have hsnorm : Summable (fun j => ∫ x, ‖F j x‖ ∂μ) := by simpa only [hnorm] using hs
  have hsum (x : E) : (∑' j, F j x) = Real.exp (‖x‖ ^ alpha / b ^ alpha) := by
    simpa only [F, Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp (‖x‖ ^ alpha / b ^ alpha)).tsum_eq
  have hint : Integrable (fun x => ∑' j, F j x) μ :=
    integrable_series_of_summable_integral_norm μ F (fun j => (hF j).1) hsnorm
  refine ⟨by simpa only [hsum] using hint, ?_⟩
  change (∫ x, Real.exp (‖x‖ ^ alpha / b ^ alpha) ∂μ) ≤ 2
  calc
    _ = ∫ x, ∑' j, F j x ∂μ := by simp_rw [hsum]
    _ = ∑' j, ∫ x, F j x ∂μ :=
      (integral_tsum_of_summable_integral_norm (fun j => (hF j).1) hsnorm).symm
    _ ≤ ∑' j, (1 / 2 : ℝ) ^ j :=
      hs.tsum_le_tsum (fun j => (hF j).2) hasSum_geometric_two.summable
    _ = 2 := hasSum_geometric_two.tsum_eq

end PaperFormalization.Manuscript
