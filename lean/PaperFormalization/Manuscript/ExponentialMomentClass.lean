import PaperFormalization.Manuscript.SourceMomentClassEquivalence

/-! # A genuine exponential moment gives the original all-real-order class

This is the sharp scalar maximization and moment conversion used in the
population-localization lemma. Genuine integrability is established before
any real integral or root is used.
-/
open MeasureTheory Set
namespace PaperFormalization.Manuscript

/-- The exact maximum of t^r exp(-t), proved from log s<=s-1. -/
theorem rpow_le_exp_moment_majorant (t r : ℝ) (ht : 0 ≤ t) (hr : 0 < r) :
    t^r ≤ (r/Real.exp 1)^r * Real.exp t := by
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · rw [← ht0,Real.zero_rpow hr.ne']
    positivity
  have hl := Real.log_le_sub_one_of_pos (div_pos htpos hr)
  rw [Real.log_div htpos.ne' hr.ne'] at hl
  have hm := mul_le_mul_of_nonneg_left hl hr.le
  rw [Real.rpow_def_of_pos htpos,Real.rpow_def_of_pos (div_pos hr (Real.exp_pos _)),
    ← Real.exp_add,Real.log_div hr.ne' (Real.exp_pos _).ne',Real.log_exp]
  apply Real.exp_le_exp.mpr
  have hd : r*(t/r)=t := by field_simp
  nlinarith

/-- Literal u^q exponential domination at the source scale k, retaining
q/(alpha e) and valid for every real q>0, not only integer moments. -/
theorem norm_power_exponential_majorant (u k alpha q : ℝ)
    (hu : 0 ≤ u) (hk : 0 < k) (halpha : 0 < alpha) (hq : 0 < q) :
    u^q ≤ k^q * (q/(alpha*Real.exp 1))^(q/alpha) * Real.exp ((u/k)^alpha) := by
  have hp := rpow_le_exp_moment_majorant ((u/k)^alpha) (q/alpha)
    (Real.rpow_nonneg (div_nonneg hu hk.le) _) (div_pos hq halpha)
  have hid : ((u/k)^alpha)^(q/alpha) = (u/k)^q := by
    rw [← Real.rpow_mul (div_nonneg hu hk.le)]
    congr 1
    field_simp
  rw [hid] at hp
  have hm := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hk.le q)
  have hleft : k^q*(u/k)^q = u^q := by
    rw [← Real.mul_rpow hk.le (div_nonneg hu hk.le)]
    congr 1
    field_simp
  rw [hleft] at hm
  have heq : q/alpha/Real.exp 1 = q/(alpha*Real.exp 1) := by ring
  rw [heq] at hm
  simpa only [mul_assoc] using hm

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  [BorelSpace E]

/-- Exponential integrability yields every real norm moment genuinely,
with the exact source scalar coefficient before taking roots. -/
theorem integrable_norm_rpow_of_exp_moment (μ : Measure E)
    (k alpha q : ℝ) (hk : 0 < k) (halpha : 0 < alpha) (hq : 0 < q)
    (he : Integrable (fun x : E => Real.exp ((‖x‖/k)^alpha)) μ)
    (hbound : (∫ x : E, Real.exp ((‖x‖/k)^alpha) ∂μ) ≤ 2) :
    Integrable (fun x : E => ‖x‖^q) μ ∧
      (∫ x : E, ‖x‖^q ∂μ) ≤ 2*(k^q*(q/(alpha*Real.exp 1))^(q/alpha)) := by
  let B := k^q*(q/(alpha*Real.exp 1))^(q/alpha)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hm (x : E) : ‖x‖^q ≤ B*Real.exp ((‖x‖/k)^alpha) :=
    norm_power_exponential_majorant ‖x‖ k alpha q (norm_nonneg _) hk halpha hq
  have hi : Integrable (fun x : E => ‖x‖^q) μ :=
    (he.const_mul B).mono' ((measurable_norm.pow_const q).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun x => by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) q)] using hm x))
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ x, B*Real.exp ((‖x‖/k)^alpha) ∂μ := integral_mono hi (he.const_mul B) hm
    _ = B*(∫ x, Real.exp ((‖x‖/k)^alpha) ∂μ) := integral_const_mul _ _
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hbound hB]

/-- Exact source coefficient for converting an exponential moment to the
original all-real-order class. -/
noncomputable def sourceExponentialMomentCoefficient (alpha : ℝ) : ℝ :=
  2 * max 1 ((alpha * Real.exp 1)^(-1/alpha))

/-- The real q-th root of the exact scalar moment bound, for every q>=1. -/
theorem exp_moment_scalar_root_bound (k alpha q : ℝ)
    (hk : 0 < k) (halpha : 0 < alpha) (hq : 1 ≤ q) :
    (2*(k^q*(q/(alpha*Real.exp 1))^(q/alpha)))^q⁻¹ ≤
      sourceExponentialMomentCoefficient alpha*k*q^(1/alpha) := by
  have hq0 : 0 < q := by linarith
  have ha : 0 < alpha*Real.exp 1 := mul_pos halpha (Real.exp_pos _)
  have hb : 0 ≤ q/(alpha*Real.exp 1) := (div_pos hq0 ha).le
  have hroot : (2*(k^q*(q/(alpha*Real.exp 1))^(q/alpha)))^q⁻¹ =
      2^q⁻¹*k*(q/(alpha*Real.exp 1))^(1/alpha) := by
    rw [Real.mul_rpow (by norm_num) (by positivity),
      Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul hk.le, ← Real.rpow_mul hb]
    have h1 : q*q⁻¹=1 := mul_inv_cancel₀ hq0.ne'
    have h2 : q/alpha*q⁻¹=1/alpha := by field_simp
    rw [h1,h2,Real.rpow_one]
    ring
  have htwo : (2 : ℝ)^q⁻¹ ≤ 2 := by
    calc
      _ ≤ (2 : ℝ)^1 := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (inv_le_one_of_one_le₀ hq)
      _ = 2 := Real.rpow_one _
  have hfactor : (q/(alpha*Real.exp 1))^(1/alpha) =
      q^(1/alpha)*(alpha*Real.exp 1)^(-1/alpha) := by
    rw [Real.div_rpow hq0.le ha.le, neg_div,Real.rpow_neg ha.le]
    rfl
  rw [hroot,hfactor]
  have hmax := le_max_right (1 : ℝ) ((alpha*Real.exp 1)^(-1/alpha))
  dsimp [sourceExponentialMomentCoefficient]
  calc
    _ ≤ 2*k*(q^(1/alpha)*(alpha*Real.exp 1)^(-1/alpha)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htwo hk.le) (by positivity)
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_left hmax
        (show 0 ≤ 2*k*q^(1/alpha) by positivity)
      nlinarith [hm]

/-- A genuine exponential moment bounded by two implies exactly the source
all-real-q moment class, with its stated C_alpha times k coefficient. -/
theorem sourceMomentClass_of_exponential_moment [SecondCountableTopology E]
    (μ : Measure E) [IsProbabilityMeasure μ] (k alpha : ℝ)
    (hk : 0 < k) (halpha : 0 < alpha)
    (he : Integrable (fun x : E => Real.exp ((‖x‖/k)^alpha)) μ)
    (hbound : (∫ x : E, Real.exp ((‖x‖/k)^alpha) ∂μ) ≤ 2) :
    μ ∈ sourceMomentClass alpha (sourceExponentialMomentCoefficient alpha*k) := by
  have hC : 0 < sourceExponentialMomentCoefficient alpha := by
    dsimp [sourceExponentialMomentCoefficient]
    exact mul_pos (by norm_num) (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  apply (sourceMomentClass_iff_integrable_root_bound alpha _ (mul_pos hC hk) μ).mpr
  refine ⟨inferInstance,fun q hq => ?_⟩
  have hq0 : 0 < q := by linarith
  obtain ⟨hi,hb⟩ := integrable_norm_rpow_of_exp_moment μ k alpha q hk halpha hq0 he hbound
  refine ⟨hi,?_⟩
  exact (Real.rpow_le_rpow (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg x) q))
    hb (inv_nonneg.mpr hq0.le)).trans (exp_moment_scalar_root_bound k alpha q hk halpha hq)

end PaperFormalization.Manuscript
