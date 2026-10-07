import PaperFormalization.Manuscript.ExponentialMomentClass
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.MeanInequalitiesPow

/-! # Genuine exponential normalization and all-time population transfer

The same probability law is retained throughout. Bounds at a nearby node
are transferred using an actual almost-everywhere norm displacement; the
normalization uses Jensen with genuine integrability established first.
-/
open MeasureTheory Set
open scoped NNReal
namespace PaperFormalization.Manuscript

/-- Jensen normalization at the exact exponent log(2)/log(M). -/
theorem integrable_exp_normalized_le_two {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (M : ℝ)
    (hf : Measurable f) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hi : Integrable (fun x => Real.exp (f x)) μ)
    (hM : 2 ≤ M) (hb : (∫ x, Real.exp (f x) ∂μ) ≤ M) :
    Integrable (fun x => Real.exp (f x*(Real.log 2/Real.log M))) μ ∧
      (∫ x, Real.exp (f x*(Real.log 2/Real.log M)) ∂μ) ≤ 2 := by
  let eta := Real.log 2/Real.log M
  have hM0 : 0 < M := by linarith
  have hlog : 0 < Real.log M := Real.log_pos (by linarith)
  have he0 : 0 < eta := div_pos (Real.log_pos (by norm_num)) hlog
  have he1 : eta ≤ 1 := (div_le_one hlog).mpr
    (Real.log_le_log (by norm_num) hM)
  have hid (x : Ω) : (Real.exp (f x))^eta = Real.exp (f x*eta) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
  have hsmall : Integrable (fun x => Real.exp (f x*eta)) μ :=
    hi.mono' ((hf.mul_const eta).exp.aestronglyMeasurable)
      (hf0.mono (fun x hx => by
        rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (mul_le_of_le_one_right hx he1)))
  have hj := (Real.concaveOn_rpow he0.le he1).le_map_integral
    (Real.continuous_rpow_const he0.le).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos (f x)).le)) hi
    (show Integrable ((fun y : ℝ => y^eta) ∘ (fun x => Real.exp (f x))) μ from
      hsmall.congr (Filter.Eventually.of_forall (fun x => (hid x).symm)))
  refine ⟨hsmall,?_⟩
  have hpower : M^eta=2 := by
    rw [Real.rpow_def_of_pos hM0]
    have hc : Real.log M*eta=Real.log 2 := by dsimp [eta];field_simp
    rw [hc,Real.exp_log (by norm_num)]
  calc
    _ = ∫ x, (Real.exp (f x))^eta ∂μ := integral_congr_ae
      (Filter.Eventually.of_forall (fun x => (hid x).symm))
    _ ≤ (∫ x, Real.exp (f x) ∂μ)^eta := hj
    _ ≤ M^eta := Real.rpow_le_rpow (integral_nonneg (fun x => (Real.exp_pos _).le)) hb he0.le
    _ = 2 := hpower

/-- Exact source factor for the positive-part power inequality. -/
noncomputable def sourcePopulationFlowFactor (alpha : ℝ) : ℝ := 2^(max (alpha-1) 0)

/-- The scalar two-point power inequality retains the exact c_alpha. -/
theorem source_population_add_rpow_bound (u v alpha : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (ha : 0 ≤ alpha) :
    (u+v)^alpha ≤ sourcePopulationFlowFactor alpha*(u^alpha+v^alpha) := by
  by_cases ha1 : alpha ≤ 1
  · simp only [sourcePopulationFlowFactor,max_eq_right (by linarith : alpha-1 ≤ 0),
      Real.rpow_zero,one_mul]
    exact Real.rpow_add_le_add_rpow hu hv ha ha1
  · have hn := NNReal.rpow_add_le_mul_rpow_add_rpow (⟨u,hu⟩ : ℝ≥0) (⟨v,hv⟩ : ℝ≥0)
      (show 1 ≤ alpha by linarith)
    have he : max (alpha-1) 0 = alpha-1 := max_eq_left (by linarith)
    dsimp [sourcePopulationFlowFactor]
    rw [he]
    exact_mod_cast hn


/-- A genuine conditional node moment propagates under the same path law
when the actual norm displacement to that node is at most one. -/
theorem integrable_exp_population_flow {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) (X Y : Ω → E) (b alpha A : ℝ)
    (hb : 0 < b) (ha : 0 < alpha) (hX : Measurable X)
    (hshift : ∀ᵐ x ∂μ, ‖X x‖ ≤ ‖Y x‖+1)
    (hi : Integrable (fun x => Real.exp (‖Y x‖^alpha/b^alpha)) μ)
    (hA : (∫ x, Real.exp (‖Y x‖^alpha/b^alpha) ∂μ) ≤ A) :
    Integrable (fun x => Real.exp (‖X x‖^alpha/
      (sourcePopulationFlowFactor alpha*b^alpha))) μ ∧
    (∫ x, Real.exp (‖X x‖^alpha/(sourcePopulationFlowFactor alpha*b^alpha)) ∂μ) ≤
      A*Real.exp (b^(-alpha)) := by
  have hc : 0 < sourcePopulationFlowFactor alpha := by
    dsimp [sourcePopulationFlowFactor];positivity
  have hbp : 0 < b^alpha := Real.rpow_pos_of_pos hb _
  have hdom : ∀ᵐ x ∂μ,
      Real.exp (‖X x‖^alpha/(sourcePopulationFlowFactor alpha*b^alpha)) ≤
        Real.exp (b^(-alpha))*Real.exp (‖Y x‖^alpha/b^alpha) := by
    filter_upwards [hshift] with x hx
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hp := (Real.rpow_le_rpow (norm_nonneg _) hx ha.le).trans
      (source_population_add_rpow_bound ‖Y x‖ 1 alpha (norm_nonneg _) (by norm_num) ha.le)
    rw [Real.one_rpow] at hp
    rw [Real.rpow_neg hb.le]
    apply (div_le_iff₀ (mul_pos hc hbp)).mpr
    have he : ((b^alpha)⁻¹+‖Y x‖^alpha/b^alpha)*
      (sourcePopulationFlowFactor alpha*b^alpha) =
      sourcePopulationFlowFactor alpha*(‖Y x‖^alpha+1) := by field_simp;ring
    rw [he]
    exact hp
  have hxmeas : Measurable (fun x => Real.exp (‖X x‖^alpha/
      (sourcePopulationFlowFactor alpha*b^alpha))) :=
    ((hX.norm.pow_const alpha).div_const _).exp
  have hix := (hi.const_mul (Real.exp (b^(-alpha)))).mono' hxmeas.aestronglyMeasurable
    (hdom.mono (fun x hx => by simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hx))
  refine ⟨hix,?_⟩
  calc
    _ ≤ ∫ x, Real.exp (b^(-alpha))*Real.exp (‖Y x‖^alpha/b^alpha) ∂μ :=
      integral_mono_ae hix (hi.const_mul _) hdom
    _ = Real.exp (b^(-alpha))*(∫ x, Real.exp (‖Y x‖^alpha/b^alpha) ∂μ) :=
      integral_const_mul _ _
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hA (Real.exp_pos (b^(-alpha))).le]


/-- Literal population normalization scale from the manuscript. -/
noncomputable def sourcePopulationNormalizedScale (alpha b A : ℝ) : ℝ :=
  (sourcePopulationFlowFactor alpha/Real.log 2*(b^alpha*Real.log A+1))^(1/alpha)

/-- The exact kth-power identity defining the normalized population scale. -/
theorem sourcePopulationNormalizedScale_pow (alpha b A : ℝ)
    (ha : 0 < alpha) (hb : 0 < b) (hA : 2 ≤ A) :
    0 < sourcePopulationNormalizedScale alpha b A ∧
    (sourcePopulationNormalizedScale alpha b A)^alpha =
      sourcePopulationFlowFactor alpha/Real.log 2*(b^alpha*Real.log A+1) := by
  have hlogA : 0 < Real.log A := Real.log_pos (by linarith)
  have hc : 0 < sourcePopulationFlowFactor alpha := by dsimp [sourcePopulationFlowFactor];positivity
  have hp : 0 < sourcePopulationFlowFactor alpha/Real.log 2*(b^alpha*Real.log A+1) :=
    mul_pos (div_pos hc (Real.log_pos (by norm_num))) (by positivity)
  refine ⟨Real.rpow_pos_of_pos hp _,?_⟩
  rw [sourcePopulationNormalizedScale,← Real.rpow_mul hp.le]
  have he : 1/alpha*alpha=1 := by field_simp
  rw [he,Real.rpow_one]

/-- Fixed-scale moment amplitude has exactly the normalized source scale;
Jensen supplies genuine integrability before the all-real-order conversion. -/
theorem integrable_exp_population_normalized {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (b alpha A : ℝ)
    (hb : 0 < b) (ha : 0 < alpha) (hA : 2 ≤ A) (hX : Measurable X)
    (hi : Integrable (fun x => Real.exp (‖X x‖^alpha/
      (sourcePopulationFlowFactor alpha*b^alpha))) μ)
    (hbound : (∫ x, Real.exp (‖X x‖^alpha/(sourcePopulationFlowFactor alpha*b^alpha)) ∂μ) ≤
      A*Real.exp (b^(-alpha))) :
    Integrable (fun x => Real.exp ((‖X x‖/sourcePopulationNormalizedScale alpha b A)^alpha)) μ ∧
      (∫ x, Real.exp ((‖X x‖/sourcePopulationNormalizedScale alpha b A)^alpha) ∂μ) ≤ 2 := by
  let M := A*Real.exp (b^(-alpha))
  have hA0 : 0 < A := by linarith
  have hbp : 0 < b^alpha := Real.rpow_pos_of_pos hb _
  have hc : 0 < sourcePopulationFlowFactor alpha := by dsimp [sourcePopulationFlowFactor];positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogA : 0 < Real.log A := Real.log_pos (by linarith)
  have hM : 2 ≤ M := by
    have he : 1 ≤ Real.exp (b^(-alpha)) := Real.one_le_exp (by positivity)
    dsimp [M]
    nlinarith [mul_le_mul_of_nonneg_left he hA0.le]
  have hlog : Real.log M = Real.log A+(b^alpha)⁻¹ := by
    dsimp [M]
    rw [Real.log_mul hA0.ne' (Real.exp_pos _).ne',Real.log_exp,Real.rpow_neg hb.le]
  obtain ⟨hk,hkpow⟩ := sourcePopulationNormalizedScale_pow alpha b A ha hb hA
  have hid (x : Ω) :
      (‖X x‖/sourcePopulationNormalizedScale alpha b A)^alpha =
      (‖X x‖^alpha/(sourcePopulationFlowFactor alpha*b^alpha))*(Real.log 2/Real.log M) := by
    rw [Real.div_rpow (norm_nonneg _) hk.le,hkpow,hlog]
    field_simp
  have hresult := integrable_exp_normalized_le_two μ
    (fun x => ‖X x‖^alpha/(sourcePopulationFlowFactor alpha*b^alpha)) M
    ((hX.norm.pow_const alpha).div_const _) (Filter.Eventually.of_forall (fun x => by positivity))
    hi hM hbound
  simpa only [← hid] using hresult

end PaperFormalization.Manuscript
