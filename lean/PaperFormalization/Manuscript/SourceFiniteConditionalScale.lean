import PaperFormalization.Manuscript.PopulationExponentialFlow
import PaperFormalization.Manuscript.SourceExponentialMoment
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! # Almost-sure finite population scales, before any localization

M13q verified unit (see CODEX_HANDOFF_M13Q.md). Genuine unconditional exponential integrability
implies a finite (history-dependent) all-real-order scale almost surely. This is
NOT an almost-sure deterministic K0 bound and consumes no probability budget.
It is used only to put actual population moments in the original all-K domain.
-/
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
namespace PaperFormalization.Manuscript
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

/-- A genuinely finite exponential moment admits some finite source-class
scale. Jensen normalization is applied only after integrability is supplied. -/
theorem source_exists_finite_scale_of_integrable_exp
    (mu : Measure E) [IsProbabilityMeasure mu] (alpha b : Real)
    (halpha : 0 < alpha) (hb : 0 < b)
    (hi : Integrable (fun x : E => Real.exp (norm x ^ alpha / b ^ alpha)) mu) :
    ∃ K : Real, 0 < K ∧ mu ∈ sourceMomentClass alpha K := by
  let M : Real := max 2 (∫ x : E, Real.exp (norm x ^ alpha / b ^ alpha) ∂mu)
  have hM : 2 ≤ M := le_max_left _ _
  have hlogM : 0 < Real.log M := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let a : Real := Real.log M / Real.log 2
  let scale : Real := b * a ^ (1 / alpha)
  have ha : 0 < a := div_pos hlogM hlog2
  have hscale : 0 < scale := mul_pos hb (Real.rpow_pos_of_pos ha _)
  have hscalePow : scale ^ alpha = b ^ alpha * a := by
    dsimp only [scale]
    rw [Real.mul_rpow hb.le (Real.rpow_nonneg ha.le _), ← Real.rpow_mul ha.le]
    have he : (1 / alpha) * alpha = 1 := by field_simp [ne_of_gt halpha]
    rw [he, Real.rpow_one]
  have heq (x : E) : (norm x / scale) ^ alpha =
      (norm x ^ alpha / b ^ alpha) * (Real.log 2 / Real.log M) := by
    rw [Real.div_rpow (norm_nonneg _) hscale.le, hscalePow]
    dsimp only [a]
    field_simp [ne_of_gt hlogM, ne_of_gt hlog2, ne_of_gt (Real.rpow_pos_of_pos hb alpha)]
  have hnorm := integrable_exp_normalized_le_two mu
    (fun x : E => norm x ^ alpha / b ^ alpha) M
    ((measurable_norm.pow_const alpha).div_const _)
    (Filter.Eventually.of_forall (fun x => by positivity)) hi hM (le_max_right _ _)
  have hi' : Integrable (fun x : E => Real.exp ((norm x / scale) ^ alpha)) mu := by
    simpa only [heq] using hnorm.1
  have hb' : (∫ x : E, Real.exp ((norm x / scale) ^ alpha) ∂mu) ≤ 2 := by
    simpa only [heq] using hnorm.2
  refine ⟨sourceExponentialMomentCoefficient alpha * scale, ?_, ?_⟩
  · apply mul_pos _ hscale
    unfold sourceExponentialMomentCoefficient
    positivity
  · exact sourceMomentClass_of_exponential_moment mu scale alpha hscale halpha hi' hb'

/-- Fubini gives genuine conditional exponential integrability on one AE
history set. Neither the conditional law nor the original measure is restricted. -/
theorem source_ae_finite_scale_of_joint_exp
    {S : Type*} [MeasurableSpace S] (rho : Measure S) [IsProbabilityMeasure rho]
    (kappa : Kernel S E) [IsMarkovKernel kappa] (alpha b : Real)
    (halpha : 0 < alpha) (hb : 0 < b)
    (hi : Integrable (fun z : S × E =>
      Real.exp (norm z.2 ^ alpha / b ^ alpha)) (rho ⊗ₘ kappa)) :
     ∀ᵐ h ∂rho, ∃ K : Real, 0 < K ∧ kappa h ∈ sourceMomentClass alpha K := by
  have hc := (Measure.integrable_compProd_iff hi.aestronglyMeasurable).mp hi
  filter_upwards [hc.1] with h hh
  exact source_exists_finite_scale_of_integrable_exp (kappa h) alpha b halpha hb hh

/-- The original unconditional all-real-order marginal assumption suffices for
AE finite conditional scales. This does NOT assume conditional moments with the
original deterministic K0, or condition the sample law on a good event. -/
theorem source_ae_finite_scale_of_mixture_class
    {S : Type*} [MeasurableSpace S] (rho : Measure S) [IsProbabilityMeasure rho]
    (kappa : Kernel S E) [IsMarkovKernel kappa] (alpha K0 : Real)
    (halpha : 0 < alpha) (hK0 : 0 < K0)
    (hclass : (rho ⊗ₘ kappa).map (Prod.snd : S × E -> E) ∈
      sourceMomentClass alpha K0) :
     ∀ᵐ h ∂rho, ∃ K : Real, 0 < K ∧ kappa h ∈ sourceMomentClass alpha K := by
  let b := sourcePopulationExponentialScale alpha K0
  have hb : 0 < b := lt_of_lt_of_le (by norm_num : (0 : Real) < 1) (le_max_left _ _)
  have hf : Measurable (fun x : E => Real.exp (norm x ^ alpha / b ^ alpha)) :=
    ((measurable_norm.pow_const alpha).div_const _).exp
  have hm := sourceMomentClass_integrable_exp_and_integral_le_two alpha K0 halpha hK0 _ hclass
  have hi : Integrable (fun z : S × E => Real.exp (norm z.2 ^ alpha / b ^ alpha))
      (rho ⊗ₘ kappa) :=
    (integrable_map_measure hf.aestronglyMeasurable measurable_snd.aemeasurable).mp hm.1
  exact source_ae_finite_scale_of_joint_exp rho kappa alpha b halpha hb hi

end PaperFormalization.Manuscript
