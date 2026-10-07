import PaperFormalization.Manuscript.PopulationExponentialFlow

/-! # Actual population marginal class and fixed-scale amplitude

These adapters keep the original conditional path law and identify its actual
pushforward marginal. Constants match the population-localization formulas.
-/
open MeasureTheory Set
namespace PaperFormalization.Manuscript

/-- The literal fixed-scale amplitude is at most e times its grid threshold. -/
theorem source_population_amplitude_le (b alpha A : ℝ)
    (hb : 1 ≤ b) (ha : 0 ≤ alpha) (hA : 0 ≤ A) :
    A*Real.exp (b^(-alpha)) ≤ A*Real.exp 1 := by
  have hp : b^(-alpha) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hb (by linarith)
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hp) hA

/-- The source fixed-scale exponent is exactly a positive multiple of the
unconditional-K norm power used by the clipping-bias estimate. -/
theorem source_population_fixed_exponent (alpha b K u : ℝ)
    (hb : 0 < b) (hK : 0 < K) (hu : 0 ≤ u) :
    0 < K^alpha/(sourcePopulationFlowFactor alpha*b^alpha) ∧
    u^alpha/(sourcePopulationFlowFactor alpha*b^alpha) =
      (K^alpha/(sourcePopulationFlowFactor alpha*b^alpha))*(u/K)^alpha := by
  have hc : 0 < sourcePopulationFlowFactor alpha := by dsimp [sourcePopulationFlowFactor];positivity
  constructor
  · positivity
  · rw [Real.div_rpow hu hK.le]
    field_simp

/-- A normalized exponential moment under the actual path law gives the
original moment class for its pushforward, without a root-integral premise. -/
theorem sourceMomentClass_map_of_exponential_moment
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E)
    (k alpha : ℝ) (hk : 0 < k) (ha : 0 < alpha) (hX : Measurable X)
    (hi : Integrable (fun x => Real.exp ((‖X x‖/k)^alpha)) μ)
    (hb : (∫ x, Real.exp ((‖X x‖/k)^alpha) ∂μ) ≤ 2) :
    μ.map X ∈ sourceMomentClass alpha (sourceExponentialMomentCoefficient alpha*k) := by
  letI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hf : Measurable (fun y : E => Real.exp ((‖y‖/k)^alpha)) :=
    ((measurable_norm.div_const k).pow_const alpha).exp
  apply sourceMomentClass_of_exponential_moment (μ.map X) k alpha hk ha
  · exact (integrable_map_measure hf.aestronglyMeasurable hX.aemeasurable).mpr hi
  · simpa only [integral_map hX.aemeasurable hf.aestronglyMeasurable] using hb
end PaperFormalization.Manuscript
