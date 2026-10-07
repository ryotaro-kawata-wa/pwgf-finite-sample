import PaperFormalization.Manuscript.PopulationExponentialMarginal
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-! # A measurable prehistory population-eligibility event

Eligibility depends only on the actual population law supplied by the
prehistory kernel. Its nonnegative extended exponential integral prevents
undefined real integrals from passing the threshold. Eligibility implies the
source moment class, and the previously constructed population event implies
eligibility through an explicit equality of the actual pre-jump marginal.
The population event itself need not be prehistory-measurable. No Gaussian
law is conditioned on that event or on eligibility in these statements.
-/

open MeasureTheory ProbabilityTheory Set
namespace PaperFormalization.Manuscript

variable {S E : Type*} [MeasurableSpace S] [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E]

/-- An actual prehistory law has normalized exponential moment at most two.
The use of an extended nonnegative integral includes genuine finiteness. -/
noncomputable def populationExponentialEligibility (κ : Kernel S E) (alpha k : ℝ) : Set S :=
  {h | (∫⁻ x, ENNReal.ofReal (Real.exp ((‖x‖ / k) ^ alpha)) ∂κ h) ≤ 2}

/-- The eligibility set is measurable in the prehistory solely because κ is
its actual measurable population kernel. No all-real-q intersection is needed. -/
theorem measurableSet_populationExponentialEligibility (κ : Kernel S E) (alpha k : ℝ) :
    MeasurableSet (populationExponentialEligibility κ alpha k) := by
  have hf : Measurable (fun x : E => Real.exp ((‖x‖ / k) ^ alpha)) :=
    ((measurable_norm.div_const k).pow_const alpha).exp
  exact measurableSet_le hf.ennreal_ofReal.lintegral_kernel measurable_const

/-- Eligibility is exactly a genuine normalized exponential integral bound,
not a bound on Lean's zero value for a nonintegrable Bochner integral. -/
theorem mem_populationExponentialEligibility_iff (κ : Kernel S E) (alpha k : ℝ) (h : S) :
    h ∈ populationExponentialEligibility κ alpha k ↔
      Integrable (fun x : E => Real.exp ((‖x‖ / k) ^ alpha)) (κ h) ∧
        (∫ x : E, Real.exp ((‖x‖ / k) ^ alpha) ∂κ h) ≤ 2 := by
  let f : E → ℝ := fun x => Real.exp ((‖x‖ / k) ^ alpha)
  have hf : Measurable f := ((measurable_norm.div_const k).pow_const alpha).exp
  have hf0 : 0 ≤ᵐ[κ h] f := Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)
  change (∫⁻ x, ENNReal.ofReal (f x) ∂κ h) ≤ 2 ↔ Integrable f (κ h) ∧ (∫ x, f x ∂κ h) ≤ 2
  constructor
  · intro hb
    have hi : Integrable f (κ h) := ⟨hf.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hf0).mpr (hb.trans_lt (by norm_num))⟩
    refine ⟨hi,?_⟩
    rw [← ofReal_integral_eq_lintegral_ofReal hi hf0] at hb
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 2)).mp (by simpa using hb)
  · rintro ⟨hi,hb⟩
    rw [← ofReal_integral_eq_lintegral_ofReal hi hf0]
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hb

/-- On the history-local eligibility event, the unchanged population kernel
law satisfies the exact original all-real-order class with C_alpha*k. -/
theorem sourceMomentClass_of_populationExponentialEligibility [SecondCountableTopology E]
    (κ : Kernel S E) [IsMarkovKernel κ] (alpha k : ℝ)
    (halpha : 0 < alpha) (hk : 0 < k) (h : S)
    (helig : h ∈ populationExponentialEligibility κ alpha k) :
    κ h ∈ sourceMomentClass alpha (sourceExponentialMomentCoefficient alpha * k) := by
  obtain ⟨hi,hb⟩ := (mem_populationExponentialEligibility_iff κ alpha k h).mp helig
  exact sourceMomentClass_of_exponential_moment (κ h) k alpha hk halpha hi hb

/-- A normalized exponential bound under the actual population path law
implies prehistory eligibility once that evaluation's pushforward is exactly
the pre-jump kernel law. No relation between their conditioning sigma-fields
is inferred from that equality. -/
theorem population_marginal_mem_exponentialEligibility
    {P : Type*} [MeasurableSpace P] (κ : Kernel S E) (alpha k : ℝ) (h : S)
    (μ : Measure P) (X : P → E) (hX : Measurable X) (hLaw : κ h = μ.map X)
    (hi : Integrable (fun path => Real.exp ((‖X path‖ / k) ^ alpha)) μ)
    (hb : (∫ path, Real.exp ((‖X path‖ / k) ^ alpha) ∂μ) ≤ 2) :
    h ∈ populationExponentialEligibility κ alpha k := by
  apply (mem_populationExponentialEligibility_iff κ alpha k h).mpr
  have hf : Measurable (fun x : E => Real.exp ((‖x‖ / k) ^ alpha)) :=
    ((measurable_norm.div_const k).pow_const alpha).exp
  rw [hLaw]
  refine ⟨(integrable_map_measure hf.aestronglyMeasurable hX.aemeasurable).mpr hi,?_⟩
  simpa only [integral_map hX.aemeasurable hf.aestronglyMeasurable] using hb

/-- A possibly future-dependent population event is contained in the pullback
of the measurable prehistory eligibility set through actual pre-law identities.
There is deliberately no measurability or independence hypothesis on Good. -/
theorem population_event_subset_prehistory_exponentialEligibility
    {O P : Type*} [MeasurableSpace P]
    (κ : Kernel S E) (alpha k : ℝ) (history : O → S) (Good : Set O)
    (μ : O → Measure P) (X : O → P → E)
    (hX : ∀ ω ∈ Good, Measurable (X ω))
    (hLaw : ∀ ω ∈ Good, κ (history ω) = (μ ω).map (X ω))
    (hbound : ∀ ω ∈ Good,
      Integrable (fun path => Real.exp ((‖X ω path‖ / k) ^ alpha)) (μ ω) ∧
        (∫ path, Real.exp ((‖X ω path‖ / k) ^ alpha) ∂μ ω) ≤ 2) :
    Good ⊆ history ⁻¹' populationExponentialEligibility κ alpha k := by
  intro ω hω
  exact population_marginal_mem_exponentialEligibility κ alpha k (history ω)
    (μ ω) (X ω) (hX ω hω) (hLaw ω hω) (hbound ω hω).1 (hbound ω hω).2

end PaperFormalization.Manuscript
