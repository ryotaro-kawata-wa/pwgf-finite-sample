import PaperFormalization.Manuscript.ClippedConcentrationThreshold
import PaperFormalization.Manuscript.JointWhitenedSeed
import Mathlib.Probability.Kernel.MeasurableIntegral

/-! # Actual measurable clipped statistics with a population kernel

Measurability of the countable statistic and its random population centers
is derived before integrating original conditional node budgets. Population
eligibility restricts the event, never the sampling law.
-/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ProbabilityTheory
namespace PaperFormalization.Manuscript
variable {G Ω E : Type*} [MeasurableSpace G] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] {N : ℕ}

/-- Actual kernel-centered clipped residuals are jointly measurable, without
whole-feature-target separability or a measurability premise for the residual. -/
theorem measurable_kernel_weightedClippedSampleResidual
    (κ : Kernel G E) (X : G × Ω → Fin N → E) (hX : ∀ i, Measurable (fun z => X z i))
    (D : ℝ) (hD : 0 ≤ D) (w : ℕ → ℝ≥0)
    (φ : ∀ n, E → H n) (hφ : ∀ n, Continuous (φ n)) :
    Measurable (fun z : G × Ω => weightedClippedSampleResidual (κ z.1) D w φ (X z)) := by
  change Measurable (fun z : G × Ω => ∑' n, (w n : ℝ) *
    ‖(N : ℝ)⁻¹ • ∑ i, φ n (sourceRadialClip D (X z i)) -
      ∫ x, φ n (sourceRadialClip D x) ∂κ z.1‖)
  apply Measurable.tsum
  intro n
  have hc : Continuous (fun x => φ n (sourceRadialClip D x)) :=
    (hφ n).comp (sourceRadialClip_continuous D hD)
  have hp : StronglyMeasurable (fun h : G => ∫ x, φ n (sourceRadialClip D x) ∂κ h) :=
    hc.stronglyMeasurable.integral_kernel
  have he : StronglyMeasurable (fun z : G × Ω =>
      (N : ℝ)⁻¹ • ∑ i, φ n (sourceRadialClip D (X z i))) :=
    (Finset.stronglyMeasurable_fun_sum Finset.univ (fun i _ =>
      hc.comp_stronglyMeasurable (hX i).stronglyMeasurable)).const_smul _
  exact measurable_const.mul (he.sub (hp.comp_measurable measurable_fst)).norm.measurable

variable [∀ n, CompleteSpace (H n)]

/-- A jointly measurable actual node failure inherits p/Q under the original
history/kernel joint law. Iid sampling is only required on eligible histories. -/
theorem joint_kernel_clipped_source_node_budget
    (ρ : Measure G) [IsProbabilityMeasure ρ]
    (k : Kernel G Ω) [IsMarkovKernel k] (κ : Kernel G E) [IsMarkovKernel κ]
    (PopGood : Set G) (hPopGood : MeasurableSet PopGood)
    (X : G × Ω → Fin N → E) (hX : ∀ i, Measurable (fun z => X z i)) (hN : 0 < N)
    (hLaw : ∀ᵐ h ∂ρ, h ∈ PopGood → ∀ i, (k h).map (fun ω => X (h,ω) i) = κ h)
    (hind : ∀ᵐ h ∂ρ, h ∈ PopGood → iIndepFun (fun i ω => X (h,ω) i) (k h))
    (D : ℝ) (hD : 0 ≤ D) (w : ℕ → ℝ≥0) (L : ℕ → ℝ) (m : ℕ → ℕ)
    (hL : ∀ n, 0 ≤ L n) (φ : ∀ n, E → H n) (hφ : ∀ n, Continuous (φ n))
    (hg : ∀ n x, ‖φ n x‖ ≤ L n * (1 + ‖x‖ ^ m n))
    (hsum : Summable (fun n => (w n : ℝ) * (L n * (1 + D ^ m n))))
    (Q p : ℝ) (hQ : 0 < Q) (hp : 0 < p) (hpQ : p < Q) :
    let A := 2 * ∑' n, (w n : ℝ) * (L n * (1 + D ^ m n))
    (ρ ⊗ₘ k).real {z | z.1 ∈ PopGood ∧
      A / Real.sqrt N + A * Real.sqrt (Real.log (Q/p)/(2*N)) <
        weightedClippedSampleResidual (κ z.1) D w φ (X z)} ≤ p/Q := by
  let A := 2 * ∑' n, (w n : ℝ) * (L n * (1 + D ^ m n))
  let r := A / Real.sqrt N + A * Real.sqrt (Real.log (Q/p)/(2*N))
  let Bad : Set (G × Ω) := {z | z.1 ∈ PopGood ∧ r < weightedClippedSampleResidual (κ z.1) D w φ (X z)}
  have hBad : MeasurableSet Bad := (hPopGood.preimage measurable_fst).inter
    (measurableSet_lt measurable_const (measurable_kernel_weightedClippedSampleResidual κ X hX D hD w φ hφ))
  have hc : ∀ᵐ h ∂ρ, k h (Prod.mk h ⁻¹' Bad) ≤ ENNReal.ofReal (p/Q) := by
    filter_upwards [hLaw,hind] with h hLawh hindh
    by_cases hh : h ∈ PopGood
    · have hb := weightedClippedSampleResidual_iid_source_threshold hN (κ h) (k h)
        (fun i ω => X (h,ω) i) (hLawh hh) (hindh hh) D hD w L m hL φ hφ hg hsum Q p hQ hp hpQ
      have he : Prod.mk h ⁻¹' Bad = {ω | r < weightedClippedSampleResidual (κ h) D w φ (X (h,ω))} := by
        ext ω
        simp only [Bad, mem_preimage, mem_setOf_eq, hh, true_and]
      rw [he]
      rw [← ofReal_measureReal (μ := k h) (s := {ω | r < weightedClippedSampleResidual (κ h) D w φ (X (h,ω))})]
      exact ENNReal.ofReal_le_ofReal hb
    · have he : Prod.mk h ⁻¹' Bad = ∅ := by
        ext ω
        simp only [Bad, mem_preimage, mem_setOf_eq, hh, false_and, mem_empty_iff_false]
      rw [he, measure_empty]
      positivity
  have hj := joint_kernel_failure_budget ρ k Bad hBad (fun _ => ENNReal.ofReal (p/Q)) hc
  have hj' : (ρ ⊗ₘ k) Bad ≤ ENNReal.ofReal (p/Q) := by simpa using hj
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hj'
  change (ρ ⊗ₘ k).real Bad ≤ p/Q
  simpa only [measureReal_def, ENNReal.toReal_ofReal (div_nonneg hp.le hQ.le)] using ht
end PaperFormalization.Manuscript
