import PaperFormalization.Manuscript.KernelClippedResidual

/-! # Joint measurability of the actual untruncated kernel-centered residual

No convergence assumption is needed solely for scalar measurability of the
totalized series; actual source convergence is established separately before
any estimate or analytic use. The original population law is unchanged.
-/
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
namespace PaperFormalization.Manuscript
variable {G Ω E : Type*} [MeasurableSpace G] [MeasurableSpace Ω]
  [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] {N : ℕ}

/-- Actual untruncated countable kernel-centered residuals are jointly
measurable even without separability of the whole feature target. -/
theorem measurable_kernel_weightedSampleResidual
    (κ : Kernel G E) (X : G × Ω → Fin N → E)
    (hX : ∀ i, Measurable (fun z => X z i)) (w : ℕ → ℝ≥0)
    (φ : ∀ n, E → H n) (hφ : ∀ n, Continuous (φ n)) :
    Measurable (fun z : G × Ω => weightedSampleResidual w φ
      (fun n => ∫ x, φ n x ∂κ z.1) (X z)) := by
  change Measurable (fun z : G × Ω => ∑' n, (w n : ℝ) *
    ‖(N : ℝ)⁻¹ • ∑ i, φ n (X z i) - ∫ x, φ n x ∂κ z.1‖)
  apply Measurable.tsum
  intro n
  have hp : StronglyMeasurable (fun h : G => ∫ x, φ n x ∂κ h) :=
    (hφ n).stronglyMeasurable.integral_kernel
  have he : StronglyMeasurable (fun z : G × Ω => (N : ℝ)⁻¹ • ∑ i, φ n (X z i)) :=
    (Finset.stronglyMeasurable_fun_sum Finset.univ (fun i _ =>
      (hφ n).comp_stronglyMeasurable (hX i).stronglyMeasurable)).const_smul _
  exact measurable_const.mul (he.sub (hp.comp_measurable measurable_fst)).norm.measurable
end PaperFormalization.Manuscript
