import Mathlib.Probability.Moments.SubGaussian

/-! # Exact Hoeffding parameter from literal oscillation

A one-coordinate replacement bound controls the full range width by c, not
2c. The interval is constructed from the actual range infimum; no exponential
moment or tail estimate is a hypothesis.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace PaperFormalization.Manuscript

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A measurable scalar random variable whose actual pairwise oscillation is
at most c has centered sub-Gaussian parameter exactly c²/4. -/
theorem hasSubgaussianMGF_centered_of_oscillation
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (c : ℝ≥0)
    (hf : AEMeasurable f μ) (hosc : ∀ x y, |f x - f y| ≤ c) :
    HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂μ) ((c / 2) ^ 2) μ := by
  letI : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  let x₀ : Ω := Classical.choice inferInstance
  have hnonempty : (range f).Nonempty := ⟨f x₀, mem_range_self x₀⟩
  have hbelow : BddBelow (range f) := by
    refine ⟨f x₀ - c, ?_⟩
    rintro z ⟨x, rfl⟩
    have h := (abs_le.mp (hosc x₀ x)).2
    linarith
  have hrange (x : Ω) : f x ∈ Icc (sInf (range f)) (sInf (range f) + c) := by
    refine ⟨csInf_le hbelow (mem_range_self x), ?_⟩
    have hlower : f x - c ≤ sInf (range f) := by
      apply le_csInf hnonempty
      rintro z ⟨y, rfl⟩
      have h := (abs_le.mp (hosc x y)).2
      linarith
    linarith
  have hs := hasSubgaussianMGF_of_mem_Icc hf (Filter.Eventually.of_forall hrange)
  have hn : ‖(sInf (range f) + (c : ℝ)) - sInf (range f)‖₊ = c := by
    simp
  simpa only [hn] using hs

end PaperFormalization.Manuscript
