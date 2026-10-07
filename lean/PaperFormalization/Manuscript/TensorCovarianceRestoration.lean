import PaperFormalization.Manuscript.ClippedTensorConcentration

/-! # Restore actual covariance tensors under the original law

Concentration precedes intersection with the sampled-energy event. The
population bias is deterministic and has coefficient one. Its tail budget
therefore adds no failure event.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace PaperFormalization.Manuscript

variable {E H ι Ω : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype ι] [DecidableEq ι]
  {N : ℕ}

/-- The original covariance and sampled-energy maximum simultaneously satisfy
the exact source threshold, with total failure at most delta/4. Both tail
inputs refer to the original laws, and no independence after intersection is used. -/
theorem covariance_sample_max_and_error_failure_le (hN : 0 < N)
    (μ : Measure E) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (Y : Fin N → Ω → E) (hLaw : ∀ i, ν.map (Y i) = μ) (hind : iIndepFun Y ν)
    (A : E → (EuclideanSpace ℝ ι →L[ℝ] H)) (hA : Continuous A)
    (tau C4 delta : ℝ) (htau : 0 ≤ tau) (hdelta : 0 < delta) (hdelta8 : delta < 8)
    (hfour : Integrable (fun x => finiteHilbertSchmidtNorm (A x) ^ 4) μ)
    (hC4 : (∫ x, finiteHilbertSchmidtNorm (A x) ^ 4 ∂μ) ≤ C4)
    (hTail : μ.real {x | tau < finiteHilbertSchmidtNorm (A x) ^ 2} ≤ delta / (8 * N))
    (hMax : ν.real {ω | ∃ i, tau < finiteHilbertSchmidtNorm (A (Y i ω)) ^ 2} ≤ delta / 8) :
    ν.real {ω | (∃ i, tau < finiteHilbertSchmidtNorm (A (Y i ω)) ^ 2) ∨
      Real.sqrt C4 / Real.sqrt N * (1 + Real.sqrt (delta / 8)) +
        tau * Real.sqrt (2 * Real.log (8 / delta) / N) <
      ‖(N : ℝ)⁻¹ • ∑ i, finiteOperatorCovariance (A (Y i ω)) -
        ∫ x, finiteOperatorCovariance (A x) ∂μ‖} ≤ delta / 4 := by
  let MaxBad := {ω | ∃ i, tau < finiteHilbertSchmidtNorm (A (Y i ω)) ^ 2}
  let ClipBad := {ω | Real.sqrt (C4 / N) + tau * Real.sqrt (2 * Real.log (8 / delta) / N) <
    energyClippedCovarianceError μ A tau (fun i => Y i ω)}
  have hclip : ν.real ClipBad ≤ delta / 8 :=
    energyClippedCovarianceError_iid_source_threshold hN μ ν Y hLaw hind A hA tau C4 delta
      htau hdelta hdelta8 hfour hC4
  have hC0 : 0 ≤ C4 := (integral_nonneg (fun x => pow_nonneg
    (finiteHilbertSchmidtNorm_nonneg (A x)) 4)).trans hC4
  have hbias : Real.sqrt C4 * Real.sqrt (μ.real {x | tau < finiteHilbertSchmidtNorm (A x) ^ 2}) ≤
      Real.sqrt C4 * Real.sqrt (delta / (8 * N)) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hTail) (Real.sqrt_nonneg _)
  have hformula : Real.sqrt (C4 / N) + tau * Real.sqrt (2 * Real.log (8 / delta) / N) +
      Real.sqrt C4 * Real.sqrt (delta / (8 * N)) =
      Real.sqrt C4 / Real.sqrt N * (1 + Real.sqrt (delta / 8)) +
        tau * Real.sqrt (2 * Real.log (8 / delta) / N) := by
    rw [show delta / (8 * (N : ℝ)) = (delta / 8) / N by ring,
      Real.sqrt_div hC0, Real.sqrt_div (div_nonneg hdelta.le (by norm_num))]
    ring
  have hsubset : {ω | (∃ i, tau < finiteHilbertSchmidtNorm (A (Y i ω)) ^ 2) ∨
      Real.sqrt C4 / Real.sqrt N * (1 + Real.sqrt (delta / 8)) +
        tau * Real.sqrt (2 * Real.log (8 / delta) / N) <
      ‖(N : ℝ)⁻¹ • ∑ i, finiteOperatorCovariance (A (Y i ω)) -
        ∫ x, finiteOperatorCovariance (A x) ∂μ‖} ⊆ MaxBad ∪ ClipBad := by
    intro ω hω
    by_cases hmax : ω ∈ MaxBad
    · exact Or.inl hmax
    right
    have hy (i : Fin N) : finiteHilbertSchmidtNorm (A (Y i ω)) ^ 2 ≤ tau := by
      by_contra hi
      exact hmax ⟨i, lt_of_not_ge hi⟩
    have hraw := covariance_error_le_energyClipped_error_add_bias μ A hA tau C4 hfour hC4
      (fun i => Y i ω) hy
    have herr := hω.resolve_left hmax
    by_contra hc
    have hcle : energyClippedCovarianceError μ A tau (fun i => Y i ω) ≤
        Real.sqrt (C4 / N) + tau * Real.sqrt (2 * Real.log (8 / delta) / N) :=
      le_of_not_gt hc
    have hbound := hraw.trans (add_le_add hcle hbias)
    rw [hformula] at hbound
    exact (not_lt_of_ge hbound) herr
  calc
    _ ≤ ν.real (MaxBad ∪ ClipBad) := measureReal_mono hsubset
    _ ≤ ν.real MaxBad + ν.real ClipBad := measureReal_union_le _ _
    _ ≤ delta / 8 + delta / 8 := add_le_add hMax hclip
    _ = delta / 4 := by ring

end PaperFormalization.Manuscript
