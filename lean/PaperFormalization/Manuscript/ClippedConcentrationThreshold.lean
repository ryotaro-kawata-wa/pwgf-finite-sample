import PaperFormalization.Manuscript.WeightedClippedConcentration

/-! # The literal logarithmic source node threshold

The source threshold relaxes the proved mean A/(2sqrt N) to A/sqrt N.
The exact one-node failure budget is p/Q, with zero amplitude handled directly.
-/
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace PaperFormalization.Manuscript

/-- The literal McDiarmid substitution costs exactly p/Q. -/
theorem source_mcdiarmid_log_threshold (A Q p : ℝ) {N : ℕ}
    (hA : 0 < A) (hQ : 0 < Q) (hp : 0 < p) (hpQ : p < Q) (hN : 0 < N) :
    Real.exp (-2 * N * (A * Real.sqrt (Real.log (Q/p)/(2*N))) ^ 2 / A ^ 2) = p/Q := by
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hratio : 1 ≤ Q/p := (le_div_iff₀ hp).mpr (by linarith)
  have hlog : 0 ≤ Real.log (Q/p) := Real.log_nonneg hratio
  have hs := Real.sq_sqrt (div_nonneg hlog (by positivity : 0 ≤ (2:ℝ)*N))
  have he : -2 * N * (A * Real.sqrt (Real.log (Q/p)/(2*N))) ^ 2 / A ^ 2 = -Real.log (Q/p) := by
    rw [mul_pow, hs]
    field_simp
  rw [he, Real.exp_neg, Real.exp_log (div_pos hQ hp), inv_div]

/-- A proved centered tail and actual mean bound yield the literal source
threshold; the scalar substitution is derived rather than assumed. -/
theorem measure_gt_source_threshold_le {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsFiniteMeasure ν] (F : Ω → ℝ) (A Q p : ℝ) {N : ℕ}
    (hA : 0 < A) (hQ : 0 < Q) (hp : 0 < p) (hpQ : p < Q) (hN : 0 < N)
    (hmean : (∫ ω, F ω ∂ν) ≤ A / Real.sqrt N)
    (htail : ∀ t : ℝ, 0 ≤ t → ν.real {ω | (∫ z, F z ∂ν) + t ≤ F ω} ≤
      Real.exp (-2 * N * t ^ 2 / A ^ 2)) :
    ν.real {ω | A / Real.sqrt N + A * Real.sqrt (Real.log (Q/p)/(2*N)) < F ω} ≤ p/Q := by
  let t := A * Real.sqrt (Real.log (Q/p)/(2*N))
  have hs : {ω | A / Real.sqrt N + t < F ω} ⊆ {ω | (∫ z, F z ∂ν) + t ≤ F ω} := by
    intro ω hω
    exact le_of_lt (lt_of_le_of_lt (add_le_add hmean le_rfl) hω)
  have hb := (measureReal_mono (μ := ν) hs).trans (htail t (mul_nonneg hA.le (Real.sqrt_nonneg _)))
  exact hb.trans_eq (source_mcdiarmid_log_threshold A Q p hA hQ hp hpQ hN)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

/-- The actual original-system clipped sample statistic has exactly the source
one-grid-node failure budget, including amplitude zero. -/
theorem weightedClippedSampleResidual_iid_source_threshold
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (hN : 0 < N)
    (μ : Measure E) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (Y : Fin N → Ω → E) (hLaw : ∀ i, ν.map (Y i) = μ) (hind : iIndepFun Y ν)
    (D : ℝ) (hD : 0 ≤ D) (w : ℕ → ℝ≥0) (L : ℕ → ℝ) (m : ℕ → ℕ)
    (hL : ∀ n, 0 ≤ L n) (φ : ∀ n, E → H n) (hc : ∀ n, Continuous (φ n))
    (hg : ∀ n x, ‖φ n x‖ ≤ L n * (1 + ‖x‖ ^ m n))
    (hsum : Summable (fun n => (w n : ℝ) * (L n * (1 + D ^ m n))))
    (Q p : ℝ) (hQ : 0 < Q) (hp : 0 < p) (hpQ : p < Q) :
    let A := 2 * ∑' n, (w n : ℝ) * (L n * (1 + D ^ m n))
    ν.real {ω | A / Real.sqrt N + A * Real.sqrt (Real.log (Q/p)/(2*N)) <
      weightedClippedSampleResidual μ D w φ (fun i => Y i ω)} ≤ p/Q := by
  let A := 2 * ∑' n, (w n : ℝ) * (L n * (1 + D ^ m n))
  have hA0 : 0 ≤ A := by
    apply mul_nonneg (by norm_num)
    exact tsum_nonneg (fun n => mul_nonneg (w n).coe_nonneg (mul_nonneg (hL n) (by positivity)))
  by_cases hAz : A = 0
  · have hz (ω : Ω) : weightedClippedSampleResidual μ D w φ (fun i => Y i ω) = 0 :=
      weightedClippedSampleResidual_eq_zero_of_amplitude_zero hN μ D hD w L m hL φ hc hg hsum hAz _
    change ν.real {ω | A / Real.sqrt N + A * Real.sqrt (Real.log (Q/p)/(2*N)) < _} ≤ _
    simp only [hAz, hz, zero_div, zero_mul, add_zero, lt_self_iff_false, Set.setOf_false, measureReal_empty]
    exact div_nonneg hp.le hQ.le
  have ha : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hAz)
  have hconc := weightedClippedSampleResidual_iid_concentration hN μ ν Y hLaw hind
    D hD w L m hL φ hc hg hsum
  apply measure_gt_source_threshold_le ν _ A Q p ha hQ hp hpQ hN _ hconc.2.2.2
  have hn : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  exact hconc.2.2.1.trans (by apply div_le_div_of_nonneg_left hA0 hn; linarith)
end PaperFormalization.Manuscript
