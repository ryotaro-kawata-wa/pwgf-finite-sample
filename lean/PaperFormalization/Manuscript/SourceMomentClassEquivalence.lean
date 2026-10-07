import PaperFormalization.Manuscript.SourceMomentClass

/-! # Honest root and supremum formulations of the all-real-order class

Every real-root formulation explicitly retains genuine integrability.
For the real supremum, boundedness is recorded instead of relying on the
arbitrary value that a conditionally complete order assigns an unbounded set.
These are exact reformulations of the extended-norm class, not new hypotheses
on members of that class.
-/

open MeasureTheory Set

namespace PaperFormalization.Manuscript

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
  [BorelSpace E] [SecondCountableTopology E]

/-- The extended norm definition is equivalent to the classical root bound,
provided all real norm-power integrals are genuinely integrable. -/
theorem sourceMomentClass_iff_integrable_root_bound (alpha K : ℝ) (hK : 0 < K)
    (μ : Measure E) :
    μ ∈ sourceMomentClass alpha K ↔
      IsProbabilityMeasure μ ∧ ∀ q : ℝ, 1 ≤ q →
        Integrable (fun x : E => ‖x‖ ^ q) μ ∧
          (∫ x : E, ‖x‖ ^ q ∂μ) ^ q⁻¹ ≤ K * q ^ (1 / alpha) := by
  constructor
  · intro hμ
    exact ⟨hμ.1, fun q hq =>
      ⟨sourceMomentClass_integrable_norm_rpow alpha K μ hμ q hq,
        sourceMomentClass_root_moment_bound alpha K hK μ hμ q hq⟩⟩
  · rintro ⟨hprob, hmoment⟩
    refine ⟨hprob, fun q hq => ?_⟩
    have hq0 : 0 < q := by linarith
    have hm : MemLp (id : E → E) (ENNReal.ofReal q) μ := by
      apply (integrable_norm_rpow_iff aestronglyMeasurable_id
        (ENNReal.ofReal_ne_zero_iff.mpr hq0) ENNReal.ofReal_ne_top).mp
      simpa only [id_eq, ENNReal.toReal_ofReal hq0.le] using (hmoment q hq).1
    rw [hm.eLpNorm_eq_integral_rpow_norm
      (ENNReal.ofReal_ne_zero_iff.mpr hq0) ENNReal.ofReal_ne_top]
    simpa only [id_eq, ENNReal.toReal_ofReal hq0.le] using
      ENNReal.ofReal_le_ofReal (hmoment q hq).2

/-- Multiplying the moment root by the exact source normalization q^(-1/alpha)
recovers the original bound with no change to its constant. -/
theorem source_normalized_root_le_iff (alpha K q root : ℝ) (hq : 0 < q) :
    q ^ (-1 / alpha) * root ≤ K ↔ root ≤ K * q ^ (1 / alpha) := by
  rw [neg_div, Real.rpow_neg hq.le, inv_mul_le_iff₀' (Real.rpow_pos_of_pos hq _)]

/-- Exact source-shaped all-real-q formulation, retaining integrability. -/
theorem sourceMomentClass_iff_integrable_normalized_root_bound (alpha K : ℝ)
    (hK : 0 < K) (μ : Measure E) :
    μ ∈ sourceMomentClass alpha K ↔
      IsProbabilityMeasure μ ∧ ∀ q : ℝ, 1 ≤ q →
        Integrable (fun x : E => ‖x‖ ^ q) μ ∧
          q ^ (-1 / alpha) * (∫ x : E, ‖x‖ ^ q ∂μ) ^ q⁻¹ ≤ K := by
  rw [sourceMomentClass_iff_integrable_root_bound alpha K hK μ]
  constructor <;> rintro ⟨hprob, hmoment⟩ <;> refine ⟨hprob, fun q hq => ?_⟩
  · exact ⟨(hmoment q hq).1,
      (source_normalized_root_le_iff alpha K q _ (by linarith)).mpr (hmoment q hq).2⟩
  · exact ⟨(hmoment q hq).1,
      (source_normalized_root_le_iff alpha K q _ (by linarith)).mp (hmoment q hq).2⟩

/-- Values of the actual source expression at all real q>=1. Integrability is
not encoded in this set itself and must be supplied before interpreting it. -/
def sourceNormalizedMomentValues (alpha : ℝ) (μ : Measure E) : Set ℝ :=
  (fun q : ℝ => q ^ (-1 / alpha) * (∫ x : E, ‖x‖ ^ q ∂μ) ^ q⁻¹) '' Ici 1

omit [BorelSpace E] [SecondCountableTopology E] in
/-- The supremum domain contains q=1, including at degenerate measures. -/
theorem sourceNormalizedMomentValues_nonempty (alpha : ℝ) (μ : Measure E) :
    (sourceNormalizedMomentValues alpha μ).Nonempty :=
  ⟨_, ⟨1, by simp, rfl⟩⟩

/-- The real source supremum is genuinely bounded, and obeys the stated K
bound, for every member of the extended-norm class. -/
theorem sourceMomentClass_bddAbove_supremum (alpha K : ℝ) (hK : 0 < K)
    (μ : Measure E) (hμ : μ ∈ sourceMomentClass alpha K) :
    BddAbove (sourceNormalizedMomentValues alpha μ) ∧
      sSup (sourceNormalizedMomentValues alpha μ) ≤ K := by
  have hall := ((sourceMomentClass_iff_integrable_normalized_root_bound
    alpha K hK μ).mp hμ).2
  have hu : ∀ z ∈ sourceNormalizedMomentValues alpha μ, z ≤ K := by
    rintro _ ⟨q, hq, rfl⟩
    exact (hall q hq).2
  exact ⟨⟨K, hu⟩, csSup_le (sourceNormalizedMomentValues_nonempty alpha μ) hu⟩

/-- An exact real-supremum interpretation of the source class. Both genuine
moment integrability and actual boundedness are explicit, preventing either
real-integral or conditionally-complete-supremum totalization loopholes. -/
theorem sourceMomentClass_iff_integrable_supremum_bound (alpha K : ℝ) (hK : 0 < K)
    (μ : Measure E) :
    μ ∈ sourceMomentClass alpha K ↔
      IsProbabilityMeasure μ ∧
      (∀ q : ℝ, 1 ≤ q → Integrable (fun x : E => ‖x‖ ^ q) μ) ∧
      BddAbove (sourceNormalizedMomentValues alpha μ) ∧
        sSup (sourceNormalizedMomentValues alpha μ) ≤ K := by
  constructor
  · intro hμ
    exact ⟨hμ.1, fun q hq => sourceMomentClass_integrable_norm_rpow alpha K μ hμ q hq,
      sourceMomentClass_bddAbove_supremum alpha K hK μ hμ⟩
  · rintro ⟨hprob, hint, hbdd, hsup⟩
    apply (sourceMomentClass_iff_integrable_normalized_root_bound alpha K hK μ).mpr
    refine ⟨hprob, fun q hq => ⟨hint q hq, ?_⟩⟩
    exact (le_csSup hbdd ⟨q, hq, rfl⟩).trans hsup

end PaperFormalization.Manuscript
