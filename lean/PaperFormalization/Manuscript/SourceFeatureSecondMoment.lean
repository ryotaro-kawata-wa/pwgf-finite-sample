import PaperFormalization.Manuscript.SourceKernelIntegrability
import PaperFormalization.Manuscript.HilbertSampleMean

/-! # Actual coordinate-feature L2 moments and independent sample means

The source index n is m=n+1. Every bound uses the original population law
and its order 2m moment, without a population cutoff. The exact Minkowski
envelope is retained; no dimension-dependent or numerical loss is added.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace PaperFormalization.Manuscript

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
  [BorelSpace E] [SecondCountableTopology E] [NormedAddCommGroup F]

/-- The exact L2 envelope of source coordinate m=n+1, from its order-2m
population moment and the source value-growth coefficient L_m. -/
noncomputable def sourceCoordinateL2Envelope (C g q alpha K : ℝ) (n : ℕ) : ℝ :=
  featureGrowth C g q n *
    (1 + (K * (2 * ((n + 1 : ℕ) : ℝ)) ^ (1 / alpha)) ^ (n + 1))

omit [SecondCountableTopology E] in
/-- The actual extended L2 seminorm has the exact displayed source envelope. -/
theorem sourceMomentClass_eLpNorm_coordinate_feature_two_le
    (C g q alpha K : ℝ) (hC : 0 ≤ C) (hK : 0 < K)
    (μ : Measure E) (hμ : μ ∈ sourceMomentClass alpha K)
    (n : ℕ) (φ : E → F)
    (hgrowth : ∀ x, ‖φ x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1))) :
    eLpNorm φ 2 μ ≤ ENNReal.ofReal (sourceCoordinateL2Envelope C g q alpha K n) := by
  exact (eLpNorm_mono_ae_real (Filter.Eventually.of_forall hgrowth)).trans
    (sourceMomentClass_eLpNorm_weighted_envelope_two_le alpha K hK μ hμ
      (featureGrowth C g q n) (by unfold featureGrowth; positivity) (n + 1))

/-- Continuous actual source coordinates are genuinely L2; finiteness is
established before interpreting their real second-moment integrals. -/
theorem sourceMomentClass_memLp_coordinate_feature_two
    (C g q alpha K : ℝ) (hC : 0 ≤ C) (hK : 0 < K)
    (μ : Measure E) (hμ : μ ∈ sourceMomentClass alpha K)
    (n : ℕ) (φ : E → F) (hφ : Continuous φ)
    (hgrowth : ∀ x, ‖φ x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1))) :
    MemLp φ 2 μ :=
  ⟨hφ.aestronglyMeasurable,
    (sourceMomentClass_eLpNorm_coordinate_feature_two_le
      C g q alpha K hC hK μ hμ n φ hgrowth).trans_lt ENNReal.ofReal_lt_top⟩

/-- The actual feature second moment is bounded by the square of the exact
Minkowski envelope, using the genuine integral rather than totalization. -/
theorem sourceMomentClass_coordinate_feature_second_moment_le
    (C g q alpha K : ℝ) (hC : 0 ≤ C) (hK : 0 < K)
    (μ : Measure E) (hμ : μ ∈ sourceMomentClass alpha K)
    (n : ℕ) (φ : E → F) (hφ : Continuous φ)
    (hgrowth : ∀ x, ‖φ x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1))) :
    Integrable (fun x => ‖φ x‖ ^ 2) μ ∧
      (∫ x, ‖φ x‖ ^ 2 ∂μ) ≤ (sourceCoordinateL2Envelope C g q alpha K n) ^ 2 := by
  have hmem := sourceMomentClass_memLp_coordinate_feature_two C g q alpha K hC hK μ hμ n φ hφ hgrowth
  refine ⟨hmem.integrable_norm_pow (by norm_num), ?_⟩
  have hb := sourceMomentClass_eLpNorm_coordinate_feature_two_le C g q alpha K hC hK μ hμ n φ hgrowth
  have hB : 0 ≤ sourceCoordinateL2Envelope C g q alpha K n := by
    unfold sourceCoordinateL2Envelope featureGrowth
    positivity
  have hs : Real.sqrt (∫ x, ‖φ x‖ ^ 2 ∂μ) ≤ sourceCoordinateL2Envelope C g q alpha K n := by
    rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)] at hb
    simpa only [ENNReal.toReal_ofNat, one_div, invOf_eq_inv, Real.rpow_two,
      Real.sqrt_eq_rpow, ENNReal.ofReal_le_ofReal_iff hB] using hb
  have hsq := Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg ‖φ x‖) :
    0 ≤ ∫ x, ‖φ x‖ ^ 2 ∂μ)
  nlinarith [Real.sqrt_nonneg (∫ x, ‖φ x‖ ^ 2 ∂μ)]

section Sample

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H]

/-- Actual independent particles with the same unchanged population law give
the source feature mean error, with the exact 1/N normalization and no
population truncation. The conditional application fixes that population law. -/
theorem expected_source_coordinate_sampleMean_error_le {N : ℕ}
    (C g q alpha K : ℝ) (hC : 0 ≤ C) (hK : 0 < K)
    (μ : Measure E) (hμ : μ ∈ sourceMomentClass alpha K)
    (n : ℕ) (φ : E → H) (hφ : Continuous φ)
    (hgrowth : ∀ x, ‖φ x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1)))
    (ν : Measure Ω) [IsProbabilityMeasure ν] (Y : Fin N → Ω → E)
    (hN : 0 < N)
    (hLaw : ∀ i, ν.map (Y i) = μ)
    (hind : Pairwise (fun i j => IndepFun (Y i) (Y j) ν)) :
    (∫ ω, ‖(N : ℝ)⁻¹ • ∑ i, φ (Y i ω) - ∫ x, φ x ∂μ‖ ∂ν) ≤
      sourceCoordinateL2Envelope C g q alpha K n / Real.sqrt N := by
  letI : IsProbabilityMeasure μ := hμ.1
  have hY (i : Fin N) : AEMeasurable (Y i) ν :=
    aemeasurable_of_map_neZero (by rw [hLaw i]; infer_instance)
  have hm := sourceMomentClass_memLp_coordinate_feature_two C g q alpha K hC hK μ hμ n φ hφ hgrowth
  have hX (i : Fin N) : MemLp (fun ω => φ (Y i ω)) 2 ν := by
    have hmap : MemLp φ 2 (ν.map (Y i)) := by rw [hLaw i]; exact hm
    exact hmap.comp_of_map (hY i)
  have hb : (∫ ω, ‖(N : ℝ)⁻¹ • ∑ i, φ (Y i ω) - ∫ x, φ x ∂μ‖ ∂ν) ≤
      Real.sqrt ((sourceCoordinateL2Envelope C g q alpha K n) ^ 2 / N) := by
    apply integral_norm_sampleMean_sub_le ν (fun i ω => φ (Y i ω)) hN hX
    · intro i j hij
      exact (hind hij).comp hφ.measurable hφ.measurable
    · intro i
      rw [← integral_map (hY i) hφ.aestronglyMeasurable, hLaw i]
    · intro i
      have hmap : (∫ x, ‖φ x‖ ^ 2 ∂(ν.map (Y i))) = ∫ ω, ‖φ (Y i ω)‖ ^ 2 ∂ν :=
        integral_map (hY i) (hφ.norm.pow 2).aestronglyMeasurable
      rw [← hmap, hLaw i]
      exact (sourceMomentClass_coordinate_feature_second_moment_le
        C g q alpha K hC hK μ hμ n φ hφ hgrowth).2
  have hB : 0 ≤ sourceCoordinateL2Envelope C g q alpha K n := by
    unfold sourceCoordinateL2Envelope featureGrowth
    positivity
  simpa only [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hB] using hb

end Sample

end PaperFormalization.Manuscript
