import PaperFormalization.Manuscript.TensorCovarianceRestoration
import PaperFormalization.Manuscript.SourceSampleMaxTail
import PaperFormalization.Manuscript.SourceWeightedTensorResidual

/-! # Actual source covariance and nuclear-residual concentration

The literal source radius, sample threshold, and fourth-moment series discharge
the generic tail and moment inputs. The original population and iid sample
laws remain unchanged; this is a fixed-law theorem, not a conditional-law
identification or a pathwise union over jump times.
-/

open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal Matrix.Norms.Frobenius
set_option maxSynthPendingDepth 8

namespace PaperFormalization.Manuscript

variable {N d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

noncomputable local instance instContinuousENormSourceCovarianceConcentrationMatrix :
    ContinuousENorm (Matrix (Fin N × Fin d) (Fin N × Fin d) ℝ) :=
  SeminormedAddGroup.toContinuousENorm

/-- The actual source tensor error and sample maximum jointly satisfy the
literal source bound. The proved failure budget is delta/4, hence also delta. -/
theorem source_covariance_sample_max_and_error_failure_le
    (c C g p q alpha K delta : ℝ) (φ : ∀ n, EuclideanSpace ℝ (Fin d) → H n)
    (hN : 0 < N) (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (halpha : 0 < alpha) (hK : 0 < K) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hφ : ∀ n, ContDiff ℝ 2 (φ n))
    (hgrowth : ∀ n z k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) z‖ ≤
      featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1 - k)))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (hμ : μ ∈ sourceMomentClass alpha K)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (Y : Fin N → Ω → EuclideanSpace ℝ (Fin d))
    (hLaw : ∀ i, ν.map (Y i) = μ) (hind : iIndepFun Y ν) :
    let J := sourceWeightedFeatureMap c p φ
    let C4 := sourceHilbertSchmidtFourthMoment d c C g p q alpha K
    let tau := sourceSampleHilbertSchmidtEnvelope d c C g p q (sourceSampleRadius N alpha K delta)
    ν.real {ω | (∃ i, tau < finiteHilbertSchmidtNorm (fderiv ℝ J (Y i ω)) ^ 2) ∨
      Real.sqrt C4 / Real.sqrt N * (1 + Real.sqrt (delta / 8)) +
        tau * Real.sqrt (2 * Real.log (8 / delta) / N) <
      ‖(N : ℝ)⁻¹ • ∑ i, finiteOperatorCovariance (fderiv ℝ J (Y i ω)) -
        ∫ x, finiteOperatorCovariance (fderiv ℝ J x) ∂μ‖} ≤ delta / 4 := by
  letI : IsProbabilityMeasure μ := hμ.1
  have hA := (contDiff_sourceWeightedFeatureMap c C g p q φ hc hC hp hq hφ hgrowth).continuous_fderiv
    (by norm_num)
  have hfour := sourceMomentClass_hilbertSchmidt_fourth_moment_le
    c C g p q alpha K φ hc hC hp hq halpha hK hφ hgrowth μ hμ
  have hTail := sourceMomentClass_hilbertSchmidt_sampleEnvelope_tail_le N
    c C g p q alpha K delta φ hN hc hC hp hq halpha hK hdelta hdelta1 hφ hgrowth μ hμ
  have hMax := source_hilbertSchmidt_sample_max_tail_le N
    c C g p q alpha K delta φ hN hc hC hp hq halpha hK hdelta hdelta1 hφ hgrowth μ hμ ν Y hLaw
  simpa only [Fintype.card_fin] using covariance_sample_max_and_error_failure_le hN μ ν Y hLaw hind
    (fderiv ℝ (sourceWeightedFeatureMap c p φ)) hA
    (sourceSampleHilbertSchmidtEnvelope (Fintype.card (Fin d)) c C g p q
      (sourceSampleRadius N alpha K delta))
    (sourceHilbertSchmidtFourthMoment (Fintype.card (Fin d)) c C g p q alpha K) delta
    ((by norm_num : (0 : ℝ) ≤ 1).trans (one_le_sourceSampleHilbertSchmidtEnvelope _ _ _ _ _ _ _))
    hdelta (by linarith) hfour.1 hfour.2 hTail hMax

omit [MeasurableSpace Ω] [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)] in
/-- The source simplification retains its exact coefficient two and sqrt N
normalization. The fourth-moment constant itself is unchanged. -/
theorem source_covariance_nuclear_threshold_relaxation
    (L tau C4 delta : ℝ) (htau : 0 ≤ tau) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    L ^ 2 * tau * (Real.sqrt C4 / Real.sqrt N * (1 + Real.sqrt (delta / 8)) +
      tau * Real.sqrt (2 * Real.log (8 / delta) / N)) ≤
    L ^ 2 * tau / Real.sqrt N *
      (2 * Real.sqrt C4 + tau * Real.sqrt (2 * Real.log (8 / delta))) := by
  have hroot : Real.sqrt (delta / 8) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hlog : 0 ≤ 2 * Real.log (8 / delta) := mul_nonneg (by norm_num)
    (Real.log_nonneg ((le_div_iff₀ hdelta).mpr (by linarith)))
  calc
    _ ≤ L ^ 2 * tau * (Real.sqrt C4 / Real.sqrt N * 2 +
        tau * Real.sqrt (2 * Real.log (8 / delta) / N)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) htau)
      exact add_le_add (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) le_rfl
    _ = _ := by rw [Real.sqrt_div hlog]; ring

set_option maxHeartbeats 1600000 in
/-- The literal normalized nuclear jump residual has the exact source
high-probability bound, with the stronger proved failure budget delta/4.
The pointwise kernel/tensor reduction and all source moment/tail inputs are
proved internally from the original local objective and feature assumptions. -/
theorem source_nuclear_covariance_residual_failure_le
    (c C g p q K D alpha C3 delta : ℝ) (φ : ∀ n, EuclideanSpace ℝ (Fin d) → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (halpha : 0 < alpha) (hK : 0 < K) (hD : 1 ≤ D)
    (hφ : ∀ n, ContDiff ℝ 2 (φ n))
    (hgrowth : ∀ n z k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) z‖ ≤
      featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1 - k)))
    (G : lp H 2 → ℝ) (U : Set (lp H 2)) (hU : IsOpen U)
    (hSU : measureMomentRegion (sourceWeightedFeatureMap c p φ) (sourceMomentClass alpha K) D ⊆ U)
    (hG : ContDiffOn ℝ 3 G U)
    (hthirdG : ∀ theta ∈ measureMomentRegion (sourceWeightedFeatureMap c p φ)
      (sourceMomentClass alpha K) D, ‖iteratedFDeriv ℝ 3 G theta‖ ≤ C3)
    (L : ℝ≥0) (hL : (L : ℝ) = sourceComparisonEnvelope c C g p q K D alpha C3 φ G)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (hμ : μ ∈ sourceMomentClass alpha K)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (Y : Fin N → Ω → EuclideanSpace ℝ (Fin d))
    (hN : 0 < N) (hLaw : ∀ i, ν.map (Y i) = μ) (hind : iIndepFun Y ν)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    let J := sourceWeightedFeatureMap c p φ
    let theta := ∫ z, J z ∂μ
    let C4 := sourceHilbertSchmidtFourthMoment d c C g p q alpha K
    let tau := sourceSampleHilbertSchmidtEnvelope d c C g p q (sourceSampleRadius N alpha K delta)
    ν.real {ω | (L : ℝ) ^ 2 * tau / Real.sqrt N *
      (2 * Real.sqrt C4 + tau * Real.sqrt (2 * Real.log (8 / delta))) <
      matrixNuclearValue (populationCovarianceResidual μ (fun i => Y i ω)
        (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix J G theta (Y i ω) z))) / N} ≤
      delta / 4 := by
  let J := sourceWeightedFeatureMap c p φ
  let theta := ∫ z, J z ∂μ
  let C4 := sourceHilbertSchmidtFourthMoment d c C g p q alpha K
  let tau := sourceSampleHilbertSchmidtEnvelope d c C g p q (sourceSampleRadius N alpha K delta)
  let B := Real.sqrt C4 / Real.sqrt N * (1 + Real.sqrt (delta / 8)) +
    tau * Real.sqrt (2 * Real.log (8 / delta) / N)
  have htau : 0 ≤ tau := (by norm_num : (0 : ℝ) ≤ 1).trans
    (one_le_sourceSampleHilbertSchmidtEnvelope _ _ _ _ _ _ _)
  have hcov := source_covariance_sample_max_and_error_failure_le
    c C g p q alpha K delta φ hN hc hC hp hq halpha hK hdelta hdelta1 hφ hgrowth μ hμ ν Y hLaw hind
  apply (measureReal_mono (μ := ν) (show
    {ω | (L : ℝ) ^ 2 * tau / Real.sqrt N *
      (2 * Real.sqrt C4 + tau * Real.sqrt (2 * Real.log (8 / delta))) <
      matrixNuclearValue (populationCovarianceResidual μ (fun i => Y i ω)
        (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix J G theta (Y i ω) z))) / N} ⊆
    {ω | (∃ i, tau < finiteHilbertSchmidtNorm (fderiv ℝ J (Y i ω)) ^ 2) ∨
      B < ‖(N : ℝ)⁻¹ • ∑ i, finiteOperatorCovariance (fderiv ℝ J (Y i ω)) -
        ∫ x, finiteOperatorCovariance (fderiv ℝ J x) ∂μ‖} from ?_)).trans hcov
  intro ω hω
  by_contra hn
  have hy (i : Fin N) : finiteHilbertSchmidtNorm (fderiv ℝ J (Y i ω)) ^ 2 ≤ tau := by
    by_contra hi
    exact hn (Or.inl ⟨i, lt_of_not_ge hi⟩)
  have he : ‖(N : ℝ)⁻¹ • ∑ i, finiteOperatorCovariance (fderiv ℝ J (Y i ω)) -
        ∫ x, finiteOperatorCovariance (fderiv ℝ J x) ∂μ‖ ≤ B := by
    by_contra hi
    exact hn (Or.inr (lt_of_not_ge hi))
  have hnpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have henergy : ((∑ i, finiteHilbertSchmidtNorm (fderiv ℝ J (Y i ω)) ^ 2) / N) ≤ tau := by
    apply (div_le_iff₀ hnpos).mpr
    calc
      _ ≤ ∑ _i : Fin N, tau := Finset.sum_le_sum (fun i _ => hy i)
      _ = _ := by simp [mul_comm]
  have hred := (source_weighted_populationCovarianceResidual_tensor_reduction
    c C g p q K D alpha C3 φ hc hC hp hq halpha hK hD hφ hgrowth
    G U hU hSU hG hthirdG L hL μ hμ (fun i => Y i ω)).2
  simp only [integral_finiteEmpiricalMeasure, finiteFeatureMean, Fintype.card_fin] at hred
  rw [norm_sub_rev (∫ z, finiteOperatorCovariance (fderiv ℝ J z) ∂μ)
    ((N : ℝ)⁻¹ • ∑ i, finiteOperatorCovariance (fderiv ℝ J (Y i ω)))] at hred
  have hb := hred.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left henergy (sq_nonneg (L : ℝ))) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left he (mul_nonneg (sq_nonneg (L : ℝ)) htau)))
  exact (not_lt_of_ge (hb.trans
    (source_covariance_nuclear_threshold_relaxation (N := N) (L : ℝ) tau C4 delta htau hdelta hdelta1))) hω

end PaperFormalization.Manuscript
