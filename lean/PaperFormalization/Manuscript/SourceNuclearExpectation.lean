import PaperFormalization.Manuscript.ActualNuclearResidualMeasurability
import PaperFormalization.Manuscript.ActualTensorSampleMean
import PaperFormalization.Manuscript.SourceWeightedTensorResidual

/-! # Expected literal source nuclear covariance residual

The residual, its measurability, its nonnegativity and its pointwise tensor
reduction are all actual and derived internally. The population law is the
original all-real-order source class. The remaining quantitative input is a
genuine bound C4 on the actual derivative Hilbert--Schmidt fourth moment;
identifying C4 with the source's sharp series coefficient is a separate unit.
-/

open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal Matrix.Norms.Frobenius
set_option maxSynthPendingDepth 8

namespace PaperFormalization.Manuscript

variable {N d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

noncomputable local instance instContinuousENormSourceNuclearExpectationMatrix : ContinuousENorm (Matrix (Fin N × Fin d) (Fin N × Fin d) ℝ) :=
  SeminormedAddGroup.toContinuousENorm

set_option maxHeartbeats 1200000 in
/-- Original source hypotheses yield the literal nuclear covariance residual's
expected L_D² C4 / sqrt N bound. Residual measurability, positivity, tensor
integrability and the pointwise reduction are conclusions of previous proofs,
not additional premises. No population or sample law is localized. -/
theorem expected_source_nuclear_populationCovarianceResidual_le
    (c C g p q K D alpha C3 : ℝ) (φ : ∀ n, EuclideanSpace ℝ (Fin d) → H n)
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
    (hN : 0 < N) (hLaw : ∀ i, ν.map (Y i) = μ)
    (hind : Pairwise (fun i j => IndepFun (Y i) (Y j) ν))
    (C4 : ℝ)
    (hfour : Integrable (fun z => finiteHilbertSchmidtNorm
      (fderiv ℝ (sourceWeightedFeatureMap c p φ) z) ^ 4) μ)
    (hC4 : (∫ z, finiteHilbertSchmidtNorm
      (fderiv ℝ (sourceWeightedFeatureMap c p φ) z) ^ 4 ∂μ) ≤ C4) :
    let J := sourceWeightedFeatureMap c p φ
    let theta := ∫ z, J z ∂μ
    let R := fun ω => matrixNuclearValue (populationCovarianceResidual μ (fun i => Y i ω)
      (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix J G theta (Y i ω) z))) / N
    Integrable R ν ∧ (∫ ω, R ω ∂ν) ≤ (L : ℝ) ^ 2 * C4 / Real.sqrt N := by
  letI : IsProbabilityMeasure μ := hμ.1
  let J := sourceWeightedFeatureMap c p φ
  let theta := ∫ z, J z ∂μ
  let R := fun ω => matrixNuclearValue (populationCovarianceResidual μ (fun i => Y i ω)
    (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix J G theta (Y i ω) z))) / N
  have hJ : Continuous (fderiv ℝ J) :=
    (contDiff_sourceWeightedFeatureMap c C g p q φ hc hC hp hq hφ hgrowth).continuous_fderiv (by norm_num)
  have htheta : theta ∈ measureMomentRegion J (sourceMomentClass alpha K) D :=
    population_integral_mem_measureMomentRegion J (sourceMomentClass alpha K) D μ hμ
  have hGlocal : ContDiffAt ℝ 2 G theta :=
    (hG.contDiffAt (hU.mem_nhds (hSU htheta))).of_le (by norm_num)
  have hW : Integrable (fun z => finiteOperatorCovariance (fderiv ℝ J z)) μ :=
    (sourceMomentClass_integrable_tensorCovariance_and_norm_sq
      c C g p q alpha K φ hc hC hp hq halpha hK hφ hgrowth μ hμ).1
  have hreg := measurable_nonneg_actual_nuclear_populationCovarianceResidual
    (N := N) J G theta μ hJ hGlocal hW
  have hY (i : Fin N) : AEMeasurable (Y i) ν :=
    aemeasurable_of_map_neZero (by rw [hLaw i]; infer_instance)
  have hRmeas : AEStronglyMeasurable R ν :=
    (hreg.1.comp_aemeasurable (aemeasurable_pi_lambda (fun ω i => Y i ω) hY)).aestronglyMeasurable
  have hR0 : ∀ᵐ ω ∂ν, 0 ≤ R ω :=
    Filter.Eventually.of_forall (fun ω => hreg.2 (fun i => Y i ω))
  apply expected_residual_le_of_actual_tensor_reduction μ ν (fderiv ℝ J) hJ Y hN hLaw hind
    C4 hfour hC4 (L : ℝ) R hRmeas hR0
  filter_upwards with ω
  have hb := (source_weighted_populationCovarianceResidual_tensor_reduction
    c C g p q K D alpha C3 φ hc hC hp hq halpha hK hD hφ hgrowth
    G U hU hSU hG hthirdG L hL μ hμ (fun i => Y i ω)).2
  change R ω ≤ (L : ℝ) ^ 2 *
    ((∑ i, finiteHilbertSchmidtNorm (fderiv ℝ J (Y i ω)) ^ 2) / N) *
      ‖(∫ z, finiteOperatorCovariance (fderiv ℝ J z) ∂μ) -
        ∫ z, finiteOperatorCovariance (fderiv ℝ J z) ∂finiteEmpiricalMeasure (fun i => Y i ω)‖ at hb
  rw [integral_finiteEmpiricalMeasure] at hb
  simp only [finiteFeatureMean, Fintype.card_fin] at hb
  rw [norm_sub_rev] at hb
  simpa only [div_eq_mul_inv, mul_comm (∑ i, finiteHilbertSchmidtNorm (fderiv ℝ J (Y i ω)) ^ 2)
    ((N : ℝ)⁻¹), mul_assoc] using hb

end PaperFormalization.Manuscript
