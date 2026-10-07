import PaperFormalization.Manuscript.SourceTensorCovarianceResidual
import PaperFormalization.Manuscript.SourceTensorCovarianceIntegrability

/-! # The literal weighted-source tensor covariance reduction

Original feature growth and population moment hypotheses discharge genuine
covariance-tensor integrability. The local objective on the original open U
supplies its actual Hessian and its bound by the literal source L_D. The final
coefficient retains the actual sample Hilbert--Schmidt energy and L_D squared.
No sample localization, conditional-law change, or target norm bound is assumed.
-/

open Matrix MeasureTheory Set
open scoped BigOperators NNReal Matrix.Norms.Frobenius
set_option maxSynthPendingDepth 8

namespace PaperFormalization.Manuscript

variable {N d : ℕ}
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

noncomputable local instance instContinuousENormWeightedTensorResidualMatrix :
    ContinuousENorm (Matrix (Fin N × Fin d) (Fin N × Fin d) ℝ) :=
  SeminormedAddGroup.toContinuousENorm

/-- The actual weighted-source residual is a tensor compression and satisfies
exactly L_D² times the empirical derivative energy times the tensor error.
The full population law and actual feature derivatives are retained throughout. -/
theorem source_weighted_populationCovarianceResidual_tensor_reduction
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
    (Y : Fin N → EuclideanSpace ℝ (Fin d)) :
    let J := sourceWeightedFeatureMap c p φ
    let theta := ∫ z, J z ∂μ
    let A := fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix J G theta (Y i) z)
    let S := (∫ z, finiteOperatorCovariance (fderiv ℝ J z) ∂μ) -
      ∫ z, finiteOperatorCovariance (fderiv ℝ J z) ∂finiteEmpiricalMeasure Y
    populationCovarianceResidual μ Y A =
        hilbertTensorCompression (actualMomentTensorColumns J G theta Y) S ∧
      matrixNuclearValue (populationCovarianceResidual μ Y A) / N ≤
        (L : ℝ) ^ 2 * ((∑ i, finiteHilbertSchmidtNorm (fderiv ℝ J (Y i)) ^ 2) / N) * ‖S‖ := by
  let J := sourceWeightedFeatureMap c p φ
  let theta := ∫ z, J z ∂μ
  let Q := sourceObjectiveAnchorFactor c p C3 φ G
  let R := sourceMomentRadius c C g p q K D alpha
  have htheta : theta ∈ measureMomentRegion J (sourceMomentClass alpha K) D :=
    population_integral_mem_measureMomentRegion J (sourceMomentClass alpha K) D μ hμ
  have hGlocal : ContDiffAt ℝ 2 G theta :=
    (hG.contDiffAt (hU.mem_nhds (hSU htheta))).of_le (by norm_num)
  have hW : Integrable (fun z => finiteOperatorCovariance (fderiv ℝ J z)) μ :=
    (sourceMomentClass_integrable_tensorCovariance_and_norm_sq
      c C g p q alpha K φ hc hC hp hq halpha hK hφ hgrowth μ hμ).1
  have hvalue : ∀ n z, ‖φ n z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1)) := by
    intro n z
    simpa only [norm_iteratedFDeriv_zero, Nat.sub_zero] using hgrowth n z 0 (by omega)
  have hb := source_measure_region_objective_bounds c C g p q K D alpha C3 φ
    (sourceMomentClass alpha K) hc hC hp hq hK hD (fun n => (hφ n).continuous)
    (sourceMomentClass_isProbabilityMeasure alpha K)
    (fun ν hν n => (sourceMomentClass_succ_moment alpha K hK ν hν n).1)
    (fun ν hν n => (sourceMomentClass_succ_moment alpha K hK ν hν n).2)
    hvalue G U hU hSU hG hthirdG
  have hQ : 1 ≤ Q := hb.1
  have hR : 1 ≤ R := one_le_sourceMomentRadius c C g p q K D alpha hC hK.le (by linarith)
  have hLQR : (L : ℝ) = 4 * Q * R ^ 3 := hL
  have hR3 : R ≤ R ^ 3 := by
    have hR2 : R ≤ R ^ 2 := by nlinarith
    have h23 : R ^ 2 ≤ R ^ 3 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hR) (sq_nonneg R)]
    exact hR2.trans h23
  have hA : ‖momentObjectiveHessian G theta‖ ≤ (L : ℝ) := by
    calc
      _ ≤ Q * R := (hb.2 theta htheta).2
      _ ≤ Q * R ^ 3 := mul_le_mul_of_nonneg_left hR3 (by linarith)
      _ ≤ (L : ℝ) := (local_moment_constant_domination Q R (by linarith) hR).2.trans_eq hLQR.symm
  refine ⟨actual_populationCovarianceResidual_eq_tensor_compression J G theta μ Y hGlocal hW, ?_⟩
  exact (actual_populationCovarianceResidual_nuclear_normalized_le J G theta μ Y hGlocal hW).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hA 2)
        (div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) (Nat.cast_nonneg N)))
      (norm_nonneg _))

end PaperFormalization.Manuscript
