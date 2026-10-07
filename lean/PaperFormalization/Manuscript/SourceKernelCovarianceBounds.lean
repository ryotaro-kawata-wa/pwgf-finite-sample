import PaperFormalization.Manuscript.SourceEmpiricalFactor
import PaperFormalization.Manuscript.SourceEmpiricalPopulationField
import PaperFormalization.Manuscript.PopulationCovariance

/-! # Actual source kernel bounds and covariance mismatch

Population and empirical kernels are evaluated on the same localized cloud.
Only these sample-supported evaluations receive the local magnitude bound;
the population covariance is the full, untruncated Bochner integral. Genuine
Gram integrability remains explicit in this intermediate adapter. The literal
Gamma/2 kernel difference derives the source 2*d*L*Gamma mismatch coefficient.
-/

open Matrix MeasureTheory Set
open scoped BigOperators NNReal Matrix.Norms.Frobenius
set_option maxSynthPendingDepth 8

namespace PaperFormalization.Manuscript

variable {N d : ℕ}

noncomputable local instance : ContinuousENorm (Matrix (Fin N × Fin d) (Fin N × Fin d) ℝ) :=
  SeminormedAddGroup.toContinuousENorm
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

variable (c C g p q K D alpha C3 : ℝ) (φ : ∀ n, EuclideanSpace ℝ (Fin d) → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (hD : 1 ≤ D)
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

include hc hC hp hq hK hD hφ hgrowth hU hSU hG hthirdG hL hμ

/-- Actual population and empirical sample-local kernel magnitudes are at
most L, and their actual operator difference is at most the literal Gamma/2.
The population law is an unchanged member of the original moment class. -/
theorem source_population_empirical_kernel_sample_bounds
    (Y : PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d)) (hN : 0 < N)
    (hY : ∀ i, ‖Y i‖ ≤ D) :
    let J := sourceWeightedFeatureMap c p φ
    let theta := ∫ z, J z ∂μ
    let thetaY := empiricalMomentMap J Y
    let Gamma := momentResidual (featureResidualWeight c p L)
      (fun n _ => finiteFeatureMean (fun i => φ n (Y i))) (fun n _ => ∫ z, φ n z ∂μ) 0
    ∀ i j,
      ‖matrixEuclideanOperator (actualMomentKernelMatrix J G theta (Y i) (Y j))‖ ≤ (L : ℝ) ∧
      ‖matrixEuclideanOperator (actualMomentKernelMatrix J G thetaY (Y i) (Y j))‖ ≤ (L : ℝ) ∧
      ‖matrixEuclideanOperator (actualMomentKernelMatrix J G theta (Y i) (Y j) -
        actualMomentKernelMatrix J G thetaY (Y i) (Y j))‖ ≤ Gamma / 2 := by
  dsimp only
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let J := sourceWeightedFeatureMap c p φ
  let Q := sourceObjectiveAnchorFactor c p C3 φ G
  let R := sourceMomentRadius c C g p q K D alpha
  have hvalue : ∀ n z, ‖φ n z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1)) := by
    intro n z
    simpa only [norm_iteratedFDeriv_zero, Nat.sub_zero] using hgrowth n z 0 (by omega)
  have hb := source_measure_region_objective_bounds c C g p q K D alpha C3 φ
    (sourceMomentClass alpha K) hc hC hp hq hK hD (fun n => (hφ n).continuous)
    (sourceMomentClass_isProbabilityMeasure alpha K)
    (fun ν hν n => (sourceMomentClass_succ_moment alpha K hK ν hν n).1)
    (fun ν hν n => (sourceMomentClass_succ_moment alpha K hK ν hν n).2)
    hvalue G U hU hSU hG hthirdG
  have ht := hb.2 _ (population_integral_mem_measureMomentRegion J (sourceMomentClass alpha K) D μ hμ)
  have htY := hb.2 _ (empiricalMomentMap_mem_measureMomentRegion J (sourceMomentClass alpha K) D Y hY)
  have hR : 1 ≤ R := one_le_sourceMomentRadius c C g p q K D alpha hC hK.le (by linarith)
  have hQ : 1 ≤ Q := hb.1
  have hLQR : (L : ℝ) = 4 * Q * R ^ 3 := hL
  intro i j
  have hi := source_feature_norms_le_radius c C g p q K D alpha φ
    hc hC hp hq hK hD hφ hgrowth (Y i) (hY i)
  have hj := source_feature_norms_le_radius c C g p q K D alpha φ
    hc hC hp hq hK hD hφ hgrowth (Y j) (hY j)
  have hm (theta : lp H 2) (htheta : ‖momentObjectiveHessian G theta‖ ≤ Q * R) :
      ‖matrixEuclideanOperator (actualMomentKernelMatrix J G theta (Y i) (Y j))‖ ≤ (L : ℝ) := by
    unfold actualMomentKernelMatrix
    rw [matrixEuclideanOperator_euclideanOperatorMatrix, hLQR]
    calc
      _ ≤ ‖fderiv ℝ J (Y i)‖ * ‖momentObjectiveHessian G theta‖ * ‖fderiv ℝ J (Y j)‖ :=
        norm_momentIntegralHessian_le _ _ _
      _ ≤ R * (Q * R) * R := by
        gcongr
        · exact hi.2.1
        · exact hj.2.1
      _ = Q * R ^ 3 := by ring
      _ ≤ _ := (local_moment_constant_domination Q R (by linarith) hR).2
  refine ⟨hm _ ht.2, hm _ htY.2, ?_⟩
  have herr := (source_empirical_population_field_bounds_by_residual c C g p q K D alpha C3 φ
    (sourceMomentClass alpha K) hc hC hp hq hK hD hφ hgrowth
    (sourceMomentClass_isProbabilityMeasure alpha K)
    (fun ν hν n => (sourceMomentClass_succ_moment alpha K hK ν hν n).1)
    (fun ν hν n => (sourceMomentClass_succ_moment alpha K hK ν hν n).2)
    G U hU hSU hG hthirdG L hL μ hμ Y hY (Y i) (Y j) (hY i) (hY j) 0).2.2
  unfold actualMomentKernelMatrix
  rw [← euclideanOperatorMatrix_sub, matrixEuclideanOperator_euclideanOperatorMatrix, norm_sub_rev]
  exact herr

/-- With genuine integrability of the actual untruncated population Gram
matrix, sample-local source estimates derive the literal normalized covariance
mismatch bound. The original 2*d*L*Gamma coefficient is retained, including
its dimension dependence and the unchanged covariance fluctuation residual. -/
theorem source_population_covariance_mismatch_normalized_le
    (Y : PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d)) (hN : 0 < N)
    (hY : ∀ i, ‖Y i‖ ≤ D)
    (hGram : let J := sourceWeightedFeatureMap c p φ
      let A := fun z => stackedKernelMatrix (fun i =>
        actualMomentKernelMatrix J G (∫ x, J x ∂μ) (Y i) z)
      Integrable (fun z => A z * (A z)ᵀ) μ) :
    let J := sourceWeightedFeatureMap c p φ
    let A := fun z => stackedKernelMatrix (fun i =>
      actualMomentKernelMatrix J G (∫ x, J x ∂μ) (Y i) z)
    let Gamma := momentResidual (featureResidualWeight c p L)
      (fun n _ => finiteFeatureMean (fun i => φ n (Y i))) (fun n _ => ∫ z, φ n z ∂μ) 0
    matrixNuclearValue (populationGramCovariance μ A -
      sourceEmpiricalKernelFactor c p φ G Y * sourceEmpiricalKernelFactor c p φ G Y) / N ≤
      2 * d * (L : ℝ) * Gamma +
        matrixNuclearValue (populationCovarianceResidual μ (fun i => Y i) A) / N := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let J := sourceWeightedFeatureMap c p φ
  let Gamma := momentResidual (featureResidualWeight c p L)
    (fun n _ => finiteFeatureMean (fun i => φ n (Y i))) (fun n _ => ∫ z, φ n z ∂μ) 0
  have hGamma : 0 ≤ Gamma := momentResidual_nonneg _ _ _ 0
  have hsample := source_population_empirical_kernel_sample_bounds c C g p q K D alpha C3 φ
    hc hC hp hq hK hD hφ hgrowth G U hU hSU hG hthirdG L hL μ hμ Y hN hY
  have hGlocal : ContDiffAt ℝ 2 G (empiricalMomentMap J Y) :=
    (hG.contDiffAt (hU.mem_nhds (hSU
      (empiricalMomentMap_mem_measureMomentRegion J (sourceMomentClass alpha K) D Y hY)))).of_le
        (by norm_num)
  have hb := population_covariance_mismatch_normalized_le μ (fun i => Y i)
    (fun i z => actualMomentKernelMatrix J G (∫ x, J x ∂μ) (Y i) z)
    (fun i j => actualMomentKernelMatrix J G (empiricalMomentMap J Y) (Y i) (Y j))
    (L : ℝ) (Gamma / 2) hN L.coe_nonneg (by positivity) hGram
    (fun i j => (hsample i j).1) (fun i j => (hsample i j).2.1)
    (fun i j => (hsample i j).2.2)
    (fun i j => actualMomentKernelMatrix_transpose J G (empiricalMomentMap J Y) (Y i) (Y j) hGlocal)
  have hcoeff : 2 * (d : ℝ) * (L : ℝ) * (Gamma / 2) ≤ 2 * d * (L : ℝ) * Gamma :=
    mul_le_mul_of_nonneg_left (by linarith : Gamma / 2 ≤ Gamma) (by positivity)
  exact hb.trans (add_le_add hcoeff le_rfl)

end PaperFormalization.Manuscript
