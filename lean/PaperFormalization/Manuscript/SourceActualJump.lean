import PaperFormalization.Manuscript.SourceEmpiricalFactor
import PaperFormalization.Manuscript.SourceGaussianJump
import PaperFormalization.Manuscript.PopulationCovariance
import PaperFormalization.Manuscript.SourceKernelCovarianceBounds

/-! # One actual source jump under an unchanged common Gaussian seed law

The actual particle difference is flattened using the product index
(particle, coordinate), with its norm proved exactly. Population covariance
is the genuine full Gram integral, and the empirical factors use the source
moments. The Gaussian event budget belongs to an unchanged seed measure;
no conditioning on sample localization is performed.
-/

open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.Frobenius MatrixOrder
set_option maxSynthPendingDepth 8

namespace PaperFormalization.Manuscript

variable {N d : ℕ}

/-- The concrete product-index vector of the particle coordinates. -/
def particleFlatten (X : PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin N × Fin d) := WithLp.toLp 2 (fun i => X i.1 i.2)

/-- Flattening uses exactly the source product indices and preserves norm. -/
theorem particleFlatten_norm (X : PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d)) :
    ‖particleFlatten X‖ = ‖X‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [particleFlatten, PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]

/-- Flattening preserves the actual difference of two particle configurations. -/
theorem particleFlatten_sub (X Y : PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d)) :
    particleFlatten (X - Y) = particleFlatten X - particleFlatten Y := rfl

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

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A fixed actual source configuration and its full population covariance
produce the source one-jump event under the unchanged standard-Gaussian seed
law. Both actual particle update identities are needed only almost surely.
All factor and covariance mismatch bounds are conclusions of source theory;
genuine population Gram integrability remains the explicit bridge input. -/
theorem exists_actual_source_jump_event
    (ν : Measure Ω) [IsFiniteMeasure ν]
    (seed : Ω → EuclideanSpace ℝ (Fin N × Fin d))
    (hseed : ν.map seed = stdGaussian (EuclideanSpace ℝ (Fin N × Fin d)))
    (X Y : PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d))
    (Xpost Ypost : Ω → PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d))
    (hN : 0 < N) (hX : ∀ i, ‖X i‖ ≤ D) (hY : ∀ i, ‖Y i‖ ≤ D)
    (eta u : ℝ) (heta : 0 ≤ eta) (hu : 0 < u) (hu1 : u < 1)
    (hGram : let J := sourceWeightedFeatureMap c p φ
      let A := fun z => stackedKernelMatrix (fun i =>
        actualMomentKernelMatrix J G (∫ x, J x ∂μ) (Y i) z)
      Integrable (fun z => A z * (A z)ᵀ) μ)
    (hXjump : ∀ᵐ ω ∂ν, particleFlatten (Xpost ω) = particleFlatten X +
      eta • matrixEuclideanOperator (sourceEmpiricalKernelFactor c p φ G X) (seed ω))
    (hYjump : let J := sourceWeightedFeatureMap c p φ
      let A := fun z => stackedKernelMatrix (fun i =>
        actualMomentKernelMatrix J G (∫ x, J x ∂μ) (Y i) z)
      let Cov := populationGramCovariance μ A
      let hMY := sourceEmpiricalKernelFactor_isHermitian c p K D alpha φ G U hU hSU
        (hG.of_le (by norm_num)) Y hN hY
      ∀ᵐ ω ∂ν, particleFlatten (Ypost ω) = particleFlatten Y +
        eta • matrixEuclideanOperator (alignedCovarianceFactor hMY Cov) (seed ω)) :
    let J := sourceWeightedFeatureMap c p φ
    let A := fun z => stackedKernelMatrix (fun i =>
      actualMomentKernelMatrix J G (∫ x, J x ∂μ) (Y i) z)
    let Gamma := momentResidual (featureResidualWeight c p L)
      (fun n _ => finiteFeatureMean (fun i => φ n (Y i))) (fun n _ => ∫ z, φ n z ∂μ) 0
    let GammaTilde := matrixNuclearValue (populationCovarianceResidual μ (fun i => Y i) A) / N
    let cJ := sourceJumpCoefficient d (featureDisplacementLambda c C g p q D L) (L : ℝ)
    ∃ Good : Set Ω, ν Goodᶜ ≤ ENNReal.ofReal u ∧ ∀ ω ∈ Good,
      ‖Xpost ω - Ypost ω‖ / Real.sqrt N ≤
        (1 + cJ * sourceGaussianDeviation u * eta) * (‖X - Y‖ / Real.sqrt N) +
          cJ * sourceGaussianDeviation u * eta * (Real.sqrt Gamma + Real.sqrt GammaTilde) := by
  let J := sourceWeightedFeatureMap c p φ
  let A := fun z => stackedKernelMatrix (fun i =>
    actualMomentKernelMatrix J G (∫ x, J x ∂μ) (Y i) z)
  let Cov := populationGramCovariance μ A
  let MX := sourceEmpiricalKernelFactor c p φ G X
  let MY := sourceEmpiricalKernelFactor c p φ G Y
  let Lambda := featureDisplacementLambda c C g p q D L
  let Gamma := momentResidual (featureResidualWeight c p L)
    (fun n _ => finiteFeatureMean (fun i => φ n (Y i))) (fun n _ => ∫ z, φ n z ∂μ) 0
  let GammaTilde := matrixNuclearValue (populationCovarianceResidual μ (fun i => Y i) A) / N
  have hMY : MY.IsHermitian := sourceEmpiricalKernelFactor_isHermitian c p K D alpha φ G U hU hSU
    (hG.of_le (by norm_num)) Y hN hY
  have hCov : Cov.PosSemidef := populationGramCovariance_posSemidef μ A hGram
  have hLambda : 0 ≤ Lambda := featureDisplacementLambda_nonneg c C g p q D L hC (by linarith)
  have hGamma : 0 ≤ Gamma := momentResidual_nonneg _ _ _ 0
  have hGammaTilde : 0 ≤ GammaTilde :=
    div_nonneg (matrixNuclearValue_nonneg_of_isHermitian
      (populationCovarianceResidual_isHermitian μ (fun i => Y i) A hGram)) (Nat.cast_nonneg N)
  have hfirst : ‖MX - MY‖ / Real.sqrt N ≤
      Real.sqrt d * (Lambda + 2 * (L : ℝ)) * (‖particleFlatten (X - Y)‖ / Real.sqrt N) := by
    rw [particleFlatten_norm]
    exact sourceEmpiricalKernelFactor_normalized_sub_le c C g p q K D alpha C3 φ
      hc hC hp hq hK hD hφ hgrowth G U hU hSU hG hthirdG L hL X Y hN hX hY
  have hmismatch : matrixNuclearValue (Cov - MY * MY) / N ≤ 2 * d * (L : ℝ) * Gamma + GammaTilde :=
    source_population_covariance_mismatch_normalized_le c C g p q K D alpha C3 φ
      hc hC hp hq hK hD hφ hgrowth G U hU hSU hG hthirdG L hL μ hμ Y hN hY hGram
  let NormGood := {ω | ‖matrixEuclideanOperator (MX - MY) (seed ω)‖ ≤
      sourceGaussianDeviation u * ‖MX - MY‖ ∧
    ‖matrixEuclideanOperator (MY - alignedCovarianceFactor hMY Cov) (seed ω)‖ ≤
      sourceGaussianDeviation u * ‖MY - alignedCovarianceFactor hMY Cov‖}
  have hbudget : ν NormGoodᶜ ≤ ENNReal.ofReal u :=
    two_matrix_gaussian_good_event ν seed hseed (MX - MY)
      (MY - alignedCovarianceFactor hMY Cov) u hu hu1
  let UpdateGood := {ω | particleFlatten (Xpost ω) = particleFlatten X +
      eta • matrixEuclideanOperator MX (seed ω) ∧
    particleFlatten (Ypost ω) = particleFlatten Y +
      eta • matrixEuclideanOperator (alignedCovarianceFactor hMY Cov) (seed ω)}
  have hupdate : ∀ᵐ ω ∂ν, ω ∈ UpdateGood := hXjump.and hYjump
  have hnull : ν UpdateGoodᶜ = 0 := ae_iff.mp hupdate
  refine ⟨NormGood ∩ UpdateGood, ?_, ?_⟩
  · rw [compl_inter]
    exact (measure_union_le _ _).trans (by simpa only [hnull, add_zero] using hbudget)
  · intro ω hω
    have hsplit : matrixEuclideanOperator (MX - MY) (seed ω) +
        matrixEuclideanOperator (MY - alignedCovarianceFactor hMY Cov) (seed ω) =
        matrixEuclideanOperator MX (seed ω) -
          matrixEuclideanOperator (alignedCovarianceFactor hMY Cov) (seed ω) := by
      change (Matrix.toEuclideanCLM (𝕜 := ℝ) (MX - MY)) (seed ω) +
          (Matrix.toEuclideanCLM (𝕜 := ℝ) (MY - alignedCovarianceFactor hMY Cov)) (seed ω) =
        (Matrix.toEuclideanCLM (𝕜 := ℝ) MX) (seed ω) -
          (Matrix.toEuclideanCLM (𝕜 := ℝ) (alignedCovarianceFactor hMY Cov)) (seed ω)
      rw [map_sub, map_sub, _root_.sub_apply, _root_.sub_apply]
      abel
    have hjump : particleFlatten (Xpost ω - Ypost ω) = particleFlatten (X - Y) +
        eta • (matrixEuclideanOperator (MX - MY) (seed ω) +
          matrixEuclideanOperator (MY - alignedCovarianceFactor hMY Cov) (seed ω)) := by
      rw [particleFlatten_sub, hω.2.1, hω.2.2, particleFlatten_sub, hsplit, smul_sub]
      abel
    have hb := source_gaussian_jump_on_good_event MX MY Cov hMY hCov (seed ω)
      (particleFlatten (X - Y)) (particleFlatten (Xpost ω - Ypost ω)) N d hN
      Lambda (L : ℝ) eta u Gamma GammaTilde hLambda L.coe_nonneg heta hGamma hGammaTilde
      hfirst hmismatch hω.1 hjump
    simpa only [particleFlatten_norm] using hb

end PaperFormalization.Manuscript
