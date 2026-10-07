import PaperFormalization.Manuscript.SourceActualJump
import PaperFormalization.Manuscript.SourcePopulationGram

/-! # Source one-jump comparison with genuine population integrability derived

The original all-real-order moment class supplies operator-valued L2 of the
actual weighted feature derivative, hence actual population Gram integrability.
The one-jump theorem has no integrability, factor-bound, covariance-norm, or
symmetry premise left over from its intermediate adapters. The seed law remains
unchanged and both actual updates are needed only almost surely. Identifying
that supplied seed law with a conditional construction remains separate.
-/

open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.Frobenius MatrixOrder
set_option maxSynthPendingDepth 8

namespace PaperFormalization.Manuscript

variable {N d : ℕ}

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

/-- Original source feature and moment assumptions give the actual one-jump
comparison event, with every population Gram integrability requirement derived.
The distances are the actual particle L2 norms divided by sqrt(N), and the
covariance fluctuation is the literal normalized two-integral residual. -/
theorem exists_actual_source_jump_event_of_source_moments
    (halpha : 0 < alpha)
    (ν : Measure Ω) [IsFiniteMeasure ν]
    (seed : Ω → EuclideanSpace ℝ (Fin N × Fin d))
    (hseed : ν.map seed = stdGaussian (EuclideanSpace ℝ (Fin N × Fin d)))
    (X Y : PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d))
    (Xpost Ypost : Ω → PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d))
    (hN : 0 < N) (hX : ∀ i, ‖X i‖ ≤ D) (hY : ∀ i, ‖Y i‖ ≤ D)
    (eta u : ℝ) (heta : 0 ≤ eta) (hu : 0 < u) (hu1 : u < 1)
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
  have hGram := sourceMomentClass_integrable_actualMomentKernelMatrix_gram
    c C g p q alpha K φ hc hC hp hq halpha hK hφ hgrowth μ hμ G
    (∫ z, sourceWeightedFeatureMap c p φ z ∂μ) (fun i => Y i)
  exact exists_actual_source_jump_event c C g p q K D alpha C3 φ
    hc hC hp hq hK hD hφ hgrowth G U hU hSU hG hthirdG L hL μ hμ
    ν seed hseed X Y Xpost Ypost hN hX hY eta u heta hu hu1 hGram hXjump hYjump

end PaperFormalization.Manuscript
