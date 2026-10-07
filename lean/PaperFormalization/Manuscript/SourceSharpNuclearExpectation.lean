import PaperFormalization.Manuscript.SourceNuclearExpectation
import PaperFormalization.Manuscript.SourceHilbertSchmidtFourthMoment

/-! # The literal source nuclear expectation with its exact fourth-moment constant

The previously genuine fourth-moment input is now discharged by the original
source series C_Phi,4. The population measure remains in the all-real-q class,
and no sample localization or additional residual premise is introduced.
-/

open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal Matrix.Norms.Frobenius
set_option maxSynthPendingDepth 8

namespace PaperFormalization.Manuscript

variable {N d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

noncomputable local instance instContinuousENormSourceSharpNuclearExpectation :
    ContinuousENorm (Matrix (Fin N × Fin d) (Fin N × Fin d) ℝ) :=
  SeminormedAddGroup.toContinuousENorm

/-- The original source assumptions imply the literal expected jump residual
bound with the exact C_Phi,4 series and its visible dimension dependence. -/
theorem expected_source_nuclear_residual_exact_fourth_moment_le
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
    (hind : Pairwise (fun i j => IndepFun (Y i) (Y j) ν)) :
    let J := sourceWeightedFeatureMap c p φ
    let theta := ∫ z, J z ∂μ
    let R := fun ω => matrixNuclearValue (populationCovarianceResidual μ (fun i => Y i ω)
      (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix J G theta (Y i ω) z))) / N
    Integrable R ν ∧ (∫ ω, R ω ∂ν) ≤
      (L : ℝ) ^ 2 * sourceHilbertSchmidtFourthMoment d c C g p q alpha K / Real.sqrt N := by
  have hfour := sourceMomentClass_hilbertSchmidt_fourth_moment_le
    c C g p q alpha K φ hc hC hp hq halpha hK hφ hgrowth μ hμ
  exact expected_source_nuclear_populationCovarianceResidual_le
    c C g p q K D alpha C3 φ hc hC hp hq halpha hK hD hφ hgrowth
    G U hU hSU hG hthirdG L hL μ hμ ν Y hN hLaw hind
    (sourceHilbertSchmidtFourthMoment d c C g p q alpha K) hfour.1
    (by simpa only [Fintype.card_fin] using hfour.2)

end PaperFormalization.Manuscript
