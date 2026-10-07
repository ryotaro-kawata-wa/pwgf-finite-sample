import PaperFormalization.Manuscript.SourceActualJumpComplete
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-! # Actual source jump failures under an unchanged conditional kernel

The bad event is exactly the intersection of the supplied population-good
history event, sample localization, and failure of the actual particle recursion.
The Gaussian seed law is never conditionally reweighted. One common AE history event supplies the original
population class, conditional standard seed law, and conditional AE updates.
Outside the population-good event no fixed population moment scale is assumed.
The joint result uses explicit measurability of this actual failure event;
no measurable selection of history-dependent good sets is required.
-/

open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.Frobenius MatrixOrder ProbabilityTheory
set_option maxSynthPendingDepth 8

namespace PaperFormalization.Manuscript

variable {N d : ℕ} {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

/-- The actual source recursion failure on population-good localized histories.
Every residual and normalized distance is constructed from the supplied source
paths and laws. -/
noncomputable def actualSourceJumpFailure (c C g p q D : ℝ)
    (φ : ∀ n, EuclideanSpace ℝ (Fin d) → H n) (G : lp H 2 → ℝ) (L : ℝ≥0)
    (PopGood : Set S) (μ : S → Measure (EuclideanSpace ℝ (Fin d)))
    (X Y : S → PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d))
    (Xpost Ypost : S → Ω → PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d))
    (eta u : ℝ) : Set (S × Ω) :=
  let J := sourceWeightedFeatureMap c p φ
  let A := fun h z => stackedKernelMatrix (fun i =>
    actualMomentKernelMatrix J G (∫ x, J x ∂(μ h)) (Y h i) z)
  let Gamma := fun h => momentResidual (featureResidualWeight c p L)
    (fun n _ => finiteFeatureMean (fun i => φ n (Y h i))) (fun n _ => ∫ z, φ n z ∂(μ h)) 0
  let GammaTilde := fun h =>
    matrixNuclearValue (populationCovarianceResidual (μ h) (fun i => Y h i) (A h)) / N
  let cJ := sourceJumpCoefficient d (featureDisplacementLambda c C g p q D L) (L : ℝ)
  {z | (z.1 ∈ PopGood ∧ ((∀ i, ‖X z.1 i‖ ≤ D) ∧ (∀ i, ‖Y z.1 i‖ ≤ D))) ∧
    (1 + cJ * sourceGaussianDeviation u * eta) * (‖X z.1 - Y z.1‖ / Real.sqrt N) +
      cJ * sourceGaussianDeviation u * eta * (Real.sqrt (Gamma z.1) + Real.sqrt (GammaTilde z.1)) <
        ‖Xpost z.1 z.2 - Ypost z.1 z.2‖ / Real.sqrt N}

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
    (halpha : 0 < alpha)
    (ρ : Measure S) (k : Kernel S Ω) [IsMarkovKernel k]
    (PopGood : Set S) (μ : S → Measure (EuclideanSpace ℝ (Fin d)))
    (X Y : S → PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d))
    (Xpost Ypost : S → Ω → PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d))
    (seed : S → Ω → EuclideanSpace ℝ (Fin N × Fin d))
    (hN : 0 < N) (eta u : ℝ) (heta : 0 ≤ eta) (hu : 0 < u) (hu1 : u < 1)
    (hgood : ∀ᵐ h ∂ρ, h ∈ PopGood →
      μ h ∈ sourceMomentClass alpha K ∧
      (k h).map (seed h) = stdGaussian (EuclideanSpace ℝ (Fin N × Fin d)) ∧
      ∀ hloc : (∀ i, ‖X h i‖ ≤ D) ∧ (∀ i, ‖Y h i‖ ≤ D),
        let J := sourceWeightedFeatureMap c p φ
        let A := fun z => stackedKernelMatrix (fun i =>
          actualMomentKernelMatrix J G (∫ x, J x ∂(μ h)) (Y h i) z)
        let Cov := populationGramCovariance (μ h) A
        let hMY := sourceEmpiricalKernelFactor_isHermitian c p K D alpha φ G U hU hSU
          (hG.of_le (by norm_num)) (Y h) hN hloc.2
        ∀ᵐ ω ∂k h,
          particleFlatten (Xpost h ω) = particleFlatten (X h) +
            eta • matrixEuclideanOperator (sourceEmpiricalKernelFactor c p φ G (X h)) (seed h ω) ∧
          particleFlatten (Ypost h ω) = particleFlatten (Y h) +
            eta • matrixEuclideanOperator (alignedCovarianceFactor hMY Cov) (seed h ω))

include hc hC hp hq hK hD hφ hgrowth hU hSU hG hthirdG hL halpha hN heta hu hu1 hgood

/-- Under the unchanged conditional law, the explicit localized actual-jump
failure has budget u for almost every history. Histories outside PopGood or
outside sample localization contribute the empty event. No Gaussian law
conditioned on localization is asserted. -/
theorem conditional_actual_source_jump_failure_bound :
    ∀ᵐ h ∂ρ, k h {ω | (h, ω) ∈ actualSourceJumpFailure c C g p q D φ G L
      PopGood μ X Y Xpost Ypost eta u} ≤ ENNReal.ofReal u := by
  filter_upwards [hgood] with h hh
  by_cases heligible : h ∈ PopGood ∧ ((∀ i, ‖X h i‖ ≤ D) ∧ (∀ i, ‖Y h i‖ ≤ D))
  · have hloc := heligible.2
    have hh := hh heligible.1
    obtain ⟨Good, hbudget, hrec⟩ := exists_actual_source_jump_event_of_source_moments
      c C g p q K D alpha C3 φ hc hC hp hq hK hD hφ hgrowth G U hU hSU hG hthirdG
      L hL (μ h) hh.1 halpha (k h) (seed h) hh.2.1 (X h) (Y h) (Xpost h) (Ypost h)
      hN hloc.1 hloc.2 eta u heta hu hu1
      ((hh.2.2 hloc).mono (fun _ hω => hω.1)) ((hh.2.2 hloc).mono (fun _ hω => hω.2))
    apply (measure_mono ?_).trans hbudget
    intro ω hbad hmem
    exact (not_lt_of_ge (hrec ω hmem)) hbad.2
  · have hempty : {ω | (h, ω) ∈ actualSourceJumpFailure c C g p q D φ G L
        PopGood μ X Y Xpost Ypost eta u} = ∅ := by
      ext ω
      simp only [actualSourceJumpFailure, mem_setOf_eq, heligible, false_and, mem_empty_iff_false]
    rw [hempty, measure_empty]
    exact bot_le

/-- The explicit measurable failure event inherits the same budget under the
actual history/sample joint law. This does not construct sequential conditional
couplings; it integrates the supplied unchanged kernel's derived bound. -/
theorem joint_actual_source_jump_failure_bound [IsProbabilityMeasure ρ]
    (hEvent : MeasurableSet (actualSourceJumpFailure c C g p q D φ G L
      PopGood μ X Y Xpost Ypost eta u)) :
    (ρ ⊗ₘ k) (actualSourceJumpFailure c C g p q D φ G L PopGood μ X Y Xpost Ypost eta u) ≤
      ENNReal.ofReal u := by
  rw [Measure.compProd_apply hEvent]
  calc
    _ ≤ ∫⁻ _h, ENNReal.ofReal u ∂ρ := lintegral_mono_ae
      (conditional_actual_source_jump_failure_bound c C g p q K D alpha C3 φ
        hc hC hp hq hK hD hφ hgrowth G U hU hSU hG hthirdG L hL halpha
        ρ k PopGood μ X Y Xpost Ypost seed hN eta u heta hu hu1 hgood)
    _ = _ := by simp

end PaperFormalization.Manuscript
