import PaperFormalization.Manuscript.SourceODEDrift
import PaperFormalization.Manuscript.ZeroDiscrepancy
import PaperFormalization.Manuscript.SourceMomentPathRegularity
import PaperFormalization.Manuscript.SourceCurvaturePath

/-! # Actual-model drift almost everywhere on one closed branch

A common AE good-time event supplies the actual empirical and population ODEs,
localization, anti-spikiness, and membership of the supplied population law in
the original all-real-order class. The positive-discrepancy source theorem
and the checked zero-discrepancy argument yield the full scalar inequality.
Particle Lipschitz paths give genuine absolute continuity; no C1 path
assumption and no differentiability of the population law is introduced.

Closed-branch paths use their chosen endpoint values. Applying this unit to a
jump branch requires the existing actual one-sided trace representatives;
no Lipschitz continuity across a jump is asserted.
-/

open MeasureTheory Set Filter
open scoped NNReal BigOperators

set_option maxSynthPendingDepth 8

namespace PaperFormalization.Manuscript

open Continuous

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]
variable {N : ℕ}

variable (c C g p q K D alpha C3 : ℝ) (φ : ∀ n, E → H n)
  (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (hD : 1 ≤ D)
  (hφ : ∀ n, ContDiff ℝ 2 (φ n))
  (hgrowth : ∀ n z k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) z‖ ≤
    featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1 - k)))
  (hthirdφ : ∀ n z, DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ (φ n))) z)
  (hgrowth₃ : ∀ n z, ‖iteratedFDeriv ℝ 3 (φ n) z‖ ≤
    featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1 - 3)))
  (G : lp H 2 → ℝ) (U : Set (lp H 2)) (hU : IsOpen U)
  (hSU : measureMomentRegion (sourceWeightedFeatureMap c p φ) (sourceMomentClass alpha K) D ⊆ U)
  (hG : ContDiffOn ℝ 3 G U)
  (hthirdG : ∀ theta ∈ measureMomentRegion (sourceWeightedFeatureMap c p φ)
      (sourceMomentClass alpha K) D, ‖iteratedFDeriv ℝ 3 G theta‖ ≤ C3)
  (L : ℝ≥0) (hL : (L : ℝ) = sourceComparisonEnvelope c C g p q K D alpha C3 φ G)

include hc hC hp hq hK hD hφ hgrowth hthirdφ hgrowth₃ hU hSU hG hthirdG hL

/-- Actual source-model drift on a single common AE good-time event, including
zero discrepancy. Gamma nonnegativity follows from its literal series. -/
theorem source_ode_ae_drift
    (mu : ℝ → Measure E) (X Y : ℝ → PiLp 2 fun _ : Fin N => E)
    (a b A_sp : ℝ) (hN : 0 < N)
    (hgood : ∀ᵐ t ∂volume.restrict (Icc a b),
      mu t ∈ sourceMomentClass alpha K ∧
      (∀ i, ‖X t i‖ ≤ D) ∧ (∀ i, ‖Y t i‖ ≤ D) ∧
      (N : ℝ)⁻¹ * ∑ i : Fin N, ‖(X t - Y t) i‖ ^ 3 ≤
        A_sp * (‖X t - Y t‖ / Real.sqrt N) ^ 3 ∧
      HasDerivAt X
        (empiricalConfigurationField (sourceWeightedFeatureMap c p φ)
          (momentGradientField (fderiv ℝ (sourceWeightedFeatureMap c p φ)) (gradient G)) (X t)) t ∧
      HasDerivAt Y
        (frozenMomentConfigurationField
          (momentGradientField (fderiv ℝ (sourceWeightedFeatureMap c p φ)) (gradient G))
          (∫ z, sourceWeightedFeatureMap c p φ z ∂(mu t)) (Y t)) t) :
    let J := sourceWeightedFeatureMap c p φ
    let r := fun t => ‖X t - Y t‖ / Real.sqrt N
    let kappa := fun t => rayleighInf (sampledMomentHessian J G (∫ z, J z ∂(mu t)) (Y t))
    let Gamma := momentResidual (featureResidualWeight c p L)
      (fun n t => finiteFeatureMean (fun i => φ n (Y t i))) (fun n t => ∫ z, φ n z ∂(mu t))
    ∀ᵐ t ∂volume.restrict (Icc a b),
      deriv r t ≤ -kappa t * r t +
        (featureDisplacementLambda c C g p q D L + (2 + A_sp) * (L : ℝ)) * (r t) ^ 2 +
        Gamma t * r t + Gamma t := by
  rw [← restrict_Ioo_eq_restrict_Icc] at hgood ⊢
  apply ae_deriv_le_nonlinear_of_pos
  · intro t _
    exact div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  · exact Eventually.of_forall (fun t => momentResidual_nonneg _ _ _ t)
  · filter_upwards [hgood] with t ht
    obtain ⟨hmu, hXt, hYt, hanti, hXode, hYode⟩ := ht
    intro hpos
    exact source_ode_discrepancy_deriv_le c C g p q K D alpha C3 φ
      hc hC hp hq hK hD hφ hgrowth hthirdφ hgrowth₃ G U hU hSU hG hthirdG L hL
      (mu t) hmu X Y t hN hXt hYt A_sp hanti hXode hYode hpos

/-- Localized source ODEs together with actual particle Lipschitz paths give
an absolutely continuous normalized discrepancy and the full AE scalar drift.
The normalization remains 1/sqrt(N); no sqrt(N) enters the nonlinear constant. -/
theorem source_ode_closed_branch
    (mu : ℝ → Measure E) (X Y : ℝ → PiLp 2 fun _ : Fin N => E)
    (a b A_sp : ℝ) (B : ℝ≥0) (hN : 0 < N)
    (hXlip : ∀ i, LipschitzOnWith B (fun t => X t i) (uIcc a b))
    (hYlip : ∀ i, LipschitzOnWith B (fun t => Y t i) (uIcc a b))
    (hgood : ∀ᵐ t ∂volume.restrict (Icc a b),
      mu t ∈ sourceMomentClass alpha K ∧
      (∀ i, ‖X t i‖ ≤ D) ∧ (∀ i, ‖Y t i‖ ≤ D) ∧
      (N : ℝ)⁻¹ * ∑ i : Fin N, ‖(X t - Y t) i‖ ^ 3 ≤
        A_sp * (‖X t - Y t‖ / Real.sqrt N) ^ 3 ∧
      HasDerivAt X
        (empiricalConfigurationField (sourceWeightedFeatureMap c p φ)
          (momentGradientField (fderiv ℝ (sourceWeightedFeatureMap c p φ)) (gradient G)) (X t)) t ∧
      HasDerivAt Y
        (frozenMomentConfigurationField
          (momentGradientField (fderiv ℝ (sourceWeightedFeatureMap c p φ)) (gradient G))
          (∫ z, sourceWeightedFeatureMap c p φ z ∂(mu t)) (Y t)) t) :
    let J := sourceWeightedFeatureMap c p φ
    let r := fun t => ‖X t - Y t‖ / Real.sqrt N
    let kappa := fun t => rayleighInf (sampledMomentHessian J G (∫ z, J z ∂(mu t)) (Y t))
    let Gamma := momentResidual (featureResidualWeight c p L)
      (fun n t => finiteFeatureMean (fun i => φ n (Y t i))) (fun n t => ∫ z, φ n z ∂(mu t))
    AbsolutelyContinuousOnInterval r a b ∧ (∀ t, 0 ≤ Gamma t) ∧
      ∀ᵐ t ∂volume.restrict (Icc a b),
        deriv r t ≤ -kappa t * r t +
          (featureDisplacementLambda c C g p q D L + (2 + A_sp) * (L : ℝ)) * (r t) ^ 2 +
          Gamma t * r t + Gamma t := by
  refine ⟨?_, fun t => momentResidual_nonneg _ _ _ t, ?_⟩
  · exact normalizedDiscrepancy_ac (fun t i => X t i) (fun t i => Y t i) a b B hN hXlip hYlip
  · exact source_ode_ae_drift c C g p q K D alpha C3 φ
      hc hC hp hq hK hD hφ hgrowth hthirdφ hgrowth₃ G U hU hSU hG hthirdG L hL
      mu X Y a b A_sp hN hgood

end PaperFormalization.Manuscript
