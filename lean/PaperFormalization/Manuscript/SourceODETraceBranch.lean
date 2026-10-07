import PaperFormalization.Manuscript.SourceODEBranch

/-! # Actual source ODEs and one-sided particle traces on a jump branch

This adapter supplies the exact scalar closed-branch regularity and original
path drift used by SourceTracking. The endpoint value is the genuine pre-jump
particle discrepancy; the actual post-jump value stays unrestricted. No
scalar differential or jump inequality is assumed.
-/
open MeasureTheory Set Filter
open scoped NNReal BigOperators Topology
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

/-- Interior particle Lipschitz paths, actual one-sided traces, and the
actual source ODEs give both the AC branch with its true pre-jump discrepancy
and the nonlinear drift of the unchanged original path, including zero r. -/
theorem source_ode_branch_of_actual_traces
    (mu : ℝ → Measure E) (X Y : ℝ → PiLp 2 fun _ : Fin N => E)
    (preX preY : PiLp 2 fun _ : Fin N => E)
    (a b A_sp : ℝ) (B : ℝ≥0) (hN : 0 < N) (hab : a < b)
    (hXlip : ∀ i, LipschitzOnWith B (fun t => X t i) (Ioo a b))
    (hYlip : ∀ i, LipschitzOnWith B (fun t => Y t i) (Ioo a b))
    (hXa : ∀ i, Tendsto (fun t => X t i) (𝓝[>] a) (𝓝 (X a i)))
    (hYa : ∀ i, Tendsto (fun t => Y t i) (𝓝[>] a) (𝓝 (Y a i)))
    (hXb : ∀ i, Tendsto (fun t => X t i) (𝓝[<] b) (𝓝 (preX i)))
    (hYb : ∀ i, Tendsto (fun t => Y t i) (𝓝[<] b) (𝓝 (preY i)))
    (hgood : ∀ᵐ t ∂volume.restrict (Ioo a b),
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
    let pre := ‖preX - preY‖ / Real.sqrt N
    let kappa := fun t => rayleighInf (sampledMomentHessian J G (∫ z, J z ∂(mu t)) (Y t))
    let Gamma := momentResidual (featureResidualWeight c p L)
      (fun n t => finiteFeatureMean (fun i => φ n (Y t i))) (fun n t => ∫ z, φ n z ∂(mu t))
    AbsolutelyContinuousOnInterval (closedBranch r b pre) a b ∧
      Tendsto r (𝓝[<] b) (𝓝 pre) ∧ (∀ t, 0 ≤ Gamma t) ∧
      ∀ᵐ t ∂volume.restrict (Ioo a b),
        deriv r t ≤ -kappa t * r t +
          (featureDisplacementLambda c C g p q D L + (2 + A_sp) * (L : ℝ)) * (r t) ^ 2 +
          Gamma t * r t + Gamma t := by
  have hac := normalizedDiscrepancy_closedBranch_ac (fun t i => X t i) (fun t i => Y t i)
    a b (fun i => preX i) (fun i => preY i) B hN hab hXlip hYlip hXa hYa hXb hYb
  have hleft := normalizedDiscrepancy_tendsto_left (fun t i => X t i) (fun t i => Y t i)
    a b (fun i => preX i) (fun i => preY i) B hN hab hXlip hYlip hXa hYa hXb hYb
  refine ⟨hac, hleft, fun t => momentResidual_nonneg _ _ _ t, ?_⟩
  have hode := source_ode_ae_drift c C g p q K D alpha C3 φ
    hc hC hp hq hK hD hφ hgrowth hthirdφ hgrowth₃ G U hU hSU hG hthirdG L hL
    mu X Y a b A_sp hN (by rwa [← restrict_Ioo_eq_restrict_Icc])
  simpa only [← restrict_Ioo_eq_restrict_Icc] using hode
end PaperFormalization.Manuscript
