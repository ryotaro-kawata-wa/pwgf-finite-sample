import PaperFormalization.Manuscript.SourceUniformGamma
import PaperFormalization.Manuscript.SourceClippedSeries

/-! # The exact source-weight localized uniform Gamma bound

The fixed-law application derives node concentration, time interpolation and
population bias internally. Branch labels retain distinct endpoint traces.
The original conditional path-law construction remains an external model
obligation; no independence is inferred after sample localization.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal
namespace PaperFormalization.Manuscript
variable {Ω Ξ E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

set_option maxHeartbeats 1600000 in
/-- The actual source weights discharge all three summability inputs internally. -/
theorem source_uniform_gamma_failure_le_of_source_weights
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (L N : ℕ) (hN : 0 < N) (a b : Fin (L+1) → ℝ) (hab : ∀ j, a j ≤ b j)
    (T : ℝ) (hlen : ∀ j, b j-a j ≤ T) (B : ℝ≥0)
    (c pDecay : ℝ) (Lfield : ℝ≥0) (hc : 0 < c) (hpDecay : 1 < pDecay)
    (Y : Fin (L+1) → Ω → ℝ → E) (X : Fin (L+1) → Ξ → Fin N → ℝ → E)
    (C g q alpha K D c₀ K₀ M : ℝ) (hq : q < pDecay) (hC : 0 ≤ C) (hK : 0 < K) (hD : 1 ≤ D)
    (hc₀ : 0 ≤ c₀) (hK₀ : 0 < K₀) (halpha : 0 ≤ alpha)
    (φ : ∀ n, E → H n) (hφ : ∀ n, ContDiff ℝ 1 (φ n))
    (hvalue : ∀ n z, ‖φ n z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ (n+1)))
    (hderiv : ∀ n z, ‖fderiv ℝ (φ n) z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ n))
    (hclass : ∀ j t, t ∈ Icc (a j) (b j) →
      μ.map (fun ω => Y j ω t) ∈ sourceMomentClass alpha K)
    (hexp : ∀ j t, t ∈ Icc (a j) (b j) →
      Integrable (fun z => Real.exp (c₀ * (‖z‖/K₀)^alpha)) (μ.map (fun ω => Y j ω t)))
    (hM : ∀ j t, t ∈ Icc (a j) (b j) →
      (∫ z, Real.exp (c₀ * (‖z‖/K₀)^alpha) ∂μ.map (fun ω => Y j ω t)) ≤ M)
    (hpopPath : ∀ j, ∀ᵐ ω ∂μ, LipschitzOnWith B (Y j ω) (Icc (a j) (b j)))
    (hsamplePath : ∀ j, ∀ᵐ ξ ∂ν, ∀ i, LipschitzOnWith B (X j ξ i) (Icc (a j) (b j)))
    (hLaw : ∀ j t, t ∈ Icc (a j) (b j) → ∀ i,
      ν.map (fun ξ => X j ξ i t) = μ.map (fun ω => Y j ω t))
    (hind : ∀ j t, t ∈ Icc (a j) (b j) → iIndepFun (fun i ξ => X j ξ i t) ν)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    let A := 2 * ∑' n, ((featureResidualWeight c pDecay Lfield) n : ℝ) * (featureGrowth C g q n * (1 + D ^ (n+1)))
    let Λ := ∑' n, ((featureResidualWeight c pDecay Lfield) n : ℝ) * (featureGrowth C g q n * (1 + 2 * D ^ n))
    let S := ∑' n, ((featureResidualWeight c pDecay Lfield) n : ℝ) * sourceCoordinateL2Envelope C g q alpha K n
    let beta := 2 * S * Real.sqrt M * Real.exp (-(c₀ * (D/K₀)^alpha)/2)
    let Q := (((L+1 : ℕ) : ℝ) * ((N+1 : ℕ) : ℝ))
    ν.real {ξ | (∀ j t, t ∈ Icc (a j) (b j) → ∀ i, ‖X j ξ i t‖ ≤ D) ∧
      ∃ j, ∃ t ∈ Icc (a j) (b j),
        beta + A / Real.sqrt N + A * Real.sqrt (Real.log (Q/p)/(2*N)) +
          2 * (B : ℝ) * T * Λ / N <
        weightedSampleResidual (featureResidualWeight c pDecay Lfield) φ (fun n => ∫ z, φ n z ∂μ.map (fun ω => Y j ω t))
          (fun i => X j ξ i t)} ≤ p := by
  exact source_uniform_gamma_failure_le μ ν L N hN a b hab T hlen B Y X
    C g q alpha K D c₀ K₀ M hC hK (by linarith) hc₀ hK₀ halpha
    (featureResidualWeight c pDecay Lfield) φ hφ hvalue hderiv hclass hexp hM hpopPath hsamplePath hLaw hind
    (summable_source_clipped_amplitude c C g pDecay q D Lfield hc hpDecay hq hD)
    (summable_source_clipped_rate c C g pDecay q D Lfield hc hC hpDecay hq hD)
    (summable_source_clipping_L2_envelope c C g pDecay q alpha K Lfield hc hpDecay hq hK)
    p hp hp1

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E]
  [SecondCountableTopology E] [∀ n, CompleteSpace (H n)] in
/-- The sample statistic is precisely the previously checked source moment
residual, with exact finite empirical normalization. -/
theorem weightedSampleResidual_eq_actual_momentResidual {N : ℕ}
    (μ : Measure E) (w : ℕ → ℝ≥0) (φ : ∀ n, E → H n) (X : Fin N → E) (t : ℝ) :
    weightedSampleResidual w φ (fun n => ∫ z, φ n z ∂μ) X =
      momentResidual w (fun n _ => finiteFeatureMean (fun i => φ n (X i)))
        (fun n _ => ∫ z, φ n z ∂μ) t := by
  simp only [weightedSampleResidual, momentResidual, momentResidualTerm,
    finiteFeatureMean, Fintype.card_fin]
end PaperFormalization.Manuscript
