import PaperFormalization.Manuscript.ConditionalUniformGamma
import PaperFormalization.Manuscript.SourceClippedSeries

/-! # Exact source-weight conditional uniform Gamma event

The original joint probability and population path kernels are unchanged.
All three source series are proved convergent internally; independence is
required only before localization, on eligible population histories.
-/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ProbabilityTheory
namespace PaperFormalization.Manuscript
variable {G Ω Ξ E : Type*} [MeasurableSpace G] [MeasurableSpace Ω] [MeasurableSpace Ξ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

set_option maxHeartbeats 1600000 in
/-- The exact source weights discharge all amplitude, time-rate and L2 series
requirements in the measurable conditional all-branch Gamma event. -/
theorem exists_conditional_uniform_gamma_event_of_source_weights
    (ρ : Measure G) [IsProbabilityMeasure ρ]
    (k : Kernel G Ξ) [IsMarkovKernel k] (μ : Kernel G Ω) [IsMarkovKernel μ]
    (PopGood : Set G) (hPopGood : MeasurableSet PopGood)
    (Model : G × Ξ → Prop) (hModel : ∀ᵐ z ∂(ρ ⊗ₘ k), Model z)
    (L N : ℕ) (hN : 0 < N) (a b : Fin (L+1) → ℝ) (hab : ∀ j, a j ≤ b j)
    (T : ℝ) (hlen : ∀ j, b j-a j ≤ T) (B : ℝ≥0)
    (c pDecay : ℝ) (Lfield : ℝ≥0) (hc : 0 < c) (hpDecay : 1 < pDecay)
    (Y : Fin (L+1) → G → Ω → ℝ → E)
    (X : Fin (L+1) → G × Ξ → Fin N → ℝ → E)
    (hY : ∀ j t, t ∈ Icc (a j) (b j) →
      Measurable (fun z : G × Ω => Y j z.1 z.2 t))
    (hX : ∀ j t, t ∈ Icc (a j) (b j) → ∀ i,
      Measurable (fun z => X j z i t))
    (C g q alpha K D c₀ K₀ M : ℝ) (hq : q < pDecay) (hC : 0 ≤ C) (hK : 0 < K) (hD : 1 ≤ D)
    (hc₀ : 0 ≤ c₀) (hK₀ : 0 < K₀) (halpha : 0 ≤ alpha)
    (φ : ∀ n, E → H n) (hφ : ∀ n, ContDiff ℝ 1 (φ n))
    (hvalue : ∀ n z, ‖φ n z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ (n+1)))
    (hderiv : ∀ n z, ‖fderiv ℝ (φ n) z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ n))
    (hpop : ∀ᵐ h ∂ρ, h ∈ PopGood →
      (∀ j, ∀ᵐ ω ∂μ h, LipschitzOnWith B (Y j h ω) (Icc (a j) (b j))) ∧
      ∀ j t, t ∈ Icc (a j) (b j) →
        (μ h).map (fun ω => Y j h ω t) ∈ sourceMomentClass alpha K ∧
        Integrable (fun z => Real.exp (c₀ * (‖z‖/K₀)^alpha)) ((μ h).map (fun ω => Y j h ω t)) ∧
        (∫ z, Real.exp (c₀ * (‖z‖/K₀)^alpha) ∂(μ h).map (fun ω => Y j h ω t)) ≤ M)
    (hsamplePath : ∀ᵐ z ∂(ρ ⊗ₘ k), z.1 ∈ PopGood →
      ∀ j i, LipschitzOnWith B (X j z i) (Icc (a j) (b j)))
    (hLaw : ∀ j t, t ∈ Icc (a j) (b j) → ∀ᵐ h ∂ρ, h ∈ PopGood → ∀ i,
      (k h).map (fun ξ => X j (h,ξ) i t) = (μ h).map (fun ω => Y j h ω t))
    (hind : ∀ j t, t ∈ Icc (a j) (b j) → ∀ᵐ h ∂ρ, h ∈ PopGood →
      iIndepFun (fun i ξ => X j (h,ξ) i t) (k h))
    (Local : Set (G × Ξ))
    (hlocal : ∀ z ∈ Local, ∀ j t, t ∈ Icc (a j) (b j) → ∀ i, ‖X j z i t‖ ≤ D)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    let A := 2 * ∑' n, ((featureResidualWeight c pDecay Lfield) n : ℝ) * (featureGrowth C g q n * (1 + D ^ (n+1)))
    let Λ := ∑' n, ((featureResidualWeight c pDecay Lfield) n : ℝ) * (featureGrowth C g q n * (1 + 2 * D ^ n))
    let S := ∑' n, ((featureResidualWeight c pDecay Lfield) n : ℝ) * sourceCoordinateL2Envelope C g q alpha K n
    let beta := 2 * S * Real.sqrt M * Real.exp (-(c₀ * (D/K₀)^alpha)/2)
    let Q := (((L+1 : ℕ) : ℝ) * ((N+1 : ℕ) : ℝ))
    ∃ Good : Set (G × Ξ), MeasurableSet Good ∧ (ρ ⊗ₘ k).real Goodᶜ ≤ p ∧
      ∀ z ∈ Good, Model z ∧ (z.1 ∈ PopGood → z ∈ Local →
        ∀ j t, t ∈ Icc (a j) (b j) →
          weightedSampleResidual (featureResidualWeight c pDecay Lfield) φ
            (fun n => ∫ x, φ n x ∂(μ z.1).map (fun ω => Y j z.1 ω t)) (fun i => X j z i t) ≤
          beta + A / Real.sqrt N + A * Real.sqrt (Real.log (Q/p)/(2*N)) +
            2 * (B : ℝ) * T * Λ / N) := by
  exact exists_conditional_uniform_gamma_event ρ k μ PopGood hPopGood Model hModel
    L N hN a b hab T hlen B Y X hY hX C g q alpha K D c₀ K₀ M hC hK (by linarith)
    hc₀ hK₀ halpha (featureResidualWeight c pDecay Lfield) φ hφ hvalue hderiv
    hpop hsamplePath hLaw hind Local hlocal
    (summable_source_clipped_amplitude c C g pDecay q D Lfield hc hpDecay hq hD)
    (summable_source_clipped_rate c C g pDecay q D Lfield hc hC hpDecay hq hD)
    (summable_source_clipping_L2_envelope c C g pDecay q alpha K Lfield hc hpDecay hq hK)
    p hp hp1
end PaperFormalization.Manuscript
