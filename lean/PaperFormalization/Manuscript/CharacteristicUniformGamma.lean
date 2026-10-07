import PaperFormalization.Manuscript.ConditionalUniformGammaComplete
import PaperFormalization.Manuscript.CharacteristicEvaluation

/-! # Source Gamma for the actual characteristic path product

The sampling kernel is constructed from the original iid initial seed law
and the common measurable characteristic map. Fixed-time iid, common laws
and joint particle measurability are derived. Actual population moments and
whole-branch path regularity remain explicit dynamical model obligations.
-/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ProbabilityTheory
namespace PaperFormalization.Manuscript
variable {G Seed Path E : Type*} [MeasurableSpace G] [MeasurableSpace Seed] [MeasurableSpace Path]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

set_option maxHeartbeats 1600000 in
/-- The exact source-weight uniform Gamma event for the constructed common
characteristic path product. No fixed-time iid/common-law or sample-map
measurability hypothesis is supplied. -/
theorem exists_characteristic_uniform_gamma_event
    (ρ : Measure G) [IsProbabilityMeasure ρ]
    (μ₀ : Measure Seed) [IsProbabilityMeasure μ₀]
    (Φ : G → Seed → Path) (hΦ : Measurable (fun z : G × Seed => Φ z.1 z.2))
    (L N : ℕ) (hN : 0 < N)
    (PopGood : Set G) (hPopGood : MeasurableSet PopGood)
    (Model : G × (Fin N → Path) → Prop)
    (hModel : ∀ᵐ z ∂(ρ ⊗ₘ characteristicProductKernel (ι := Fin N) μ₀ Φ), Model z)
    (a b : Fin (L+1) → ℝ) (hab : ∀ j, a j ≤ b j)
    (T : ℝ) (hlen : ∀ j, b j-a j ≤ T) (B : ℝ≥0)
    (c pDecay : ℝ) (Lfield : ℝ≥0) (hc : 0 < c) (hpDecay : 1 < pDecay)
    (Y : Fin (L+1) → G → Path → ℝ → E)
    (hY : ∀ j t, t ∈ Icc (a j) (b j) →
      Measurable (fun z : G × Path => Y j z.1 z.2 t))
    (C g q alpha K D c₀ K₀ M : ℝ) (hq : q < pDecay) (hC : 0 ≤ C)
    (hK : 0 < K) (hD : 1 ≤ D) (hc₀ : 0 ≤ c₀) (hK₀ : 0 < K₀) (halpha : 0 ≤ alpha)
    (φ : ∀ n, E → H n) (hφ : ∀ n, ContDiff ℝ 1 (φ n))
    (hvalue : ∀ n z, ‖φ n z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ (n+1)))
    (hderiv : ∀ n z, ‖fderiv ℝ (φ n) z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ n))
    (hpop : ∀ᵐ h ∂ρ, h ∈ PopGood →
      (∀ j, ∀ᵐ v ∂characteristicKernel μ₀ Φ h,
        LipschitzOnWith B (Y j h v) (Icc (a j) (b j))) ∧
      ∀ j t, t ∈ Icc (a j) (b j) →
        (characteristicKernel μ₀ Φ h).map (fun v => Y j h v t) ∈ sourceMomentClass alpha K ∧
        Integrable (fun z => Real.exp (c₀ * (‖z‖/K₀)^alpha))
          ((characteristicKernel μ₀ Φ h).map (fun v => Y j h v t)) ∧
        (∫ z, Real.exp (c₀ * (‖z‖/K₀)^alpha)
          ∂(characteristicKernel μ₀ Φ h).map (fun v => Y j h v t)) ≤ M)
    (hsamplePath : ∀ᵐ z ∂(ρ ⊗ₘ characteristicProductKernel (ι := Fin N) μ₀ Φ),
      z.1 ∈ PopGood → ∀ j i, LipschitzOnWith B (Y j z.1 (z.2 i)) (Icc (a j) (b j)))
    (Local : Set (G × (Fin N → Path)))
    (hlocal : ∀ z ∈ Local, ∀ j t, t ∈ Icc (a j) (b j) → ∀ i, ‖Y j z.1 (z.2 i) t‖ ≤ D)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    let A := 2 * ∑' n, ((featureResidualWeight c pDecay Lfield) n : ℝ) *
      (featureGrowth C g q n * (1 + D ^ (n+1)))
    let Λ := ∑' n, ((featureResidualWeight c pDecay Lfield) n : ℝ) *
      (featureGrowth C g q n * (1 + 2 * D ^ n))
    let S := ∑' n, ((featureResidualWeight c pDecay Lfield) n : ℝ) *
      sourceCoordinateL2Envelope C g q alpha K n
    let beta := 2 * S * Real.sqrt M * Real.exp (-(c₀ * (D/K₀)^alpha)/2)
    let Q := (((L+1 : ℕ) : ℝ) * ((N+1 : ℕ) : ℝ))
    ∃ Good : Set (G × (Fin N → Path)), MeasurableSet Good ∧
      (ρ ⊗ₘ characteristicProductKernel (ι := Fin N) μ₀ Φ).real Goodᶜ ≤ p ∧
      ∀ z ∈ Good, Model z ∧ (z.1 ∈ PopGood → z ∈ Local →
        ∀ j t, t ∈ Icc (a j) (b j) →
          weightedSampleResidual (featureResidualWeight c pDecay Lfield) φ
            (fun n => ∫ x, φ n x ∂(characteristicKernel μ₀ Φ z.1).map (fun v => Y j z.1 v t))
            (fun i => Y j z.1 (z.2 i) t) ≤
          beta + A / Real.sqrt N + A * Real.sqrt (Real.log (Q/p)/(2*N)) +
            2 * (B : ℝ) * T * Λ / N) := by
  letI : IsMarkovKernel (characteristicKernel μ₀ Φ) := (characteristicKernel_properties μ₀ Φ hΦ).1
  letI : IsMarkovKernel (characteristicProductKernel (ι := Fin N) μ₀ Φ) :=
    (characteristicProductKernel_properties μ₀ Φ hΦ).1
  have hev j t (ht : t ∈ Icc (a j) (b j)) :=
    characteristicProductKernel_evaluation_laws (ι := Fin N) μ₀ Φ hΦ
      (fun h v => Y j h v t) (hY j t ht)
  exact exists_conditional_uniform_gamma_event_of_source_weights ρ
    (characteristicProductKernel (ι := Fin N) μ₀ Φ) (characteristicKernel μ₀ Φ)
    PopGood hPopGood Model hModel L N hN a b hab T hlen B c pDecay Lfield hc hpDecay
    Y (fun j z i t => Y j z.1 (z.2 i) t) hY (fun j t ht => (hev j t ht).1)
    C g q alpha K D c₀ K₀ M hq hC hK hD hc₀ hK₀ halpha φ hφ hvalue hderiv
    hpop hsamplePath
    (fun j t ht => Filter.Eventually.of_forall (fun h _ => (hev j t ht).2 h |>.2))
    (fun j t ht => Filter.Eventually.of_forall (fun h _ => (hev j t ht).2 h |>.1))
    Local hlocal p hp hp1
end PaperFormalization.Manuscript
