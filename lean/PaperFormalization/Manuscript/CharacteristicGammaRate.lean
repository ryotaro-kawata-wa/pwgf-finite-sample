import PaperFormalization.Manuscript.CharacteristicUniformGamma
import PaperFormalization.Manuscript.SourceGammaConvenientRate

/-! # Actual characteristic Gamma event with the convenient source rate

One radius coefficient, rate coefficient and sample threshold are chosen
before all running parameters and before the population law and common
characteristic map. The actual finite-grid threshold is absorbed internally;
no desired concentration rate is supplied as a hypothesis.
-/
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators ProbabilityTheory
namespace PaperFormalization.Manuscript
variable {Env Seed Path E : Type*} [MeasurableSpace Env] [MeasurableSpace Seed]
  [MeasurableSpace Path] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

set_option maxHeartbeats 1600000 in
/-- The actual measurable characteristic-product event has loss at most p/3
and the convenient source rate with constants uniform in N,J,T,B,p,K,Mpop,L.
Any fixed minimum radius coefficient can be imposed before these parameters. -/
theorem exists_characteristic_uniform_gamma_rate
    (c C g pDecay q alpha C3 CK sK CM cM c₀ K₀ epsilon CDmin : ℝ)
    (φ : ∀ n, E → H n) (G : lp H 2 → ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hpDecay : 1 < pDecay) (hq : q < pDecay)
    (halpha : 0 < alpha) (hCM : 0 ≤ CM) (hcM : 0 ≤ cM)
    (hc₀ : 0 < c₀) (hK₀ : 0 < K₀) (he : 0 < epsilon)
    (hφ : ∀ n, ContDiff ℝ 1 (φ n))
    (hvalue : ∀ n z, ‖φ n z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ (n+1)))
    (hderiv : ∀ n z, ‖fderiv ℝ (φ n) z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ n)) :
    ∃ CD : ℝ, CDmin ≤ CD ∧ 1 ≤ CD ∧ ∃ M : ℝ, 0 < M ∧ ∃ N0 : ℕ, 0 < N0 ∧
      ∀ N J : ℕ, N0 ≤ N → ∀ (T : ℝ) (B : ℝ≥0) (p : ℝ), 0 ≤ T → 0 < p → p ≤ 1 →
      let x := sourceGammaScale N J T B p
      let D := CD*(1+Real.log x)^(1/alpha)
      ∀ K Mpop : ℝ, 0 < K → K ≤ CK*(1+Real.log x)^sK → Mpop ≤ CM*x^cM →
      ∀ Lfield : ℝ≥0,
        (Lfield : ℝ) ≤ |sourceComparisonEnvelope c C g pDecay q K D alpha C3 φ G| →
      ∀ (ρ : Measure Env) (_hρ : IsProbabilityMeasure ρ)
        (μ₀ : Measure Seed) (_hμ₀ : IsProbabilityMeasure μ₀)
        (Φ : Env → Seed → Path), Measurable (fun z : Env × Seed => Φ z.1 z.2) →
      ∀ (a b : Fin (J+1) → ℝ), (∀ j, a j ≤ b j) → (∀ j, b j-a j ≤ T) →
      ∀ (PopGood : Set Env), MeasurableSet PopGood →
      ∀ (Model : Env × (Fin N → Path) → Prop),
        (∀ᵐ z ∂(ρ ⊗ₘ characteristicProductKernel (ι := Fin N) μ₀ Φ), Model z) →
      ∀ (Y : Fin (J+1) → Env → Path → ℝ → E),
        (∀ j t, t ∈ Icc (a j) (b j) →
          Measurable (fun z : Env × Path => Y j z.1 z.2 t)) →
        (∀ᵐ h ∂ρ, h ∈ PopGood →
          (∀ j, ∀ᵐ v ∂characteristicKernel μ₀ Φ h,
            LipschitzOnWith B (Y j h v) (Icc (a j) (b j))) ∧
          ∀ j t, t ∈ Icc (a j) (b j) →
            (characteristicKernel μ₀ Φ h).map (fun v => Y j h v t) ∈ sourceMomentClass alpha K ∧
            Integrable (fun z => Real.exp (c₀ * (‖z‖/K₀)^alpha))
              ((characteristicKernel μ₀ Φ h).map (fun v => Y j h v t)) ∧
            (∫ z, Real.exp (c₀ * (‖z‖/K₀)^alpha)
              ∂(characteristicKernel μ₀ Φ h).map (fun v => Y j h v t)) ≤ Mpop) →
        (∀ᵐ z ∂(ρ ⊗ₘ characteristicProductKernel (ι := Fin N) μ₀ Φ),
          z.1 ∈ PopGood → ∀ j i, LipschitzOnWith B (Y j z.1 (z.2 i)) (Icc (a j) (b j))) →
      ∀ (Local : Set (Env × (Fin N → Path))),
        (∀ z ∈ Local, ∀ j t, t ∈ Icc (a j) (b j) → ∀ i, ‖Y j z.1 (z.2 i) t‖ ≤ D) →
      ∃ Good : Set (Env × (Fin N → Path)), MeasurableSet Good ∧
        (ρ ⊗ₘ characteristicProductKernel (ι := Fin N) μ₀ Φ).real Goodᶜ ≤ p/3 ∧
        ∀ z ∈ Good, Model z ∧ (z.1 ∈ PopGood → z ∈ Local →
          ∀ j t, t ∈ Icc (a j) (b j) →
            weightedSampleResidual (featureResidualWeight c pDecay Lfield) φ
              (fun n => ∫ x, φ n x ∂(characteristicKernel μ₀ Φ z.1).map (fun v => Y j z.1 v t))
              (fun i => Y j z.1 (z.2 i) t) ≤
            M*x^epsilon*((Real.sqrt N)⁻¹+(B : ℝ)*T/N)) := by
  obtain ⟨CD,hCDmin,hCD,M,hM,N0,hN0,hrate⟩ :=
    exists_source_gamma_convenient_threshold_rate c C g pDecay q alpha C3 CK sK CM cM
      c₀ K₀ epsilon CDmin φ G hc hC hpDecay hq halpha hCM hcM hc₀ hK₀ he
  refine ⟨CD,hCDmin,hCD,M,hM,N0,hN0,?_⟩
  intro N J hN0N T B p hT hp hp1
  let x := sourceGammaScale N J T B p
  let D := CD*(1+Real.log x)^(1/alpha)
  dsimp only
  intro K Mpop hK hKb hMb Lfield hL ρ hρ μ₀ hμ₀ Φ hΦ a b hab hlen
    PopGood hPopGood Model hModel Y hY hpop hsamplePath Local hlocal
  letI : IsProbabilityMeasure ρ := hρ
  letI : IsProbabilityMeasure μ₀ := hμ₀
  have hN : 0 < N := hN0.trans_le hN0N
  have hx : 2 ≤ x := (sourceGammaScale_bounds N J T B p hN hT B.coe_nonneg hp hp1).1
  have hD : 1 ≤ D := by
    have hb : 1 ≤ 1+Real.log x := by linarith [Real.log_nonneg (by linarith : 1 ≤ x)]
    have hpow := Real.one_le_rpow hb (show 0 ≤ 1/alpha by positivity)
    dsimp [D]
    nlinarith
  obtain ⟨Good,hGood,hbudget,hbound⟩ := exists_characteristic_uniform_gamma_event
    ρ μ₀ Φ hΦ J N hN PopGood hPopGood Model hModel a b hab T hlen B
    c pDecay Lfield hc hpDecay Y hY C g q alpha K D c₀ K₀ Mpop hq hC hK hD
    hc₀.le hK₀ halpha.le φ hφ hvalue hderiv hpop hsamplePath Local hlocal
    (p/3) (by positivity) (by linarith)
  have hb := hrate N J hN0N T B p hT B.coe_nonneg hp hp1 K Mpop hK hKb hMb Lfield hL
  refine ⟨Good,hGood,hbudget,?_⟩
  intro z hz
  refine ⟨(hbound z hz).1,?_⟩
  intro helig hloc j t ht
  exact ((hbound z hz).2 helig hloc j t ht).trans hb
end PaperFormalization.Manuscript
