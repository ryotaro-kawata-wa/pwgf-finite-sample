import PaperFormalization.Manuscript.SourceActualCoefficientSmallness
import PaperFormalization.Manuscript.SourcePopulationScaleRates

/-! # Actual population and radius choices in source bootstrap smallness

The original population moment scale and D=CD(1+log Xi)^(1/alpha) replace the
abstract scale-growth premises. The only stochastic-rate premises remaining
are the separately proved continuous and covariance residual bounds.
-/
open MeasureTheory Set Filter
open scoped BigOperators NNReal Topology
namespace PaperFormalization.Manuscript
open Continuous

variable {E : Type*} [Zero E] {H : ℕ → Type*}
  [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℝ (H n)]

/-- Literal population/radius choices imply eventual bootstrap smallness,
with the sample-size threshold chosen before the horizon, confidence,
schedule and actual response functions. -/
theorem eventually_source_population_coefficient_smallness
    (d : ℕ) (c C g pDecay q alpha C3 A_sp K0 CD : ℝ)
    (φ : ∀ n, E → H n) (G : lp H 2 → ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hpDecay : 1 < pDecay) (hq : q < pDecay)
    (halpha : 0 < alpha) (hA_sp : 0 ≤ A_sp) (hCD : 1 ≤ CD)
    (L0 : ℝ) (B : ℝ≥0) (Cp theta nu zeta Cg Ct C0 : ℝ)
    (hL0 : 0 ≤ L0) (htheta : 0 < theta) (hnu : 0 ≤ nu) (hzeta : 0 < zeta)
    (hCg : 0 ≤ Cg) (hCt : 0 ≤ Ct) (hC0 : 0 ≤ C0)
    (hexp : (5/4+Cp)*(L0+5/2)*theta ≤ zeta/2) :
    ∀ᶠ N : ℕ in atTop, ∀ (J : ℕ) (T p : ℝ), (J : ℝ) ≤ L0 → 0 ≤ T →
      0 < p → p ≤ 1 → T ≤ (N : ℝ)^(1/4-nu-zeta) → (N : ℝ)^(-Cp) ≤ p →
      let x := sourceGammaScale N J T B (3*p/8)
      let b := sourcePopulationExponentialScale alpha K0
      let A0 := 4*(populationGridBudget B J T : ℝ)/(p/8)
      let K := sourceExponentialMomentCoefficient alpha*sourcePopulationNormalizedScale alpha b A0
      let D := CD*(1+Real.log x)^(1/alpha)
      ∀ L : ℝ≥0, (L : ℝ) = sourceComparisonEnvelope c C g pDecay q K D alpha C3 φ G →
      let Lambda := featureDisplacementLambda c C g pDecay q D L
      let A := sourceJumpCoefficient d Lambda L*sourceGaussianDeviation (p/(8*((J : ℝ)+1)))
      let cD := Lambda+(2+A_sp)*(L : ℝ)
      ∀ (delta deltaTilde : ℝ) (kappa : ℝ → ℝ) (tau eta : ℕ → ℝ),
      delta ≤ Cg*x^theta*((Real.sqrt N)⁻¹+T/N) →
      deltaTilde ≤ Ct*x^theta*(Real.sqrt N)⁻¹ →
      (∀ i < J, 0 ≤ eta i ∧ eta i ≤ C0) →
      (∀ t ∈ Icc 0 T, (∫ s in (0 : ℝ)..t, propagator kappa t s) ≤ C0*(N : ℝ)^nu*(1+T)) →
      (∀ t ∈ Icc 0 T,
        (∑ i ∈ (Finset.range J).filter (fun i => tau (i+1) ≤ t),
          eta i*propagator kappa t (tau (i+1))) ≤ C0*(N : ℝ)^nu) →
      T*(delta+cD*(2*jumpAmplification (sourceJumpError A eta) J*
        sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A J T)) ≤ 1/4 := by
  obtain ⟨CK,CM,hCK,hCM,hscale⟩ := exists_source_population_tracking_scale_growth alpha K0 halpha
  have hsmall := eventually_source_actual_coefficient_smallness d c C g pDecay q alpha C3 A_sp
    CK (1/alpha) CD (1/alpha) φ G hc hC hpDecay hq halpha hA_sp L0 B Cp theta nu zeta Cg Ct C0
    hL0 B.coe_nonneg htheta hnu hzeta hCg hCt hC0 hexp
  filter_upwards [hsmall, eventually_ge_atTop 1] with N hNs hN1
  intro J T p hJ hT hp hp1 hTN hpN
  let x := sourceGammaScale N J T B (3*p/8)
  let b := sourcePopulationExponentialScale alpha K0
  let A0 := 4*(populationGridBudget B J T : ℝ)/(p/8)
  let K := sourceExponentialMomentCoefficient alpha*sourcePopulationNormalizedScale alpha b A0
  let D := CD*(1+Real.log x)^(1/alpha)
  have hN : 0 < N := by omega
  have hx : 2 ≤ x := (sourceGammaScale_bounds N J T B (3*p/8)
    hN hT B.coe_nonneg (by positivity) (by linarith)).1
  have hb : 0 < b := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  have hA0 : 2 ≤ A0 := by
    have hh := (source_population_grid_scale_bounds N J T B (p/8)
      hN hT (by positivity) (by linarith)).2.1
    dsimp [A0]
    linarith
  have hK : 0 < K := mul_pos
    (by unfold sourceExponentialMomentCoefficient; positivity)
    (sourcePopulationNormalizedScale_pow alpha b A0 halpha hb hA0).1
  have hD : 1 ≤ D := by
    have hl : 1 ≤ 1+Real.log x := by linarith [Real.log_nonneg (show 1 ≤ x by linarith)]
    have hpow := Real.one_le_rpow hl (show 0 ≤ 1/alpha by positivity)
    dsimp [D]
    nlinarith [mul_le_mul hCD hpow (by norm_num : (0 : ℝ) ≤ 1) (by linarith)]
  have hKb : K ≤ CK*(1+Real.log x)^(1/alpha) := (hscale N J T B p hN hT hp hp1).1
  exact hNs J T p hJ hT hp hp1 hTN hpN K D hK hD hKb le_rfl

end PaperFormalization.Manuscript
