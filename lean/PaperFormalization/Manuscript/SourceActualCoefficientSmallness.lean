import PaperFormalization.Manuscript.SourceBootstrapSmallness
import PaperFormalization.Manuscript.SourceJumpRateCoefficients

/-! # Original source coefficients discharge bootstrap coefficient-rate inputs

The actual drift coefficient and c_J times its printed Gaussian factor are
constructed from the source series and local objective coefficient. Their
bounds are derived with constants chosen before N,T,p,K,D and the schedule.
The continuous and covariance residual rates remain the separate stochastic
inputs; no probability event or conditional-law identification is asserted.
-/
open MeasureTheory Set Filter
open scoped BigOperators NNReal Topology
namespace PaperFormalization.Manuscript
open Continuous

variable {E : Type*} [Zero E] {H : ℕ → Type*}
  [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℝ (H n)]

/-- The literal source drift coefficient is subpolynomial under the two
original radius bounds, retaining the fixed anti-spikiness parameter. -/
theorem exists_source_drift_coefficient_subpolynomial
    (c C g pDecay q alpha C3 A_sp CK sK CD sD epsilon : ℝ)
    (φ : ∀ n, E → H n) (G : lp H 2 → ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hpDecay : 1 < pDecay) (hq : q < pDecay)
    (halpha : 0 < alpha) (hA_sp : 0 ≤ A_sp) (he : 0 < epsilon) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, 2 ≤ x → ∀ K D : ℝ,
      0 < K → 1 ≤ D → K ≤ CK*(1+Real.log x)^sK → D ≤ CD*(1+Real.log x)^sD →
      ∀ L : ℝ≥0, (L : ℝ) = sourceComparisonEnvelope c C g pDecay q K D alpha C3 φ G →
      featureDisplacementLambda c C g pDecay q D L+(2+A_sp)*(L : ℝ) ≤ M*x^epsilon := by
  obtain ⟨A,hA,hsource⟩ := exists_uniform_source_drift_coefficient_bound
    c C g pDecay q alpha C3 A_sp φ G hc hC hpDecay hq halpha hA_sp
  obtain ⟨M,hM,hbound⟩ := exists_exp_chi_source_scales_le_rpow A A pDecay CK sK CD sD epsilon
    hA.le hA.le hpDecay he
  refine ⟨M,hM,?_⟩
  intro x hx K D hK hD hKb hDb L hL
  exact (hsource K hK D hD L hL).trans (hbound x hx K D hK.le (by linarith) hKb hDb)

set_option maxHeartbeats 1200000 in
/-- Under the proved residual rates, the original source coefficients and
actual controlled curvature responses imply the source stability event for
all sufficiently large N, uniformly in every admissible horizon and confidence.
No drift/jump coefficient bound, radius bound, or stability bound is assumed. -/
theorem eventually_source_actual_coefficient_smallness
    (d : ℕ) (c C g pDecay q alpha C3 A_sp CK sK CD sD : ℝ)
    (φ : ∀ n, E → H n) (G : lp H 2 → ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hpDecay : 1 < pDecay) (hq : q < pDecay)
    (halpha : 0 < alpha) (hA_sp : 0 ≤ A_sp)
    (L0 B Cp theta nu zeta Cg Ct C0 : ℝ)
    (hL0 : 0 ≤ L0) (hB : 0 ≤ B) (htheta : 0 < theta) (hnu : 0 ≤ nu) (hzeta : 0 < zeta)
    (hCg : 0 ≤ Cg) (hCt : 0 ≤ Ct) (hC0 : 0 ≤ C0)
    (hexp : (5/4+Cp)*(L0+5/2)*theta ≤ zeta/2) :
    ∀ᶠ N : ℕ in atTop, ∀ (J : ℕ) (T p : ℝ), (J : ℝ) ≤ L0 → 0 ≤ T →
      0 < p → p ≤ 1 → T ≤ (N : ℝ)^(1/4-nu-zeta) → (N : ℝ)^(-Cp) ≤ p →
      let x := sourceGammaScale N J T B (3*p/8)
      ∀ K D : ℝ, 0 < K → 1 ≤ D → K ≤ CK*(1+Real.log x)^sK → D ≤ CD*(1+Real.log x)^sD →
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
  obtain ⟨Ca,hCa,hjumpRate⟩ := exists_source_jump_gaussian_coefficient_subpolynomial
    d c C g pDecay q alpha C3 CK sK CD sD theta φ G hc hC hpDecay hq halpha htheta
  obtain ⟨Cd,hCd,hdriftRate⟩ := exists_source_drift_coefficient_subpolynomial
    c C g pDecay q alpha C3 A_sp CK sK CD sD theta φ G hc hC hpDecay hq halpha hA_sp htheta
  have hsmall := eventually_source_actual_bootstrap_smallness L0 B Cp theta nu zeta Ca Cg Ct Cd C0
    hL0 hB htheta.le hnu hzeta hCa.le hCg hCt hCd.le hC0 hexp
  filter_upwards [hsmall, eventually_ge_atTop 1] with N hNs hN1
  intro J T p hJ hT hp hp1 hTN hpN
  dsimp only
  intro K D hK hD hKb hDb L hL delta deltaTilde kappa tau eta hg hgt heta hcont hjump
  let x := sourceGammaScale N J T B (3*p/8)
  let Lambda := featureDisplacementLambda c C g pDecay q D L
  let A := sourceJumpCoefficient d Lambda L*sourceGaussianDeviation (p/(8*((J : ℝ)+1)))
  let cD := Lambda+(2+A_sp)*(L : ℝ)
  have hN : 0 < N := by omega
  have hx : 2 ≤ x := (sourceGammaScale_bounds N J T B (3*p/8)
    hN hT hB (by positivity) (by linarith)).1
  have hratio : ((J : ℝ)+1)/p ≤ x := by
    have hh := sourceGammaScale_jump_budget_ratio N J T B (3*p/8) hN hT hB (by positivity)
    exact (div_le_div_of_nonneg_left (by positivity) (by positivity : 0 < 3*p/8) (by linarith)).trans hh
  have hAb : A ≤ Ca*x^theta := hjumpRate x hx K D hK hD hKb hDb J p hp hratio L hL
  have hcd : cD ≤ Cd*x^theta := hdriftRate x hx K D hK hD hKb hDb L hL
  have hLambda : 0 ≤ Lambda := featureDisplacementLambda_nonneg c C g pDecay q D L hC (by linarith)
  have hA : 0 ≤ A := by
    apply mul_nonneg
    · exact (by norm_num : (0 : ℝ) ≤ 1).trans
        (sourceJumpCoefficient_domination d Lambda L hLambda L.coe_nonneg).1
    · exact (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_sourceGaussianDeviation _)
  have hcD : 0 ≤ cD := by dsimp [cD]; positivity
  exact hNs J T p hJ hT hp hp1 hTN hpN A delta deltaTilde cD kappa tau eta
    hA hcD hAb hcd hg hgt heta hcont hjump

end PaperFormalization.Manuscript
