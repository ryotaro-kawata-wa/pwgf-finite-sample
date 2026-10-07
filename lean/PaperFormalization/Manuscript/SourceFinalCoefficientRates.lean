import PaperFormalization.Manuscript.SourceFixedRadiusGammaRate
import PaperFormalization.Manuscript.SourceRateScaleComparison
import PaperFormalization.Manuscript.SourcePopulationScaleRates
import PaperFormalization.Manuscript.SourceNuclearEnvelopeRate
import PaperFormalization.Manuscript.SourceJumpRateCoefficients

/-! # Uniform rates for the literal FINAL source thresholds

M13t verified implementation. The population scale, Gamma threshold,
covariance threshold, Lambda and jump coefficient are the actual source
expressions. All constants are chosen before N,J,T,p and L. B, dimension,
features/objective and the one fixed CD are structural parameters. The fixed
clipping condition contains no epsilon, so no Good event is retuned to epsilon.
-/
open Set
open scoped NNReal
namespace PaperFormalization.Manuscript
variable {d : Nat}
variable {H : Nat -> Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace Real (H n)] [∀ n, CompleteSpace (H n)]

/-- A deterministic admission condition for the one chosen localization
coefficient. It is proved satisfiable before all rate exponents and schedules. -/
def SourceRateRadiusAdmissible (alpha K0 CD : Real) : Prop :=
  1 ≤ CD ∧ sourceRadiusCoefficientMinimum alpha K0 ≤ CD ∧
  (1 : Real)/2+3 ≤ ((sourcePopulationFlowFactor alpha)⁻¹)/2 *
    (CD/sourcePopulationExponentialScale alpha K0)^alpha

theorem exists_source_rate_radius (alpha K0 : Real) (ha : 0 < alpha) :
    ∃ CD : Real, SourceRateRadiusAdmissible alpha K0 CD := by
  have hb : 0 < sourcePopulationExponentialScale alpha K0 :=
    lt_of_lt_of_le (by norm_num : (0 : Real) < 1) (le_max_left _ _)
  have hc0 : 0 < (sourcePopulationFlowFactor alpha)⁻¹ := by
    unfold sourcePopulationFlowFactor; positivity
  obtain ⟨CD,hmin,hCD,hdecay⟩ := exists_source_radius_before_all_exponents
    ((sourcePopulationFlowFactor alpha)⁻¹) (sourcePopulationExponentialScale alpha K0) alpha 1
    (sourceRadiusCoefficientMinimum alpha K0) hc0 hb ha (by norm_num)
  exact ⟨CD,hCD,hmin,hdecay⟩

set_option maxHeartbeats 4000000 in
/-- All final coefficients use the same appendix Xi and same radius.
The four constants and cutoff are uniform in N,J,T,p; no residual estimate
or matrix concentration conclusion is supplied as a new premise. -/
theorem exists_source_final_coefficient_rates
    (c C g pDecay q alpha K0 C3 CD : Real)
    (phi : ∀ n, EuclideanSpace Real (Fin d) -> H n) (G : lp H 2 -> Real)
    (B : NNReal) (hc : 0 < c) (hC : 0 ≤ C) (hpDecay : 1 < pDecay) (hq : q < pDecay)
    (ha : 0 < alpha) (hCD : SourceRateRadiusAdmissible alpha K0 CD)
    (epsilon : Real) (he : 0 < epsilon) :
    ∃ Cg Ct Ca Cl : Real, 0 < Cg ∧ 0 < Ct ∧ 0 < Ca ∧ 0 < Cl ∧
      ∃ N0 : Nat, 0 < N0 ∧ ∀ N J : Nat, N0 ≤ N ->
      ∀ T p : Real, 0 ≤ T -> 0 < p -> p < 1 ->
      let x := sourceAsymptoticXi N J T p B
      let K := sourceFinalMomentScale J T alpha K0 p B
      let D := sourceRateRadius N J T p alpha CD B
      ∀ L : NNReal, (L : Real) = sourceComparisonEnvelope c C g pDecay q K D alpha C3 phi G ->
      sourceFinalGammaThreshold J N T alpha K0 D p c C g pDecay q B L ≤
        Cg*x^epsilon*((Real.sqrt N)⁻¹+T/N) ∧
      sourcePrescribedCovarianceEnvelope J N d c C g pDecay q alpha K L p ≤
        Ct*x^epsilon*(Real.sqrt N)⁻¹ ∧
      (0 ≤ sourceFinalJumpCoefficient J d c C g pDecay q D p L ∧
        sourceFinalJumpCoefficient J d c C g pDecay q D p L ≤ Ca*x^epsilon) ∧
      (0 ≤ featureDisplacementLambda c C g pDecay q D L ∧
        featureDisplacementLambda c C g pDecay q D L ≤ Cl*x^epsilon) := by
  obtain ⟨CK,CM,hCK,hCM,hpop⟩ := exists_source_population_tracking_scale_growth alpha K0 ha
  let b := sourcePopulationExponentialScale alpha K0
  let c0 := (sourcePopulationFlowFactor alpha)⁻¹
  have hb : 0 < b := lt_of_lt_of_le (by norm_num : (0 : Real) < 1) (le_max_left _ _)
  have hc0 : 0 < c0 := by dsimp [c0]; unfold sourcePopulationFlowFactor; positivity
  obtain ⟨MG,hMG,N0,hN0,hgamma⟩ := source_gamma_rate_at_fixed_radius
    c C g pDecay q alpha C3 CK (1/alpha) CM 1 c0 b epsilon CD phi G
    hc hC hpDecay hq ha hCM.le (by norm_num) hc0 hb he hCD.1 hCD.2.2
  let Klog := CK*(1+1/Real.log 2)^(1/alpha)
  let Dlog := CD*(1+1/Real.log 2)^(1/alpha)
  obtain ⟨MT,hMT,hnuclear⟩ := exists_uniform_source_nuclear_covariance_threshold_rate
    d c C g pDecay q alpha C3 Klog (1/alpha) Dlog (1/alpha) epsilon phi G
    hc hC hpDecay hq ha he
  obtain ⟨MA,hMA,hjump⟩ := exists_source_jump_gaussian_coefficient_subpolynomial
    d c C g pDecay q alpha C3 CK (1/alpha) CD (1/alpha) epsilon phi G hc hC hpDecay hq ha he
  obtain ⟨ML,hML,hlambda⟩ := exists_uniform_source_gamma_coefficients_subpolynomial
    c C g pDecay q alpha C3 CK (1/alpha) CD (1/alpha) epsilon phi G hc hC hpDecay hq ha he
  refine ⟨MG*(1+(B : Real)),MT,MA,ML,by positivity,hMT,hMA,hML,N0,hN0,?_⟩
  intro N J hN0N T p hT hp hp1
  dsimp only
  intro L hL
  let x := sourceAsymptoticXi N J T p B
  let K := sourceFinalMomentScale J T alpha K0 p B
  let D := sourceRateRadius N J T p alpha CD B
  have hN : 0 < N := hN0.trans_le hN0N
  have hx : 2 ≤ x := (sourceAsymptoticXi_bounds N J T p B hN hT hp hp1.le).1
  have hK : 0 < K := (sourceFinalScales_positive J T alpha K0 p B ha hp hp1).2
  have hD : 1 ≤ D := sourceRateRadius_one_le N J T p alpha CD B hN hT hp hp1.le ha hCD.1
  have hKg : K ≤ CK*(1+Real.log x)^(1/alpha) := (hpop N J T B p hN hT hp hp1.le).1
  have hMg : (4*(populationGridBudget B J T : Real)/(p/8))*Real.exp (b^(-alpha)) ≤ CM*x :=
    (hpop N J T B p hN hT hp hp1.le).2
  have hLabs : (L : Real) ≤ |sourceComparisonEnvelope c C g pDecay q K D alpha C3 phi G| := by
    rw [hL]; exact le_abs_self _
  have hG0 := hgamma N J hN0N T B (3*p/8) hT B.coe_nonneg (by positivity) (by linarith)
    K ((4*(populationGridBudget B J T : Real)/(p/8))*Real.exp (b^(-alpha))) hK hKg
    (by simpa only [Real.rpow_one,x,sourceAsymptoticXi] using hMg) L hLabs
  have hGamma : sourceFinalGammaThreshold J N T alpha K0 D p c C g pDecay q B L ≤
      MG*x^epsilon*((Real.sqrt N)⁻¹+(B : Real)*T/N) := by
    simpa only [sourceFinalGammaThreshold,sourceOriginalGammaThreshold,featureDisplacementLambda,
      K,D,x,sourceRateRadius,sourceAsymptoticXi,b,c0,
      show (3*p/8)/3=p/8 by ring] using hG0
  have hrate : (Real.sqrt N)⁻¹+(B : Real)*T/N ≤
      (1+(B : Real))*((Real.sqrt N)⁻¹+T/N) := by
    have heq : (1+(B : Real))*((Real.sqrt N)⁻¹+T/N) =
        ((Real.sqrt N)⁻¹+(B : Real)*T/N) + ((B : Real)*(Real.sqrt N)⁻¹+T/N) := by ring
    rw [heq]
    exact le_add_of_nonneg_right (by positivity)
  have hGamma' := hGamma.trans (mul_le_mul_of_nonneg_left hrate (show 0 ≤ MG*x^epsilon by positivity))
  have hlogK : K ≤ Klog*(Real.log x)^(1/alpha) := by
    have h := mul_le_mul_of_nonneg_left (source_one_add_log_rpow_le x (1/alpha) hx (by positivity)) hCK.le
    exact hKg.trans (by dsimp [Klog]; nlinarith)
  have hlogD : D ≤ Dlog*(Real.log x)^(1/alpha) := by
    have h := mul_le_mul_of_nonneg_left (source_one_add_log_rpow_le x (1/alpha) hx (by positivity))
      (show 0 ≤ CD by linarith [hCD.1])
    change CD*(1+Real.log x)^(1/alpha) ≤ (CD*(1+1/Real.log 2)^(1/alpha))*(Real.log x)^(1/alpha)
    exact h.trans_eq (by ring)
  let u := p/(8*((J : Real)+1))
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 8*((J : Real)+1))).mpr
    nlinarith [Nat.cast_nonneg (α := Real) J]
  have hT0 := hnuclear N hN u x hu hu1 hx
    (sourceAsymptoticXi_covariance_scale N J T p B hT hp) K D hK hD hlogK hlogD L hL
  have hratio : ((J : Real)+1)/p ≤ x := by
    have hd : ((J : Real)+1)/p ≤ ((J : Real)+1)/(3*p/8) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    exact hd.trans (sourceGammaScale_jump_budget_ratio N J T B (3*p/8) hN hT B.coe_nonneg (by positivity))
  have hA := hjump x hx K D hK hD hKg le_rfl J p hp hratio L hL
  have hLambda := (hlambda x hx K D hK hD hKg le_rfl L hLabs).2.1
  have hLambda0 := featureDisplacementLambda_nonneg c C g pDecay q D L hC (by linarith)
  have hcj0 : 0 ≤ sourceJumpCoefficient d (featureDisplacementLambda c C g pDecay q D L) L :=
    (by norm_num : (0 : Real) ≤ 1).trans
      (sourceJumpCoefficient_domination d _ L hLambda0 L.coe_nonneg).1
  have hA0 : 0 ≤ sourceFinalJumpCoefficient J d c C g pDecay q D p L :=
    mul_nonneg hcj0 ((by norm_num : (0 : Real) ≤ 1).trans (one_le_sourceGaussianDeviation _))
  refine ⟨?_,?_,⟨hA0,hA⟩,⟨hLambda0,hLambda⟩⟩
  · exact hGamma'.trans_eq (by ring)
  · simpa only [sourcePrescribedCovarianceEnvelope,div_eq_mul_inv,K,u,x] using hT0

end PaperFormalization.Manuscript
