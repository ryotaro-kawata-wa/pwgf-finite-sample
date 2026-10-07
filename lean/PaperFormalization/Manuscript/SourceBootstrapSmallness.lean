import PaperFormalization.Manuscript.SourceCurvatureResponseRates
import PaperFormalization.Manuscript.SourceTrackingScale
import PaperFormalization.Manuscript.GrowingHorizonAlgebra

/-! # Uniform eventual smallness of the actual source bootstrap radius

The curvature-response bound and finite jump product are derived internally.
The continuous/covariance residual and coefficient rates are supplied by their
separate source estimates. This unit makes the exact growing-horizon exponent
substitution and the uniform-in-horizon eventual threshold explicit.
-/
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace PaperFormalization.Manuscript
open Continuous

/-- Exact scalar Step3 substitution, keeping the source stability bracket.
Only rate bounds are used; no smallness or limiting conclusion is assumed. -/
theorem source_stability_bracket_rate
    (N : ℕ) (L0 x theta nu T delta cD R Cg Cd Cr : ℝ)
    (hN : 0 < N) (hL0 : 0 ≤ L0) (hx : 1 ≤ x) (htheta : 0 ≤ theta)
    (hnu : 0 ≤ nu) (hT : 0 ≤ T) (hcD : 0 ≤ cD)
    (hCg : 0 ≤ Cg) (hCr : 0 ≤ Cr)
    (hdelta : delta ≤ Cg*x^theta*((Real.sqrt N)⁻¹+T/N))
    (hcd : cD ≤ Cd*x^theta)
    (hR : R ≤ Cr*x^((L0+3/2)*theta)*(N : ℝ)^nu*
      ((1+T)/Real.sqrt N+(N : ℝ)^(-1/4 : ℝ))) :
    T*(delta+cD*R) ≤ (Cg+Cd*Cr)*x^((L0+5/2)*theta)*(N : ℝ)^nu*
      (T*(1+T)/Real.sqrt N+T*(N : ℝ)^(-1/4 : ℝ)) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hn0
  have hsle : Real.sqrt (N : ℝ) ≤ N := by
    nlinarith [Real.sq_sqrt hn0.le, Real.sqrt_nonneg (N : ℝ)]
  have htr : T/(N : ℝ) ≤ T/Real.sqrt N := div_le_div_of_nonneg_left hT hs hsle
  have hrate : (Real.sqrt N)⁻¹+T/N ≤ (1+T)/Real.sqrt N := by
    calc
      _ ≤ (Real.sqrt N)⁻¹+T/Real.sqrt N := add_le_add le_rfl htr
      _ = _ := by ring
  have hxp : x^theta ≤ x^((L0+5/2)*theta) :=
    Real.rpow_le_rpow_of_exponent_le hx (by nlinarith)
  have hnp : 1 ≤ (N : ℝ)^nu := Real.one_le_rpow hn hnu
  have hd : delta ≤ Cg*x^((L0+5/2)*theta)*(N : ℝ)^nu*((1+T)/Real.sqrt N) := by
    have hfirst := hdelta.trans (mul_le_mul (mul_le_mul_of_nonneg_left hxp hCg) hrate
      (by positivity) (by positivity))
    have hsecond := mul_le_mul_of_nonneg_left hnp
      (show 0 ≤ Cg*x^((L0+5/2)*theta)*((1+T)/Real.sqrt N) by positivity)
    nlinarith
  have hcr : cD*R ≤ Cd*Cr*x^((L0+5/2)*theta)*(N : ℝ)^nu*
      ((1+T)/Real.sqrt N+(N : ℝ)^(-1/4 : ℝ)) := by
    calc
      _ ≤ cD*(Cr*x^((L0+3/2)*theta)*(N : ℝ)^nu*
          ((1+T)/Real.sqrt N+(N : ℝ)^(-1/4 : ℝ))) := mul_le_mul_of_nonneg_left hR hcD
      _ ≤ (Cd*x^theta)*(Cr*x^((L0+3/2)*theta)*(N : ℝ)^nu*
          ((1+T)/Real.sqrt N+(N : ℝ)^(-1/4 : ℝ))) :=
        mul_le_mul_of_nonneg_right hcd (by positivity)
      _ = Cd*Cr*(x^theta*x^((L0+3/2)*theta))*(N : ℝ)^nu*
          ((1+T)/Real.sqrt N+(N : ℝ)^(-1/4 : ℝ)) := by ring
      _ = _ := by
        rw [← Real.rpow_add (by linarith : 0 < x),
          show theta+(L0+3/2)*theta=(L0+5/2)*theta by ring]
  have hdT := mul_le_mul_of_nonneg_left hd hT
  have hcrT := mul_le_mul_of_nonneg_left hcr hT
  have hextra : 0 ≤ Cg*x^((L0+5/2)*theta)*(N : ℝ)^nu*T*(N : ℝ)^(-1/4 : ℝ) := by positivity
  simp only [div_eq_mul_inv] at hdT hcrT hextra ⊢
  nlinarith only [hdT, hcrT, hextra]

set_option maxHeartbeats 600000 in
/-- The actual source radius satisfies the Step3 stability bound. The
source response and jump-amplification bounds are not assumptions. -/
theorem source_actual_stability_bracket_rate
    (N J : ℕ) (L0 x theta nu T A Cg Ct Ca Cd C0 delta deltaTilde cD : ℝ)
    (kappa : ℝ → ℝ) (tau eta : ℕ → ℝ)
    (hN : 0 < N) (hJ : (J : ℝ) ≤ L0) (hx : 1 ≤ x) (htheta : 0 ≤ theta)
    (hnu : 0 ≤ nu) (hT : 0 ≤ T) (hTN : T ≤ Real.sqrt N) (hA : 0 ≤ A) (hcD : 0 ≤ cD)
    (hCg : 0 ≤ Cg) (hCt : 0 ≤ Ct) (hCa : 0 ≤ Ca) (hC0 : 0 ≤ C0)
    (hAb : A ≤ Ca*x^theta) (hcd : cD ≤ Cd*x^theta)
    (hg : delta ≤ Cg*x^theta*((Real.sqrt N)⁻¹+T/N))
    (hgt : deltaTilde ≤ Ct*x^theta*(Real.sqrt N)⁻¹)
    (heta : ∀ i < J, 0 ≤ eta i ∧ eta i ≤ C0)
    (hcont : ∀ t ∈ Icc 0 T, (∫ s in (0 : ℝ)..t, propagator kappa t s) ≤
      C0*(N : ℝ)^nu*(1+T))
    (hjump : ∀ t ∈ Icc 0 T,
      (∑ i ∈ (Finset.range J).filter (fun i => tau (i+1) ≤ t),
        eta i*propagator kappa t (tau (i+1))) ≤ C0*(N : ℝ)^nu) :
    let Cr := 4*C0*(1+Ca*C0)^L0*(Cg+Ca*(Real.sqrt Cg+Real.sqrt Ct))
    T*(delta+cD*(2*jumpAmplification (sourceJumpError A eta) J*
      sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A J T)) ≤
      (Cg+Cd*Cr)*x^((L0+5/2)*theta)*(N : ℝ)^nu*
        (T*(1+T)/Real.sqrt N+T*(N : ℝ)^(-1/4 : ℝ)) := by
  have hR := source_bootstrap_radius_rate N J L0 x theta nu T A Cg Ct Ca C0 delta deltaTilde
    kappa tau eta hN hJ hx htheta hT hTN hA hCg hCt hCa hC0 hAb hg hgt heta hcont hjump
  have hL0 : 0 ≤ L0 := (Nat.cast_nonneg J).trans hJ
  exact source_stability_bracket_rate N L0 x theta nu T delta cD _ Cg Cd _
    hN hL0 hx htheta hnu hT hcD hCg (by positivity) hg hcd hR

set_option maxHeartbeats 1000000 in
/-- One threshold in N works for every original admissible T,p,J and every
path satisfying the source response condition. The radius in the conclusion
is literally 2 times the finite jump product times the actual source supremum.
Residual and coefficient rates are the separate upstream inputs to this final
deterministic assembly, not a smallness or radius premise. -/
theorem eventually_source_actual_bootstrap_smallness
    (L0 B Cp theta nu zeta Ca Cg Ct Cd C0 : ℝ)
    (hL0 : 0 ≤ L0) (hB : 0 ≤ B) (htheta : 0 ≤ theta)
    (hnu : 0 ≤ nu) (hzeta : 0 < zeta)
    (hCa : 0 ≤ Ca) (hCg : 0 ≤ Cg) (hCt : 0 ≤ Ct) (hCd : 0 ≤ Cd) (hC0 : 0 ≤ C0)
    (hexp : (5/4+Cp)*(L0+5/2)*theta ≤ zeta/2) :
    ∀ᶠ N : ℕ in atTop, ∀ (J : ℕ) (T p : ℝ), (J : ℝ) ≤ L0 → 0 ≤ T →
      0 < p → p ≤ 1 → T ≤ (N : ℝ)^(1/4-nu-zeta) → (N : ℝ)^(-Cp) ≤ p →
      let x := sourceGammaScale N J T B (3*p/8)
      ∀ (A delta deltaTilde cD : ℝ) (kappa : ℝ → ℝ) (tau eta : ℕ → ℝ),
      0 ≤ A → 0 ≤ cD → A ≤ Ca*x^theta → cD ≤ Cd*x^theta →
      delta ≤ Cg*x^theta*((Real.sqrt N)⁻¹+T/N) →
      deltaTilde ≤ Ct*x^theta*(Real.sqrt N)⁻¹ →
      (∀ i < J, 0 ≤ eta i ∧ eta i ≤ C0) →
      (∀ t ∈ Icc 0 T, (∫ s in (0 : ℝ)..t, propagator kappa t s) ≤ C0*(N : ℝ)^nu*(1+T)) →
      (∀ t ∈ Icc 0 T,
        (∑ i ∈ (Finset.range J).filter (fun i => tau (i+1) ≤ t),
          eta i*propagator kappa t (tau (i+1))) ≤ C0*(N : ℝ)^nu) →
      T*(delta+cD*(2*jumpAmplification (sourceJumpError A eta) J*
        sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A J T)) ≤ 1/4 := by
  let a := (L0+5/2)*theta
  let Cr := 4*C0*(1+Ca*C0)^L0*(Cg+Ca*(Real.sqrt Cg+Real.sqrt Ct))
  let Cscale := 8*(Real.exp 1+1)*(L0+1)*(1+B)
  let K := (Cg+Cd*Cr)*Cscale^a
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hCr : 0 ≤ Cr := by dsimp [Cr]; positivity
  have hK : 0 ≤ K := by dsimp [K,Cscale]; positivity
  have hstable := eventually_source_horizon_stability K nu zeta hK hnu hzeta
  filter_upwards [hstable, eventually_ge_atTop 1] with N hNS hN1
  intro J T p hJ hT hp hp1 hTN hpN
  dsimp only
  intro A delta deltaTilde cD kappa tau eta hA hcD hAb hcd hg hgt heta hcont hjump
  let x := sourceGammaScale N J T B (3*p/8)
  have hN : 0 < N := by omega
  have hx2 : 2 ≤ x := (sourceGammaScale_bounds N J T B (3*p/8)
    hN hT hB (by positivity) (by linarith)).1
  have hTN' := source_growing_horizon_le_sqrt N T nu zeta hN hnu hzeta.le hTN
  have hb := source_actual_stability_bracket_rate N J L0 x theta nu T A Cg Ct Ca Cd C0
    delta deltaTilde cD kappa tau eta hN hJ (by linarith) htheta hnu hT hTN' hA hcD
    hCg hCt hCa hC0 hAb hcd hg hgt heta hcont hjump
  have hxp : x^a ≤ Cscale^a*(N : ℝ)^(zeta/2) :=
    sourceTrackingScale_power_le N J T B p nu zeta Cp L0 a hN hT hB hp hnu hzeta.le hJ hTN hpN
      ha (by dsimp [a]; nlinarith [hexp])
  have hm := mul_le_mul_of_nonneg_left hxp (show 0 ≤ (Cg+Cd*Cr)*(N : ℝ)^nu*
    (T*(1+T)/Real.sqrt N+T*(N : ℝ)^(-1/4 : ℝ)) by positivity)
  have hconvert : (Cg+Cd*Cr)*x^a*(N : ℝ)^nu*
      (T*(1+T)/Real.sqrt N+T*(N : ℝ)^(-1/4 : ℝ)) ≤
      K*(N : ℝ)^(zeta/2)*(N : ℝ)^nu*
        (T*(1+T)/(N : ℝ)^(1/2 : ℝ)+T/(N : ℝ)^(1/4 : ℝ)) := by
    have hquarter : (N : ℝ)^(-1/4 : ℝ) = ((N : ℝ)^(1/4 : ℝ))⁻¹ := by
      rw [show (-1/4 : ℝ) = -(1/4 : ℝ) by ring, Real.rpow_neg (Nat.cast_nonneg N)]
    rw [Real.sqrt_eq_rpow, hquarter] at hm ⊢
    dsimp [K]
    convert hm using 1 <;> first | rfl | ring
  change _ ≤ (Cg+Cd*Cr)*x^a*(N : ℝ)^nu*_
    at hb
  exact hb.trans (hconvert.trans (hNS T hT hTN))

end PaperFormalization.Manuscript
