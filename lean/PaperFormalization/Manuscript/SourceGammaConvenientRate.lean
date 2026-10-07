import PaperFormalization.Manuscript.SourceGammaRateAlgebra
import PaperFormalization.Manuscript.SourceClippingBiasRate

/-! # The convenient source Gamma threshold with quantified constants

The exact coefficient series, source Xi and D=C_D(1+log Xi)^(1/alpha)
are substituted internally. The result concerns the deterministic threshold;
population/radius event probabilities are supplied by separate theorems.
-/
namespace PaperFormalization.Manuscript
open scoped NNReal
variable {E : Type*} [Zero E] {H : ℕ → Type*}
  [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℝ (H n)]

set_option maxHeartbeats 1600000 in
/-- One radius coefficient, rate coefficient and sample threshold work
uniformly over N,J,T,B,p and every admitted population K and Mpop. -/
theorem exists_source_gamma_convenient_threshold_rate
    (c C g pDecay q alpha C3 CK sK CM cM c0 K0 epsilon CDmin : ℝ)
    (φ : ∀ n, E → H n) (G : lp H 2 → ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hpDecay : 1 < pDecay) (hq : q < pDecay)
    (halpha : 0 < alpha) (hCM : 0 ≤ CM) (hcM : 0 ≤ cM)
    (hc0 : 0 < c0) (hK0 : 0 < K0) (he : 0 < epsilon) :
    ∃ CD : ℝ, CDmin ≤ CD ∧ 1 ≤ CD ∧ ∃ M : ℝ, 0 < M ∧ ∃ N0 : ℕ, 0 < N0 ∧
      ∀ N J : ℕ, N0 ≤ N → ∀ T B p : ℝ, 0 ≤ T → 0 ≤ B → 0 < p → p ≤ 1 →
      let x := sourceGammaScale N J T B p
      let D := CD*(1+Real.log x)^(1/alpha)
      ∀ K Mpop : ℝ, 0 < K → K ≤ CK*(1+Real.log x)^sK → Mpop ≤ CM*x^cM →
      ∀ L : ℝ≥0, (L : ℝ) ≤ |sourceComparisonEnvelope c C g pDecay q K D alpha C3 φ G| →
      let A := 2 * ∑' n, (featureResidualWeight c pDecay L n : ℝ) *
        (featureGrowth C g q n * (1+D^(n+1)))
      let Lambda := featureDisplacementLambda c C g pDecay q D L
      let S := ∑' n, (featureResidualWeight c pDecay L n : ℝ) *
        sourceCoordinateL2Envelope C g q alpha K n
      let beta := 2*S*Real.sqrt Mpop*Real.exp (-(c0*(D/K0)^alpha)/2)
      let Q := (((J+1 : ℕ) : ℝ)*((N+1 : ℕ) : ℝ))
      beta + A/Real.sqrt N + A*Real.sqrt (Real.log (Q/(p/3))/(2*N)) + 2*B*T*Lambda/N ≤
        M*x^epsilon*((Real.sqrt N)⁻¹+B*T/N) := by
  obtain ⟨CD,hCDmin,hCD,hdecay⟩ := exists_source_clipping_radius_coefficient_above c0 K0 alpha cM CDmin hc0 hK0 halpha hcM
  obtain ⟨Ca,hCa,hcoeff⟩ := exists_uniform_source_gamma_coefficients_subpolynomial
    c C g pDecay q alpha C3 CK sK CD (1/alpha) (epsilon/2) φ G hc hC hpDecay hq halpha (by positivity)
  obtain ⟨Cs,hCs,hbiascoeff⟩ := exists_uniform_source_gamma_coefficients_subpolynomial
    c C g pDecay q alpha C3 CK sK CD (1/alpha) 1 φ G hc hC hpDecay hq halpha (by norm_num)
  obtain ⟨Cl,hCl,hlog⟩ := exists_sqrt_log_multiple_le_rpow 2 (epsilon/2) (by norm_num) (by positivity)
  obtain ⟨N0,hN0⟩ := exists_nat_gt (2*Cs*Real.sqrt CM)
  have hN0pos : 0 < N0 := by
    have hN0r : (0 : ℝ) < N0 := lt_of_le_of_lt (by positivity) hN0
    exact_mod_cast hN0r
  refine ⟨CD,hCDmin,hCD,1+Ca+Ca*Cl+2*Ca,by positivity,N0,hN0pos,?_⟩
  intro N J hN0N T B p hT hB hp hp1
  let x := sourceGammaScale N J T B p
  let D := CD*(1+Real.log x)^(1/alpha)
  dsimp only
  intro K Mpop hK hKb hMb L hL
  have hN : 0 < N := hN0pos.trans_le hN0N
  obtain ⟨hx,hNx,hgrid⟩ := sourceGammaScale_bounds N J T B p hN hT hB hp hp1
  change 2 ≤ x at hx
  change (N : ℝ) ≤ x at hNx
  have hD : 1 ≤ D := by
    have hb : 1 ≤ 1+Real.log x := by linarith [Real.log_nonneg (by linarith : 1 ≤ x)]
    have hpow := Real.one_le_rpow hb (show 0 ≤ 1/alpha by positivity)
    dsimp [D]
    nlinarith
  have hcoef := hcoeff x hx K D hK hD hKb le_rfl L hL
  have hS := (hbiascoeff x hx K D hK hD hKb le_rfl L hL).2.2
  simp only [Real.rpow_one] at hS
  let A := 2 * ∑' n, (featureResidualWeight c pDecay L n : ℝ) *
    (featureGrowth C g q n * (1+D^(n+1)))
  let Lambda := featureDisplacementLambda c C g pDecay q D L
  let S := ∑' n, (featureResidualWeight c pDecay L n : ℝ) * sourceCoordinateL2Envelope C g q alpha K n
  let beta := 2*S*Real.sqrt Mpop*Real.exp (-(c0*(D/K0)^alpha)/2)
  let Q := (((J+1 : ℕ) : ℝ)*((N+1 : ℕ) : ℝ))
  have hbeta : beta ≤ (N : ℝ)⁻¹ := by
    have hb := source_clipping_bias_le_inverse_square S Mpop Cs CM cM c0 CD K0 alpha x
      hCs.le hCM hcM (by linarith) hK0 halpha (by linarith) hS hMb hdecay
    have hCN : 2*Cs*Real.sqrt CM ≤ N := hN0.le.trans (by exact_mod_cast hN0N)
    exact hb.trans (source_inverse_square_le_inverse_sample N x (2*Cs*Real.sqrt CM) hN hCN hNx)
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    norm_cast
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.succ_ne_zero _) (Nat.succ_ne_zero _))
  have hratio : 1 ≤ Q/(p/3) := (le_div_iff₀ (by positivity : 0 < p/3)).mpr (by linarith)
  have hlogb := hlog x hx (Q/(p/3)) (by positivity) hgrid
  exact source_gamma_threshold_rate N x epsilon A Lambda beta Ca Cl B T Q (p/3)
    hN (by linarith) he.le hCa.le hCl.le hB hT hcoef.1 hcoef.2.1 hbeta hratio hlogb
end PaperFormalization.Manuscript
