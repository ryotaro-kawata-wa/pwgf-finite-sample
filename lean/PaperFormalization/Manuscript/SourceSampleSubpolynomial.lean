import PaperFormalization.Manuscript.PolylogFeatureEnvelope
import PaperFormalization.Manuscript.SourceSampleMaxTail

/-! # The source sampled threshold is uniformly subpolynomial

The literal sampled radius, max-one energy threshold and sharp fourth-moment
coefficient are retained. A single constant is chosen before N, delta, Xi and
K. The source exponent s_K may be any real number; no additional positivity
assumption on it is imposed. The result holds for every Xi>=2.
-/

open scoped BigOperators

namespace PaperFormalization.Manuscript

/-- The two actual logarithms are controlled by the same shifted log, using
only Xi>=N/delta and the source positive-particle, probability-budget domain. -/
theorem source_sample_logs_le_shifted_log (N : ℕ) (delta x : ℝ)
    (hN : 0 < N) (hdelta : 0 < delta) (hx : 2 ≤ x) (hscale : (N : ℝ) / delta ≤ x) :
    1 + Real.log (8 * (N : ℝ) / delta) ≤
      (2 + Real.log 8) * Real.log (Real.exp 1 + x) ∧
    1 + Real.log (8 / delta) ≤
      (2 + Real.log 8) * Real.log (Real.exp 1 + x) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog8 : 0 ≤ Real.log (8 : ℝ) := Real.log_nonneg (by norm_num)
  have hL : 1 ≤ Real.log (Real.exp 1 + x) := one_le_featureScaleLog x (by linarith)
  have hlogx : Real.log x ≤ Real.log (Real.exp 1 + x) :=
    Real.log_le_log (by linarith) (by linarith [Real.exp_pos (1 : ℝ)])
  have hratio : 8 * (N : ℝ) / delta ≤ 8 * x := by
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hscale (by norm_num : (0 : ℝ) ≤ 8)
  have hlogN : Real.log (8 * (N : ℝ) / delta) ≤ Real.log 8 + Real.log x := by
    calc
      _ ≤ Real.log (8 * x) := Real.log_le_log (by positivity) hratio
      _ = _ := Real.log_mul (by norm_num) (by linarith)
  have hmain : 1 + Real.log (8 * (N : ℝ) / delta) ≤
      (2 + Real.log 8) * Real.log (Real.exp 1 + x) := by nlinarith
  refine ⟨hmain, ?_⟩
  have hlogdelta : Real.log (8 / delta) ≤ Real.log (8 * (N : ℝ) / delta) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by nlinarith) hdelta.le)
  linarith

/-- The literal radius R_(N,delta) has the explicit shifted-polylog bound
with exponent s+1/alpha, before any asymptotic absorption. -/
theorem sourceSampleRadius_le_shifted_polylog
    (N : ℕ) (alpha K delta x C s : ℝ) (hN : 0 < N)
    (halpha : 0 < alpha) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hx : 2 ≤ x) (hscale : (N : ℝ) / delta ≤ x) (hC : 0 ≤ C)
    (hKbound : K ≤ C * (Real.log (Real.exp 1 + x)) ^ s) :
    sourceSampleRadius N alpha K delta ≤
      (C * (Real.exp 1 * max alpha 1 * (2 + Real.log 8)) ^ (1 / alpha)) *
        (Real.log (Real.exp 1 + x)) ^ (s + 1 / alpha) := by
  let l := Real.log (Real.exp 1 + x)
  have hl : 1 ≤ l := one_le_featureScaleLog x (by linarith)
  have hl0 : 0 < l := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : 0 ≤ Real.log (8 * (N : ℝ) / delta) :=
    Real.log_nonneg ((le_div_iff₀ hdelta).mpr (by nlinarith))
  have hmax : 0 ≤ max alpha 1 := le_trans (by norm_num) (le_max_right _ _)
  have hclog : 0 ≤ 2 + Real.log (8 : ℝ) := by
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)]
  have hlog := (source_sample_logs_le_shifted_log N delta x hN hdelta hx hscale).1
  have hpow : (Real.exp 1 * max alpha 1 * (1 + Real.log (8 * (N : ℝ) / delta))) ^ (1 / alpha) ≤
      ((Real.exp 1 * max alpha 1 * (2 + Real.log 8)) * l) ^ (1 / alpha) := by
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    exact (mul_le_mul_of_nonneg_left hlog (mul_nonneg (Real.exp_pos _).le hmax)).trans_eq (by dsimp [l]; ring)
  unfold sourceSampleRadius
  calc
    _ ≤ (C * l ^ s) * ((Real.exp 1 * max alpha 1 * (2 + Real.log 8)) * l) ^ (1 / alpha) :=
      mul_le_mul hKbound hpow (by positivity) (mul_nonneg hC (Real.rpow_nonneg hl0.le _))
    _ = _ := by
      rw [Real.mul_rpow (by positivity) hl0.le, Real.rpow_add hl0]
      ring

/-- The source square-root logarithm has a uniform arbitrary-power bound,
with a constant chosen before N, delta and Xi. -/
theorem exists_source_sample_sqrt_log_le_rpow (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ M : ℝ, 0 < M ∧ ∀ N : ℕ, 0 < N → ∀ delta x : ℝ,
      0 < delta → delta ≤ 1 → 2 ≤ x → (N : ℝ) / delta ≤ x →
      Real.sqrt (Real.log (8 / delta)) ≤ M * x ^ epsilon := by
  have hc : 0 ≤ 2 + Real.log (8 : ℝ) := by
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)]
  obtain ⟨M, hM, hbound⟩ := exists_shifted_loglog_envelope_le_rpow_all
    1 (2 + Real.log 8) 1 epsilon (by norm_num) hc (by norm_num) he
  refine ⟨M, hM, ?_⟩
  intro N hN delta x hdelta hdelta1 hx hscale
  have hlog0 : 0 ≤ Real.log (8 / delta) :=
    Real.log_nonneg ((le_div_iff₀ hdelta).mpr (by linarith))
  have hlog := (source_sample_logs_le_shifted_log N delta x hN hdelta hx hscale).2
  have hsqrt : Real.sqrt (Real.log (8 / delta)) ≤ 1 + Real.log (8 / delta) := by
    nlinarith [Real.sq_sqrt hlog0, Real.sqrt_nonneg (Real.log (8 / delta))]
  have hL : 0 < Real.log (Real.exp 1 + x) :=
    lt_of_lt_of_le zero_lt_one (one_le_featureScaleLog x (by linarith))
  have hlogexp : Real.log (Real.exp 1 + x) ≤
      Real.exp (1 * (1 + Real.log (Real.log (Real.exp 1 + x))) ^ (1 : ℝ)) := by
    rw [Real.rpow_one, one_mul]
    calc
      _ = Real.exp (Real.log (Real.log (Real.exp 1 + x))) := (Real.exp_log hL).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  exact (hsqrt.trans hlog).trans
    ((mul_le_mul_of_nonneg_left hlogexp hc).trans (hbound x hx))

set_option maxHeartbeats 1200000 in
/-- The exact source envelope combination is uniformly subpolynomial for
all Xi>=2. The constant precedes every varying N, delta, Xi and K; arbitrary
real source s_K is retained, as is the original K in C_Phi,4 and the radius. -/
theorem exists_uniform_source_sample_envelope_subpolynomial
    (d : ℕ) (c C g p q alpha CK sK epsilon : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (halpha : 0 < alpha) (he : 0 < epsilon) :
    ∃ M : ℝ, 0 < M ∧ ∀ N : ℕ, 0 < N → ∀ delta x : ℝ,
      0 < delta → delta ≤ 1 → 2 ≤ x → (N : ℝ) / delta ≤ x →
      ∀ K : ℝ, 0 < K → K ≤ CK * (Real.log x) ^ sK →
      sourceSampleHilbertSchmidtEnvelope d c C g p q (sourceSampleRadius N alpha K delta) ^ 2 *
          Real.sqrt (Real.log (8 / delta)) + sourceHilbertSchmidtFourthMoment d c C g p q alpha K ≤
        M * x ^ epsilon := by
  let Ck := (|CK| + 1) * max 1 ((Real.log 2) ^ sK)
  let sk := max sK 0
  let Cr := Ck * (Real.exp 1 * max alpha 1 * (2 + Real.log 8)) ^ (1 / alpha)
  let sr := sk + 1 / alpha
  have hCk : 0 < Ck := mul_pos (by positivity) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  have hsk : 0 ≤ sk := le_max_right _ _
  have hCr : 0 ≤ Cr := by
    have hm : 0 ≤ max alpha 1 := le_trans (by norm_num) (le_max_right _ _)
    have hl : 0 ≤ 2 + Real.log (8 : ℝ) := by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)]
    dsimp [Cr]
    positivity
  have hsr : 0 ≤ sr := by dsimp [sr]; positivity
  obtain ⟨At, hAt, ht⟩ := exists_uniform_sourceSampleHilbertSchmidtEnvelope_dim_bound c C g p q hc hC hp hq
  obtain ⟨Mt, hMt, hMtbound⟩ := exists_exp_chi_polylog_le_rpow At ((1 + (d : ℝ)) * At) p Cr sr (epsilon / 4)
    hAt.le (by positivity) hp hCr hsr (by positivity)
  obtain ⟨A4, hA4, h4⟩ := exists_uniform_sourceHilbertSchmidtFourthMoment_bound d c C g p q alpha
    hc hC hp hq halpha
  obtain ⟨M4, hM4, hM4bound⟩ := exists_exp_chi_polylog_le_rpow A4 A4 p Ck sk epsilon
    hA4.le hA4.le hp hCk.le hsk he
  obtain ⟨Ml, hMl, hMlbound⟩ := exists_source_sample_sqrt_log_le_rpow (epsilon / 2) (by positivity)
  refine ⟨Mt ^ 2 * Ml + M4, by positivity, ?_⟩
  intro N hN delta x hdelta hdelta1 hx hscale K hK hKorig
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hKpoly : K ≤ Ck * (Real.log (Real.exp 1 + x)) ^ sk := by
    calc
      _ ≤ CK * (Real.log x) ^ sK := hKorig
      _ ≤ (|CK| + 1) * (Real.log x) ^ sK :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self CK]) (Real.rpow_nonneg hlog0.le _)
      _ ≤ (|CK| + 1) * (max 1 ((Real.log 2) ^ sK) *
          (Real.log (Real.exp 1 + x)) ^ (max sK 0)) :=
        mul_le_mul_of_nonneg_left (log_rpow_le_shifted_log_rpow sK x hx) (by positivity)
      _ = _ := by dsimp [Ck, sk]; ring
  let R := sourceSampleRadius N alpha K delta
  let tau := sourceSampleHilbertSchmidtEnvelope d c C g p q R
  have hR : 0 < R := sourceSampleRadius_pos N alpha K delta hN hK hdelta hdelta1
  have hRpoly : R ≤ Cr * (Real.log (Real.exp 1 + x)) ^ sr :=
    sourceSampleRadius_le_shifted_polylog N alpha K delta x Ck sk hN halpha hdelta hdelta1
      hx hscale hCk.le hKpoly
  have htau0 : 0 ≤ tau := le_trans (by norm_num) (one_le_sourceSampleHilbertSchmidtEnvelope d c C g p q R)
  have htau : tau ≤ Mt * x ^ (epsilon / 4) := by
    have ht' := ht d R hR.le
    have ht'' := hMtbound x hx R hR.le hRpoly
    exact ht'.trans (by simpa only [mul_assoc] using ht'')
  have htausq : tau ^ 2 ≤ Mt ^ 2 * x ^ (epsilon / 2) := by
    calc
      _ ≤ (Mt * x ^ (epsilon / 4)) ^ 2 := pow_le_pow_left₀ htau0 htau 2
      _ = _ := by
        rw [mul_pow, ← Real.rpow_mul_natCast hx0.le]
        congr 2
        norm_num
        ring
  have hlog := hMlbound N hN delta x hdelta hdelta1 hx hscale
  have hfour := (h4 K hK).trans (hM4bound x hx K hK.le hKpoly)
  have hprod : tau ^ 2 * Real.sqrt (Real.log (8 / delta)) ≤
      (Mt ^ 2 * Ml) * x ^ epsilon := by
    calc
      _ ≤ (Mt ^ 2 * x ^ (epsilon / 2)) * (Ml * x ^ (epsilon / 2)) :=
        mul_le_mul htausq hlog (Real.sqrt_nonneg _) (by positivity)
      _ = (Mt ^ 2 * Ml) * (x ^ (epsilon / 2) * x ^ (epsilon / 2)) := by ring
      _ = _ := by rw [← Real.rpow_add hx0]; congr 2; ring
  change tau ^ 2 * Real.sqrt (Real.log (8 / delta)) + _ ≤ _
  nlinarith

end PaperFormalization.Manuscript
