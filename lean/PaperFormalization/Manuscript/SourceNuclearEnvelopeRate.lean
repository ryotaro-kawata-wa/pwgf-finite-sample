import PaperFormalization.Manuscript.SourceSampleSubpolynomial
import PaperFormalization.Manuscript.SourceGammaSubpolynomial

/-! # The full literal source nuclear covariance envelope is subpolynomial

The exact sampled radius, max-one threshold, sharp fourth-moment series and
local factor L_D squared remain in the left side. Constants are chosen before
N, delta, Xi, K, D and L. The original real polylog exponents may be negative.
This is deterministic coefficient algebra; it changes no probability law.
-/

open scoped NNReal
namespace PaperFormalization.Manuscript

/-- Original powers of log Xi admit a fixed multiple of powers of 1+log Xi,
including negative exponents, uniformly for Xi at least two. -/
theorem log_rpow_le_one_add_log_rpow (s x : ℝ) (hx : 2 ≤ x) :
    (Real.log x) ^ s ≤ max 1 ((Real.log 2) ^ s) * (1 + Real.log x) ^ (max s 0) := by
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hl : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlx : 0 ≤ Real.log x := le_trans hl2.le hl
  by_cases hs : 0 ≤ s
  · rw [max_eq_left hs]
    have hp := Real.rpow_le_rpow hlx (by linarith : Real.log x ≤ 1 + Real.log x) hs
    exact hp.trans (le_mul_of_one_le_left (Real.rpow_nonneg (by linarith) _) (le_max_left _ _))
  · rw [max_eq_right (le_of_not_ge hs), Real.rpow_zero, mul_one]
    exact (Real.rpow_le_rpow_of_nonpos hl2 hl (le_of_not_ge hs)).trans (le_max_right _ _)

section Objective
variable {E : Type*} [Zero E] {H : ℕ → Type*}
  [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℝ (H n)]

/-- The actual source local field coefficient has a uniform arbitrary-power
bound under the original log-radius hypotheses. The anchor is fixed before
all varying scales; no objective smoothness beyond that needed to define the
literal coefficient is added to this deterministic estimate. -/
theorem exists_uniform_sourceComparisonEnvelope_log_subpolynomial
    (c C g p q alpha C3 CK sK CD sD epsilon : ℝ)
    (φ : ∀ n, E → H n) (G : lp H 2 → ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (halpha : 0 < alpha) (he : 0 < epsilon) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, 2 ≤ x → ∀ K D : ℝ, 0 < K → 1 ≤ D →
      K ≤ CK * (Real.log x) ^ sK → D ≤ CD * (Real.log x) ^ sD →
      |sourceComparisonEnvelope c C g p q K D alpha C3 φ G| ≤ M * x ^ epsilon := by
  let Ck := (|CK| + 1) * max 1 ((Real.log 2) ^ sK)
  let Cd := (|CD| + 1) * max 1 ((Real.log 2) ^ sD)
  obtain ⟨A, hA, hfield⟩ := exists_uniform_sourceComparisonEnvelope_bound
    c C g p q alpha C3 φ G hc hC hp hq halpha
  obtain ⟨M, hM, hbound⟩ := exists_exp_chi_source_scales_le_rpow
    A A p Ck (max sK 0) Cd (max sD 0) epsilon hA.le hA.le hp he
  refine ⟨M, hM, ?_⟩
  intro x hx K D hK hD hKb hDb
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have helper (C s : ℝ) : C * (Real.log x) ^ s ≤
      ((|C| + 1) * max 1 ((Real.log 2) ^ s)) * (1 + Real.log x) ^ (max s 0) := by
    calc
      _ ≤ (|C| + 1) * (Real.log x) ^ s :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) (Real.rpow_nonneg hlog _)
      _ ≤ (|C| + 1) * (max 1 ((Real.log 2) ^ s) * (1 + Real.log x) ^ (max s 0)) :=
        mul_le_mul_of_nonneg_left (log_rpow_le_one_add_log_rpow s x hx) (by positivity)
      _ = _ := by ring
  exact (hfield K hK D hD).trans (hbound x hx K D hK.le (by linarith)
    (hKb.trans (helper CK sK)) (hDb.trans (helper CD sD)))
end Objective

/-- The exact covariance numerator is bounded by the previously controlled
combination tau squared times sqrt log plus C4. Young's inequality supplies
the mixed term; a fixed positive log(8) lower bound absorbs tau squared. -/
theorem source_nuclear_numerator_le_sample_combination (tau C4 delta : ℝ)
    (hC4 : 0 ≤ C4) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    tau * (2 * Real.sqrt C4 + tau * Real.sqrt (2 * Real.log (8 / delta))) ≤
      (1 / Real.sqrt (Real.log 8) + 1 + Real.sqrt 2) *
        (tau ^ 2 * Real.sqrt (Real.log (8 / delta)) + C4) := by
  have hlog8 : 0 < Real.log (8 : ℝ) := Real.log_pos (by norm_num)
  have hlambda : 0 < Real.sqrt (Real.log (8 : ℝ)) := Real.sqrt_pos.mpr hlog8
  have hratio : (8 : ℝ) ≤ 8 / delta := (le_div_iff₀ hdelta).mpr (by nlinarith)
  have hlog : Real.log 8 ≤ Real.log (8 / delta) := Real.log_le_log (by norm_num) hratio
  have hroot : Real.sqrt (Real.log 8) ≤ Real.sqrt (Real.log (8 / delta)) := Real.sqrt_le_sqrt hlog
  let Q := tau ^ 2 * Real.sqrt (Real.log (8 / delta)) + C4
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have htau : tau ^ 2 ≤ Q / Real.sqrt (Real.log 8) := by
    apply (le_div_iff₀ hlambda).mpr
    have h := mul_le_mul_of_nonneg_left hroot (sq_nonneg tau)
    dsimp [Q]
    linarith
  have hC : C4 ≤ Q := by
    dsimp [Q]
    linarith [mul_nonneg (sq_nonneg tau) (Real.sqrt_nonneg (Real.log (8 / delta)))]
  have hterm : tau ^ 2 * Real.sqrt (Real.log (8 / delta)) ≤ Q := by dsimp [Q]; linarith
  have hyoung : 2 * tau * Real.sqrt C4 ≤ tau ^ 2 + C4 := by
    nlinarith [sq_nonneg (tau - Real.sqrt C4), Real.sq_sqrt hC4]
  calc
    _ = 2 * tau * Real.sqrt C4 + Real.sqrt 2 *
        (tau ^ 2 * Real.sqrt (Real.log (8 / delta))) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    _ ≤ tau ^ 2 + C4 + Real.sqrt 2 * (tau ^ 2 * Real.sqrt (Real.log (8 / delta))) :=
      add_le_add hyoung le_rfl
    _ ≤ Q / Real.sqrt (Real.log 8) + Q + Real.sqrt 2 * Q :=
      add_le_add (add_le_add htau hC) (mul_le_mul_of_nonneg_left hterm (Real.sqrt_nonneg _))
    _ = _ := by dsimp [Q]; ring

section Full
variable {E : Type*} [Zero E] {H : ℕ → Type*}
  [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℝ (H n)]

set_option maxHeartbeats 1600000 in
/-- The complete literal source covariance threshold, including actual L_D
squared, is at most C_epsilon Xi^epsilon/sqrt N. One positive constant is
chosen before N, delta, Xi, K, D and L; fixed dimension remains an explicit
parameter of that constant. Neither concentration nor a coefficient bound
is assumed as the conclusion. -/
theorem exists_uniform_source_nuclear_covariance_threshold_rate
    (d : ℕ) (c C g p q alpha C3 CK sK CD sD epsilon : ℝ)
    (φ : ∀ n, E → H n) (G : lp H 2 → ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (halpha : 0 < alpha) (he : 0 < epsilon) :
    ∃ M : ℝ, 0 < M ∧ ∀ N : ℕ, 0 < N → ∀ delta x : ℝ,
      0 < delta → delta ≤ 1 → 2 ≤ x → (N : ℝ) / delta ≤ x →
      ∀ K D : ℝ, 0 < K → 1 ≤ D → K ≤ CK * (Real.log x) ^ sK → D ≤ CD * (Real.log x) ^ sD →
      ∀ L : ℝ≥0, (L : ℝ) = sourceComparisonEnvelope c C g p q K D alpha C3 φ G →
      let C4 := sourceHilbertSchmidtFourthMoment d c C g p q alpha K
      let tau := sourceSampleHilbertSchmidtEnvelope d c C g p q (sourceSampleRadius N alpha K delta)
      (L : ℝ) ^ 2 * tau / Real.sqrt N *
        (2 * Real.sqrt C4 + tau * Real.sqrt (2 * Real.log (8 / delta))) ≤
          M * x ^ epsilon / Real.sqrt N := by
  obtain ⟨ML, hML, hlocal⟩ := exists_uniform_sourceComparisonEnvelope_log_subpolynomial
    c C g p q alpha C3 CK sK CD sD (epsilon / 4) φ G hc hC hp hq halpha (by positivity)
  obtain ⟨MS, hMS, hsample⟩ := exists_uniform_source_sample_envelope_subpolynomial
    d c C g p q alpha CK sK (epsilon / 2) hc hC hp hq halpha (by positivity)
  let B := 1 / Real.sqrt (Real.log 8) + 1 + Real.sqrt 2
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨ML ^ 2 * (B * MS), by positivity, ?_⟩
  intro N hN delta x hdelta hdelta1 hx hscale K D hK hD hKb hDb L hL
  let C4 := sourceHilbertSchmidtFourthMoment d c C g p q alpha K
  let tau := sourceSampleHilbertSchmidtEnvelope d c C g p q (sourceSampleRadius N alpha K delta)
  have hx0 : 0 < x := by linarith
  have htau : 0 ≤ tau := (by norm_num : (0 : ℝ) ≤ 1).trans
    (one_le_sourceSampleHilbertSchmidtEnvelope _ _ _ _ _ _ _)
  have hC4 : 0 ≤ C4 := sq_nonneg _
  have hLabs : (L : ℝ) ≤ |sourceComparisonEnvelope c C g p q K D alpha C3 φ G| := by
    rw [hL]
    exact le_abs_self _
  have hLbound : (L : ℝ) ≤ ML * x ^ (epsilon / 4) :=
    hLabs.trans (hlocal x hx K D hK hD hKb hDb)
  have hLsq : (L : ℝ) ^ 2 ≤ ML ^ 2 * x ^ (epsilon / 2) := by
    calc
      _ ≤ (ML * x ^ (epsilon / 4)) ^ 2 := pow_le_pow_left₀ L.coe_nonneg hLbound 2
      _ = _ := by
        rw [mul_pow, ← Real.rpow_mul_natCast hx0.le]
        congr 2
        norm_num
        ring
  have hsampleBound := hsample N hN delta x hdelta hdelta1 hx hscale K hK hKb
  have hnum : tau * (2 * Real.sqrt C4 + tau * Real.sqrt (2 * Real.log (8 / delta))) ≤
      (B * MS) * x ^ (epsilon / 2) := by
    exact (source_nuclear_numerator_le_sample_combination tau C4 delta hC4 hdelta hdelta1).trans
      ((mul_le_mul_of_nonneg_left hsampleBound hB.le).trans_eq (by dsimp [B]; ring))
  have hfull : (L : ℝ) ^ 2 * (tau * (2 * Real.sqrt C4 + tau * Real.sqrt (2 * Real.log (8 / delta)))) ≤
      (ML ^ 2 * (B * MS)) * x ^ epsilon := by
    calc
      _ ≤ (ML ^ 2 * x ^ (epsilon / 2)) * ((B * MS) * x ^ (epsilon / 2)) :=
        mul_le_mul hLsq hnum (by positivity) (by positivity)
      _ = (ML ^ 2 * (B * MS)) * (x ^ (epsilon / 2) * x ^ (epsilon / 2)) := by ring
      _ = _ := by rw [← Real.rpow_add hx0]; congr 2; ring
  calc
    _ = ((L : ℝ) ^ 2 * (tau * (2 * Real.sqrt C4 + tau * Real.sqrt (2 * Real.log (8 / delta))))) /
        Real.sqrt N := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hfull (Real.sqrt_nonneg _)
end Full

end PaperFormalization.Manuscript
