import PaperFormalization.Manuscript.SubpolynomialEnvelope

/-! # Uniform polylogarithmic substitution into the source scale

Constants are chosen before the varying radius and scale. The finite-prefix
argument upgrades eventual subpolynomial absorption to every x>=2. These are
deterministic bounds; no probability law or localization event is assumed.
-/

open Filter
open scoped Topology

namespace PaperFormalization.Manuscript

/-- A polynomial of log(e+x) inside the actual chi scale is controlled by a
fixed multiple of the exact shifted log-log power. -/
theorem featureScaleChi_le_loglog_of_le_polylog (p C s x R : ℝ)
    (hp : 1 < p) (hC : 0 ≤ C) (hs : 0 ≤ s) (hx : 0 ≤ x) (hR : 0 ≤ R)
    (hbound : R ≤ C * (Real.log (Real.exp 1 + x)) ^ s) :
    featureScaleChi p R ≤
      (1 + Real.log (Real.exp 1 + C) + s) ^ (p / (p - 1)) *
        (1 + Real.log (Real.log (Real.exp 1 + x))) ^ (p / (p - 1)) := by
  let l := Real.log (Real.exp 1 + x)
  have hl : 1 ≤ l := one_le_featureScaleLog x hx
  have hl0 : 0 < l := by linarith
  have hll : 0 ≤ Real.log l := Real.log_nonneg hl
  have hpow : 1 ≤ l ^ s := Real.one_le_rpow hl hs
  have hC1 : 1 ≤ Real.log (Real.exp 1 + C) := one_le_featureScaleLog C hC
  have hprod : Real.exp 1 + R ≤ (Real.exp 1 + C) * l ^ s := by
    nlinarith [Real.exp_pos (1 : ℝ)]
  have hlog : Real.log (Real.exp 1 + R) ≤
      (1 + Real.log (Real.exp 1 + C) + s) * (1 + Real.log l) := by
    calc
      _ ≤ Real.log ((Real.exp 1 + C) * l ^ s) :=
        Real.log_le_log (by positivity) hprod
      _ = Real.log (Real.exp 1 + C) + s * Real.log l := by
        rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos hl0 s).ne', Real.log_rpow hl0]
      _ ≤ _ := by nlinarith
  unfold featureScaleChi
  calc
    _ ≤ ((1 + Real.log (Real.exp 1 + C) + s) * (1 + Real.log l)) ^ (p / (p - 1)) :=
      Real.rpow_le_rpow (by linarith [one_le_featureScaleLog R hR]) hlog (by positivity)
    _ = _ := Real.mul_rpow (by linarith) (by linarith)

/-- The shifted log-log envelope is subpolynomial uniformly over every x>=2,
with a single fixed constant covering the bounded prefix. -/
theorem exists_shifted_loglog_envelope_le_rpow_all
    (A B r epsilon : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 0 ≤ r) (he : 0 < epsilon) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, 2 ≤ x →
      B * Real.exp (A * (1 + Real.log (Real.log (Real.exp 1 + x))) ^ r) ≤
        M * x ^ epsilon := by
  obtain ⟨X, hX⟩ := eventually_atTop.1
    (eventually_shifted_loglog_envelope_le_rpow A B r epsilon hA hB hr he)
  let x0 := max 2 X
  let M := 1 + B * Real.exp (A * (1 + Real.log (Real.log (Real.exp 1 + x0))) ^ r)
  have hx0 : 2 ≤ x0 := le_max_left _ _
  have hM : 0 < M := by dsimp [M]; positivity
  have hM1 : 1 ≤ M := by
    dsimp [M]
    exact le_add_of_nonneg_right (mul_nonneg hB (Real.exp_pos _).le)
  refine ⟨M, hM, ?_⟩
  intro x hx
  have hxpow : 1 ≤ x ^ epsilon := Real.one_le_rpow (by linarith) he.le
  by_cases hlarge : x0 ≤ x
  · have ht := hX x ((le_max_right 2 X).trans hlarge)
    exact ht.trans (by nlinarith [Real.rpow_nonneg (by linarith : 0 ≤ x) epsilon])
  · have hxx0 : x ≤ x0 := (lt_of_not_ge hlarge).le
    have hlog : Real.log (Real.exp 1 + x) ≤ Real.log (Real.exp 1 + x0) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlog0 : 0 < Real.log (Real.exp 1 + x) :=
      lt_of_lt_of_le zero_lt_one (one_le_featureScaleLog x (by linarith))
    have hloglog : Real.log (Real.log (Real.exp 1 + x)) ≤
        Real.log (Real.log (Real.exp 1 + x0)) := Real.log_le_log hlog0 hlog
    have hbase : 0 ≤ 1 + Real.log (Real.log (Real.exp 1 + x)) := by
      linarith [Real.log_nonneg (one_le_featureScaleLog x (by linarith))]
    have hp : (1 + Real.log (Real.log (Real.exp 1 + x))) ^ r ≤
        (1 + Real.log (Real.log (Real.exp 1 + x0))) ^ r :=
      Real.rpow_le_rpow hbase (by linarith) hr
    have henv : B * Real.exp (A * (1 + Real.log (Real.log (Real.exp 1 + x))) ^ r) ≤
        B * Real.exp (A * (1 + Real.log (Real.log (Real.exp 1 + x0))) ^ r) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hp hA)) hB
    have hprefix : B * Real.exp (A * (1 + Real.log (Real.log (Real.exp 1 + x0))) ^ r) ≤ M := by
      dsimp [M]
      linarith
    exact (henv.trans hprefix).trans (by nlinarith)

/-- Every fixed exponential chi-envelope becomes uniformly subpolynomial
when its radius has a fixed polylogarithmic bound. The constant is chosen
before x and before any radius satisfying that bound. -/
theorem exists_exp_chi_polylog_le_rpow
    (A B p C s epsilon : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hp : 1 < p) (hC : 0 ≤ C) (hs : 0 ≤ s) (he : 0 < epsilon) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, 2 ≤ x → ∀ R : ℝ, 0 ≤ R →
      R ≤ C * (Real.log (Real.exp 1 + x)) ^ s →
      B * Real.exp (A * featureScaleChi p R) ≤ M * x ^ epsilon := by
  let c := (1 + Real.log (Real.exp 1 + C) + s) ^ (p / (p - 1))
  have hc : 0 ≤ c := Real.rpow_nonneg
    (by linarith [one_le_featureScaleLog C hC]) _
  obtain ⟨M, hM, hbound⟩ := exists_shifted_loglog_envelope_le_rpow_all
    (A * c) B (p / (p - 1)) epsilon (mul_nonneg hA hc) hB (by positivity) he
  refine ⟨M, hM, ?_⟩
  intro x hx R hR hpoly
  have hchi := featureScaleChi_le_loglog_of_le_polylog p C s x R hp hC hs (by linarith) hR hpoly
  calc
    _ ≤ B * Real.exp ((A * c) *
        (1 + Real.log (Real.log (Real.exp 1 + x))) ^ (p / (p - 1))) := by
      apply mul_le_mul_of_nonneg_left _ hB
      apply Real.exp_le_exp.mpr
      exact (mul_le_mul_of_nonneg_left hchi hA).trans_eq (by dsimp [c]; ring)
    _ ≤ _ := hbound x hx

/-- Any real power of log x is bounded by a nonnegative power of log(e+x)
with one fixed prefactor. This avoids requiring a source polylog exponent
to be nonnegative when applying the uniform envelopes. -/
theorem log_rpow_le_shifted_log_rpow (s x : ℝ) (hx : 2 ≤ x) :
    (Real.log x) ^ s ≤ max 1 ((Real.log 2) ^ s) *
      (Real.log (Real.exp 1 + x)) ^ (max s 0) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogx : Real.log (2 : ℝ) ≤ Real.log x := Real.log_le_log (by norm_num) hx
  by_cases hs : 0 ≤ s
  · rw [max_eq_left hs]
    have hmono : (Real.log x) ^ s ≤ (Real.log (Real.exp 1 + x)) ^ s :=
      Real.rpow_le_rpow (by linarith) (Real.log_le_log (by linarith)
        (by linarith [Real.exp_pos (1 : ℝ)])) hs
    have hbase : 0 ≤ (Real.log (Real.exp 1 + x)) ^ s :=
      Real.rpow_nonneg (by linarith [one_le_featureScaleLog x (by linarith)]) _
    have hmax : 1 ≤ max 1 ((Real.log 2) ^ s) := le_max_left _ _
    nlinarith
  · have hs0 : s ≤ 0 := (lt_of_not_ge hs).le
    rw [max_eq_right hs0, Real.rpow_zero, mul_one]
    exact (Real.rpow_le_rpow_of_nonpos hlog2 hlogx hs0).trans (le_max_right _ _)

end PaperFormalization.Manuscript
