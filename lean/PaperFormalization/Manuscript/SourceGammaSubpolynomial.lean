import PaperFormalization.Manuscript.UniformGammaCoefficients
import PaperFormalization.Manuscript.PolylogFeatureEnvelope

/-! # Subpolynomial growth of the literal source Gamma coefficients

The population and localization radii retain their individual source
polylogarithmic powers. Constants precede the running scale and both radii.
-/
namespace PaperFormalization.Manuscript
open scoped NNReal

/-- Arbitrary real powers of 1+log x admit a nonnegative shifted-log
majorant with a fixed coefficient, including negative source powers. -/
theorem one_add_log_rpow_le_shifted_log_rpow (s x : ℝ) (hx : 2 ≤ x) :
    (1 + Real.log x) ^ s ≤ max 1 ((2 : ℝ) ^ s) *
      (Real.log (Real.exp 1 + x)) ^ (max s 0) := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hl : 1 ≤ Real.log (Real.exp 1 + x) := one_le_featureScaleLog x (by linarith)
  have hL : Real.log x ≤ Real.log (Real.exp 1 + x) :=
    Real.log_le_log (by linarith) (by linarith [Real.exp_pos (1 : ℝ)])
  by_cases hs : 0 ≤ s
  · rw [max_eq_left hs]
    calc
      _ ≤ (2 * Real.log (Real.exp 1 + x)) ^ s :=
        Real.rpow_le_rpow (by linarith) (by linarith) hs
      _ = (2 : ℝ)^s * (Real.log (Real.exp 1 + x))^s :=
        Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by linarith) _)
  · have hs0 : s ≤ 0 := (lt_of_not_ge hs).le
    rw [max_eq_right hs0, Real.rpow_zero, mul_one]
    exact (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) hs0).trans (le_max_left _ _)

/-- A uniform exponential chi(K+D) envelope stays subpolynomial under the
literal two source polylog bounds. Either source exponent may be negative. -/
theorem exists_exp_chi_source_scales_le_rpow
    (A B p CK sK CD sD epsilon : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hp : 1 < p) (he : 0 < epsilon) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, 2 ≤ x → ∀ K D : ℝ,
      0 ≤ K → 0 ≤ D → K ≤ CK * (1 + Real.log x)^sK →
      D ≤ CD * (1 + Real.log x)^sD →
      B * Real.exp (A * featureScaleChi p (K+D)) ≤ M * x^epsilon := by
  let k := (|CK|+1)*max 1 ((2 : ℝ)^sK)
  let d := (|CD|+1)*max 1 ((2 : ℝ)^sD)
  let s := max (max sK 0) (max sD 0)
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hs : 0 ≤ s := (le_max_right sK 0).trans (le_max_left _ _)
  obtain ⟨M,hM,hbound⟩ := exists_exp_chi_polylog_le_rpow A B p (k+d) s epsilon
    hA hB hp (add_nonneg hk hd) hs he
  refine ⟨M,hM,?_⟩
  intro x hx K D hK hD hKb hDb
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hl : 1 ≤ Real.log (Real.exp 1 + x) := one_le_featureScaleLog x (by linarith)
  have helper (C r : ℝ) (hr : max r 0 ≤ s) :
      C*(1+Real.log x)^r ≤ (|C|+1)*max 1 ((2 : ℝ)^r) *
        (Real.log (Real.exp 1 + x))^s := by
    calc
      _ ≤ (|C|+1) * (1+Real.log x)^r :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) (Real.rpow_nonneg (by linarith) _)
      _ ≤ (|C|+1) * (max 1 ((2 : ℝ)^r) * (Real.log (Real.exp 1+x))^(max r 0)) :=
        mul_le_mul_of_nonneg_left (one_add_log_rpow_le_shifted_log_rpow r x hx) (by positivity)
      _ ≤ _ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hl hr) (by positivity)
  apply hbound x hx (K+D) (add_nonneg hK hD)
  have hbK := hKb.trans (helper CK sK (le_max_left _ _))
  have hbD := hDb.trans (helper CD sD (le_max_right _ _))
  change K+D ≤ (k+d) * _
  change K ≤ k * _ at hbK
  change D ≤ d * _ at hbD
  nlinarith

section Objective
variable {E : Type*} [Zero E] {H : ℕ → Type*}
  [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℝ (H n)]

/-- The actual A, Lambda and exact S are uniformly subpolynomial, with one
constant before Xi,K,D,L and both original polylog exponents preserved. -/
theorem exists_uniform_source_gamma_coefficients_subpolynomial
    (c C g p q alpha C3 CK sK CD sD epsilon : ℝ)
    (φ : ∀ n, E → H n) (G : lp H 2 → ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (halpha : 0 < alpha) (he : 0 < epsilon) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, 2 ≤ x → ∀ K D : ℝ, 0 < K → 1 ≤ D →
      K ≤ CK * (1+Real.log x)^sK → D ≤ CD * (1+Real.log x)^sD → ∀ L : ℝ≥0,
      (L : ℝ) ≤ |sourceComparisonEnvelope c C g p q K D alpha C3 φ G| →
      (2 * ∑' n, (featureResidualWeight c p L n : ℝ) *
        (featureGrowth C g q n * (1+D^(n+1)))) ≤ M*x^epsilon ∧
      featureDisplacementLambda c C g p q D L ≤ M*x^epsilon ∧
      (∑' n, (featureResidualWeight c p L n : ℝ) *
        sourceCoordinateL2Envelope C g q alpha K n) ≤ M*x^epsilon := by
  obtain ⟨A,hA,hcoeff⟩ := exists_uniform_source_gamma_coefficients_bound
    c C g p q alpha C3 φ G hc hC hp hq halpha
  obtain ⟨M,hM,hbound⟩ := exists_exp_chi_source_scales_le_rpow A A p CK sK CD sD epsilon
    hA.le hA.le hp he
  refine ⟨M,hM,?_⟩
  intro x hx K D hK hD hKb hDb L hL
  have hb := hbound x hx K D hK.le (by linarith) hKb hDb
  obtain ⟨ha,hLambda,hS⟩ := hcoeff K hK D hD L hL
  exact ⟨ha.trans hb,hLambda.trans hb,hS.trans hb⟩
end Objective
end PaperFormalization.Manuscript
