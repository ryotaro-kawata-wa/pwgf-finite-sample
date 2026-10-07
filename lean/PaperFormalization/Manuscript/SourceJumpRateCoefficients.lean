import PaperFormalization.Manuscript.UniformDriftJumpCoefficients
import PaperFormalization.Manuscript.SourceGammaRateAlgebra

/-! # The literal Gaussian jump coefficient is uniformly subpolynomial

The printed budget is p/(8(J+1)). The jump count is retained in its logarithm
and in the supplied scale inequality, never absorbed as a fixed parameter.
Dimension and the original objective anchor are fixed before all scales.
-/
open scoped NNReal
namespace PaperFormalization.Manuscript

/-- The exact printed Gaussian factor at p/(8(J+1)) is subpolynomial in
any Xi dominating (J+1)/p. No upper bound on J is needed here. -/
theorem exists_sourceGaussianDeviation_subpolynomial (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ x : ℝ, 2 ≤ x → ∀ J : ℕ, ∀ p : ℝ, 0 < p →
      ((J : ℝ)+1)/p ≤ x →
      sourceGaussianDeviation (p/(8*((J : ℝ)+1))) ≤ Q*x^epsilon := by
  obtain ⟨Q,hQ,hbound⟩ := exists_sqrt_log_multiple_le_rpow 16 epsilon (by norm_num) he
  refine ⟨1+Real.sqrt 2*Q, by positivity, ?_⟩
  intro x hx J p hp hscale
  have hratio : 0 < 16*((J : ℝ)+1)/p := by positivity
  have hb := hbound x hx (16*((J : ℝ)+1)/p) hratio (by
    calc
      _ = 16*(((J : ℝ)+1)/p) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hscale (by norm_num))
  have hxpow : 1 ≤ x^epsilon := Real.one_le_rpow (by linarith) he.le
  unfold sourceGaussianDeviation
  rw [show 2/(p/(8*((J : ℝ)+1))) = 16*((J : ℝ)+1)/p by field_simp; ring,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith [mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg (2 : ℝ))]

section Source
variable {E : Type*} [Zero E] {H : ℕ → Type*}
  [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℝ (H n)]

/-- The actual c_J uses the original feature series and local objective
coefficient. Both source polylog exponents may be arbitrary real numbers. -/
theorem exists_source_jump_gaussian_coefficient_subpolynomial
    (d : ℕ) (c C g pDecay q alpha C3 CK sK CD sD epsilon : ℝ)
    (φ : ∀ n, E → H n) (G : lp H 2 → ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hpDecay : 1 < pDecay) (hq : q < pDecay)
    (halpha : 0 < alpha) (he : 0 < epsilon) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, 2 ≤ x → ∀ K D : ℝ,
      0 < K → 1 ≤ D → K ≤ CK*(1+Real.log x)^sK → D ≤ CD*(1+Real.log x)^sD →
      ∀ J : ℕ, ∀ p : ℝ, 0 < p → ((J : ℝ)+1)/p ≤ x → ∀ L : ℝ≥0,
      (L : ℝ) = sourceComparisonEnvelope c C g pDecay q K D alpha C3 φ G →
      sourceJumpCoefficient d (featureDisplacementLambda c C g pDecay q D L) L *
        sourceGaussianDeviation (p/(8*((J : ℝ)+1))) ≤ M*x^epsilon := by
  obtain ⟨A,hA,hsource⟩ := exists_uniform_source_jump_coefficient_bound
    d c C g pDecay q alpha C3 φ G hc hC hpDecay hq halpha
  obtain ⟨Cj,hCj,hjump⟩ := exists_exp_chi_source_scales_le_rpow A A pDecay CK sK CD sD
    (epsilon/2) hA.le hA.le hpDecay (by positivity)
  obtain ⟨Cq,hCq,hgauss⟩ := exists_sourceGaussianDeviation_subpolynomial (epsilon/2) (by positivity)
  refine ⟨Cj*Cq, mul_pos hCj hCq, ?_⟩
  intro x hx K D hK hD hKb hDb J p hp hscale L hL
  have hcj := (hsource K hK D hD L hL).trans
    (hjump x hx K D hK.le (by linarith) hKb hDb)
  have hcq := hgauss x hx J p hp hscale
  have hq0 : 0 ≤ sourceGaussianDeviation (p/(8*((J : ℝ)+1))) :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_sourceGaussianDeviation _)
  calc
    _ ≤ (Cj*x^(epsilon/2))*(Cq*x^(epsilon/2)) :=
      mul_le_mul hcj hcq hq0 (by positivity)
    _ = (Cj*Cq)*(x^(epsilon/2)*x^(epsilon/2)) := by ring
    _ = _ := by
      rw [← Real.rpow_add (by linarith : 0 < x), show epsilon/2+epsilon/2=epsilon by ring]
end Source

/-- The literal Gamma scale dominates the Gaussian budget ratio, uniformly
in the jump count; this discharges the scale input of the preceding theorem. -/
theorem sourceGammaScale_jump_budget_ratio (N J : ℕ) (T B p : ℝ)
    (hN : 0 < N) (hT : 0 ≤ T) (hB : 0 ≤ B) (hp : 0 < p) :
    ((J : ℝ)+1)/p ≤ sourceGammaScale N J T B p := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have he : 1 ≤ Real.exp (1 : ℝ)+T := by
    linarith [Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)]
  have hb : 1 ≤ 1+B := by linarith
  have hprod : 1 ≤ (N : ℝ)*(Real.exp 1+T)*(1+B) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hN1 he) hb
  unfold sourceGammaScale
  apply (div_le_div_iff₀ hp hp).mpr
  have hmul := mul_le_mul_of_nonneg_right hprod (show 0 ≤ (J : ℝ)+1 by positivity)
  nlinarith

end PaperFormalization.Manuscript
