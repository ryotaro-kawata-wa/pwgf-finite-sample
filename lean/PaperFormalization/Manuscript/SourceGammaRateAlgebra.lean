import PaperFormalization.Manuscript.SourceGammaSubpolynomial

/-! # Literal Gamma scale, concentration logarithm and final rate algebra -/
namespace PaperFormalization.Manuscript

/-- The displayed scale in the convenient uniform Gamma lemma. -/
noncomputable def sourceGammaScale (N J : ℕ) (T B p : ℝ) : ℝ :=
  3*(N : ℝ)*(Real.exp 1+T)*(J+1)*(1+B)/p

/-- Xi dominates N, and the literal labelled-grid ratio Q/(p/3) is at most
2 Xi. Neither schedule count nor the path speed is hidden in a constant. -/
theorem sourceGammaScale_bounds (N J : ℕ) (T B p : ℝ)
    (hN : 0 < N) (hT : 0 ≤ T) (hB : 0 ≤ B) (hp : 0 < p) (hp1 : p ≤ 1) :
    2 ≤ sourceGammaScale N J T B p ∧ (N : ℝ) ≤ sourceGammaScale N J T B p ∧
    (((J+1 : ℕ) : ℝ)*((N+1 : ℕ) : ℝ))/(p/3) ≤ 2*sourceGammaScale N J T B p := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hj : (1 : ℝ) ≤ (J+1 : ℕ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le J))
  have he : 1 ≤ Real.exp (1 : ℝ)+T := by linarith [Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)]
  have hb : 1 ≤ 1+B := by linarith
  have hprod : (N : ℝ) ≤ (N : ℝ)*(Real.exp 1+T)*(J+1)*(1+B) := by
    calc
      _ ≤ (N : ℝ)*(Real.exp 1+T) := le_mul_of_one_le_right (by positivity) he
      _ ≤ (N : ℝ)*(Real.exp 1+T)*(J+1) := le_mul_of_one_le_right (by positivity) (show (1 : ℝ) ≤ (J : ℝ)+1 by linarith [show (0 : ℝ) ≤ J from Nat.cast_nonneg J])
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hb
  have hscale : 3*(N : ℝ) ≤ sourceGammaScale N J T B p := by
    unfold sourceGammaScale
    apply (le_div_iff₀ hp).mpr
    nlinarith
  refine ⟨by linarith,by linarith,?_⟩
  have hNJ : (N : ℝ)*(J+1) ≤ (N : ℝ)*(Real.exp 1+T)*(J+1)*(1+B) := by
    calc
      _ ≤ (N : ℝ)*(Real.exp 1+T)*(J+1) := mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) he) (by positivity)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hb
  unfold sourceGammaScale
  simp only [Nat.cast_add, Nat.cast_one]
  apply (div_le_iff₀ (by positivity : 0 < p/3)).mpr
  have hpne := hp.ne'
  field_simp
  nlinarith

/-- The actual square-root concentration logarithm is uniformly absorbed,
with a constant chosen before Xi and every ratio bounded by C Xi. -/
theorem exists_sqrt_log_multiple_le_rpow (C epsilon : ℝ) (hC : 1 ≤ C) (he : 0 < epsilon) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, 2 ≤ x → ∀ y : ℝ, 0 < y → y ≤ C*x →
      Real.sqrt (Real.log y) ≤ M*x^epsilon := by
  have hC0 : 0 < C := by linarith
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  obtain ⟨M,hM,hbound⟩ := exists_shifted_loglog_envelope_le_rpow_all
    1 (2+Real.log C) 1 epsilon (by norm_num) (by positivity) (by norm_num) he
  refine ⟨M,hM,?_⟩
  intro x hx y hy hyb
  have hx0 : 0 < x := by linarith
  have hl : 1 ≤ Real.log (Real.exp 1+x) := one_le_featureScaleLog x (by linarith)
  have hl0 : 0 < Real.log (Real.exp 1+x) := by linarith
  have hlogx : Real.log x ≤ Real.log (Real.exp 1+x) :=
    Real.log_le_log hx0 (by linarith [Real.exp_pos (1 : ℝ)])
  have hlog : 0 ≤ Real.log (C*x) := Real.log_nonneg (by nlinarith)
  have hsqrt : Real.sqrt (Real.log (C*x)) ≤ 1+Real.log (C*x) := by
    nlinarith [Real.sq_sqrt hlog,Real.sqrt_nonneg (Real.log (C*x))]
  have hlinear : 1+Real.log (C*x) ≤ (2+Real.log C)*Real.log (Real.exp 1+x) := by
    rw [Real.log_mul hC0.ne' hx0.ne']
    nlinarith
  have hlogexp : Real.log (Real.exp 1+x) ≤
      Real.exp (1*(1+Real.log (Real.log (Real.exp 1+x)))^(1 : ℝ)) := by
    rw [Real.rpow_one,one_mul]
    calc
      _ = Real.exp (Real.log (Real.log (Real.exp 1+x))) := (Real.exp_log hl0).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  exact ((Real.sqrt_le_sqrt (Real.log_le_log hy hyb)).trans hsqrt).trans
    (hlinear.trans ((mul_le_mul_of_nonneg_left hlogexp (by positivity)).trans (hbound x hx)))

/-- The literal four-term Gamma threshold reduces to the claimed rate.
The constants A0 and Q0 separately record coefficient and log absorption. -/
theorem source_gamma_threshold_rate (N : ℕ) (x epsilon A Lambda beta A0 Q0 B T Q r : ℝ)
    (hN : 0 < N) (hx : 1 ≤ x) (he : 0 ≤ epsilon)
    (hA0 : 0 ≤ A0) (hQ0 : 0 ≤ Q0) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hA : A ≤ A0*x^(epsilon/2)) (hLambda : Lambda ≤ A0*x^(epsilon/2))
    (hbeta : beta ≤ (N : ℝ)⁻¹) (hQr : 1 ≤ Q/r)
    (hlog : Real.sqrt (Real.log (Q/r)) ≤ Q0*x^(epsilon/2)) :
    beta + A/Real.sqrt N + A*Real.sqrt (Real.log (Q/r)/(2*N)) + 2*B*T*Lambda/N ≤
      (1+A0+A0*Q0+2*A0)*x^epsilon*((Real.sqrt N)⁻¹+B*T/N) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hn0
  have hx0 : 0 < x := by linarith
  have hxpow : 1 ≤ x^epsilon := Real.one_le_rpow hx he
  have hhalf : x^(epsilon/2) ≤ x^epsilon := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hroot : Real.sqrt (Real.log (Q/r)/(2*N)) ≤
      (Q0*x^(epsilon/2))/Real.sqrt N := by
    calc
      _ = Real.sqrt (Real.log (Q/r))/Real.sqrt (2*(N : ℝ)) := Real.sqrt_div (Real.log_nonneg hQr) _
      _ ≤ (Q0*x^(epsilon/2))/Real.sqrt N :=
        div_le_div₀ (by positivity) hlog hsqrt (Real.sqrt_le_sqrt (by nlinarith))
  have hbeta' : beta ≤ (Real.sqrt N)⁻¹ := by
    apply hbeta.trans
    simpa only [one_div] using one_div_le_one_div_of_le hsqrt (show Real.sqrt (N : ℝ) ≤ (N : ℝ) by nlinarith [Real.sq_sqrt hn0.le,Real.sqrt_nonneg (N : ℝ)])
  have hmain : A/Real.sqrt N ≤ A0*x^epsilon/Real.sqrt N :=
    div_le_div_of_nonneg_right (hA.trans (mul_le_mul_of_nonneg_left hhalf hA0)) hsqrt.le
  have hfluct : A*Real.sqrt (Real.log (Q/r)/(2*N)) ≤
      A0*Q0*x^epsilon/Real.sqrt N := by
    calc
      _ ≤ (A0*x^(epsilon/2))*((Q0*x^(epsilon/2))/Real.sqrt N) :=
        mul_le_mul hA hroot (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by
        rw [show A0*x^(epsilon/2)*(Q0*x^(epsilon/2)/Real.sqrt N) =
          A0*Q0*(x^(epsilon/2)*x^(epsilon/2))/Real.sqrt N by ring,
          ← Real.rpow_add hx0]
        rw [show epsilon/2+epsilon/2=epsilon by ring]
  have htime : 2*B*T*Lambda/N ≤ 2*A0*x^epsilon*(B*T/N) := by
    have h := mul_le_mul_of_nonneg_left (hLambda.trans (mul_le_mul_of_nonneg_left hhalf hA0))
      (show 0 ≤ 2*B*T/(N : ℝ) by positivity)
    calc
      _ = (2*B*T/(N : ℝ))*Lambda := by ring
      _ ≤ (2*B*T/(N : ℝ))*(A0*x^epsilon) := h
      _ = _ := by ring
  have hbn : 0 ≤ B*T/(N : ℝ) := by positivity
  have hi : 0 ≤ (Real.sqrt (N : ℝ))⁻¹ := by positivity
  have hbeta'' : beta ≤ x^epsilon*(Real.sqrt N)⁻¹ := hbeta'.trans (by nlinarith)
  have hrest : 0 ≤ (1+A0+A0*Q0)*x^epsilon*(B*T/N) + 2*A0*x^epsilon*(Real.sqrt N)⁻¹ := by positivity
  simp only [div_eq_mul_inv] at hmain hfluct htime hrest ⊢
  nlinarith
end PaperFormalization.Manuscript
