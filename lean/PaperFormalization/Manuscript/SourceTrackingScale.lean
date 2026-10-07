import PaperFormalization.Manuscript.SourceGammaRateAlgebra

/-! # The literal fixed-schedule tracking scale on growing horizons

The convenient-Gamma budget is 3p/8, so its scale is exactly the source
8N(e+T)(J+1)(1+B)/p. The polynomial majorant keeps the fixed speed and
jump-count cap visible; it is uniform in the admitted N,T,p.
-/
namespace PaperFormalization.Manuscript

/-- Exact budget substitution from the convenient Gamma scale to the source
fixed-schedule scale. -/
theorem sourceTrackingScale_eq (N J : ℕ) (T B p : ℝ) :
    sourceGammaScale N J T B (3*p/8) =
      8*(N : ℝ)*(Real.exp 1+T)*((J : ℝ)+1)*(1+B)/p := by
  simp only [sourceGammaScale, div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- Original horizon and confidence restrictions give the source exponent
5/4+Cp. The explicit coefficient depends only on fixed L0 and B. -/
theorem sourceTrackingScale_le_polynomial
    (N J : ℕ) (T B p nu zeta Cp L0 : ℝ)
    (hN : 0 < N) (hB : 0 ≤ B) (hp : 0 < p)
    (hnu : 0 ≤ nu) (hzeta : 0 ≤ zeta) (hJ : (J : ℝ) ≤ L0)
    (hT : T ≤ (N : ℝ)^(1/4-nu-zeta)) (hpN : (N : ℝ)^(-Cp) ≤ p) :
    sourceGammaScale N J T B (3*p/8) ≤
      (8*(Real.exp 1+1)*(L0+1)*(1+B))*(N : ℝ)^(5/4+Cp) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hnq : 1 ≤ (N : ℝ)^(1/4 : ℝ) := Real.one_le_rpow hn (by norm_num)
  have hTq : T ≤ (N : ℝ)^(1/4 : ℝ) := hT.trans
    (Real.rpow_le_rpow_of_exponent_le hn (by linarith))
  have htime : Real.exp 1+T ≤ (Real.exp 1+1)*(N : ℝ)^(1/4 : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hnq (Real.exp_pos 1).le]
  have hinv : p⁻¹ ≤ (N : ℝ)^Cp := by
    have hi := one_div_le_one_div_of_le (Real.rpow_pos_of_pos hn0 (-Cp)) hpN
    simpa only [one_div, Real.rpow_neg hn0.le, inv_inv] using hi
  have hJ0 : 0 ≤ (J : ℝ)+1 := by positivity
  have hL0 : 0 ≤ L0+1 := hJ0.trans (by linarith)
  have hmain : (Real.exp 1+T)*((J : ℝ)+1) ≤
      ((Real.exp 1+1)*(N : ℝ)^(1/4 : ℝ))*(L0+1) :=
    mul_le_mul htime (by linarith) hJ0 (by positivity)
  have hden := mul_le_mul hmain hinv (by positivity : 0 ≤ p⁻¹) (by positivity)
  have h := mul_le_mul_of_nonneg_left hden (show 0 ≤ 8*(N : ℝ)*(1+B) by positivity)
  calc
    _ = (8*(N : ℝ)*(1+B))*((Real.exp 1+T)*((J : ℝ)+1)*p⁻¹) := by
      rw [sourceTrackingScale_eq]
      ring
    _ ≤ (8*(N : ℝ)*(1+B))*
      (((Real.exp 1+1)*(N : ℝ)^(1/4 : ℝ))*(L0+1)*(N : ℝ)^Cp) := h
    _ = (8*(Real.exp 1+1)*(L0+1)*(1+B))*
        ((N : ℝ)^(1 : ℝ)*(N : ℝ)^(1/4 : ℝ)*(N : ℝ)^Cp) := by
      rw [Real.rpow_one]
      ring
    _ = _ := by
      rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
      congr 2
      ring

/-- The source exponent constraint absorbs a power of the actual tracking
scale into N^(zeta/2), with the fixed coefficient displayed explicitly. -/
theorem sourceTrackingScale_power_le
    (N J : ℕ) (T B p nu zeta Cp L0 a : ℝ)
    (hN : 0 < N) (hT0 : 0 ≤ T) (hB : 0 ≤ B) (hp : 0 < p)
    (hnu : 0 ≤ nu) (hzeta : 0 ≤ zeta) (hJ : (J : ℝ) ≤ L0)
    (hT : T ≤ (N : ℝ)^(1/4-nu-zeta)) (hpN : (N : ℝ)^(-Cp) ≤ p)
    (ha : 0 ≤ a) (hexp : (5/4+Cp)*a ≤ zeta/2) :
    (sourceGammaScale N J T B (3*p/8))^a ≤
      (8*(Real.exp 1+1)*(L0+1)*(1+B))^a*(N : ℝ)^(zeta/2) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hL0 : 0 ≤ L0+1 := by linarith [Nat.cast_nonneg (α := ℝ) J]
  have hscale0 : 0 ≤ sourceGammaScale N J T B (3*p/8) := by unfold sourceGammaScale; positivity
  calc
    _ ≤ ((8*(Real.exp 1+1)*(L0+1)*(1+B))*(N : ℝ)^(5/4+Cp))^a :=
      Real.rpow_le_rpow hscale0 (sourceTrackingScale_le_polynomial N J T B p nu zeta Cp L0
        hN hB hp hnu hzeta hJ hT hpN) ha
    _ = (8*(Real.exp 1+1)*(L0+1)*(1+B))^a*(N : ℝ)^((5/4+Cp)*a) := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hn0.le _), ← Real.rpow_mul hn0.le]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn hexp) (by positivity)

end PaperFormalization.Manuscript
