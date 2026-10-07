import PaperFormalization.Manuscript.SourceUniformRadius
import PaperFormalization.Manuscript.SourceGammaRateAlgebra

/-! # The exact radius choice and one fixed coefficient for the source scale

The minimum coefficient depends only on the fixed marginal moment parameters.
Every larger coefficient works, allowing the same radius to meet clipping-bias
and path-localization requirements without a running-parameter-dependent choice.
-/
open MeasureTheory Set
open scoped BigOperators NNReal
namespace PaperFormalization.Manuscript

/-- Literal logarithmic radius choice implies the printed radius-tail budget. -/
theorem source_uniform_radius_bound_le_budget
    (J N : ℕ) (alpha K D T B pRad : ℝ) (hN : 0 < N)
    (halpha : 0 < alpha) (hK : 0 < K) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hp : 0 < pRad) (hp1 : pRad ≤ 1)
    (hchoice : 2 * Real.exp 1 * K *
      (1 + Real.log (2 * N * (2*((J : ℝ)+1) + B*T/(Real.exp 1*K))/pRad))^(1/alpha) ≤ D) :
    2 * Real.exp 1 * K ≤ D ∧
    2 * N * (2*((J : ℝ)+1) + 2*B*T/D) *
      Real.exp (-((D/(2*Real.exp 1*K))^alpha)) ≤ pRad := by
  let A := 2*(N : ℝ)*(2*((J : ℝ)+1)+B*T/(Real.exp 1*K))
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hJ : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have heK : 0 < Real.exp 1 * K := mul_pos (Real.exp_pos _) hK
  have hA : 1 ≤ A := by
    have hh : 0 ≤ B*T/(Real.exp 1*K) := by positivity
    dsimp [A]
    nlinarith
  have hr : 1 ≤ A/pRad := (le_div_iff₀ hp).mpr (by linarith)
  have hr0 : 0 < A/pRad := lt_of_lt_of_le zero_lt_one hr
  have hlog : 0 ≤ Real.log (A/pRad) := Real.log_nonneg hr
  have hpower : 1 ≤ (1+Real.log (A/pRad))^(1/alpha) :=
    Real.one_le_rpow (by linarith) (by positivity)
  change 2*Real.exp 1*K*(1+Real.log (A/pRad))^(1/alpha) ≤ D at hchoice
  have hD : 2*Real.exp 1*K ≤ D := by
    have hm := mul_le_mul_of_nonneg_left hpower (by positivity : 0 ≤ 2*Real.exp 1*K)
    nlinarith
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hD
  have hratio : (1+Real.log (A/pRad))^(1/alpha) ≤ D/(2*Real.exp 1*K) :=
    (le_div_iff₀ (by positivity : 0 < 2*Real.exp 1*K)).mpr (by simpa [mul_comm] using hchoice)
  have hpow : 1+Real.log (A/pRad) ≤ (D/(2*Real.exp 1*K))^alpha := by
    calc
      _ = ((1+Real.log (A/pRad))^(1/alpha))^alpha := by
        rw [← Real.rpow_mul (by linarith : 0 ≤ 1+Real.log (A/pRad)),
          one_div_mul_cancel halpha.ne', Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hratio halpha.le
  have hcount : 2*(N : ℝ)*(2*((J : ℝ)+1)+2*B*T/D) ≤ A := by
    have hterm : 2*B*T/D ≤ B*T/(Real.exp 1*K) := by
      apply (div_le_div_iff₀ hD0 heK).mpr
      nlinarith [mul_le_mul_of_nonneg_left hD (show 0 ≤ B*T by positivity)]
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hterm) (by positivity)
  have hexp : Real.exp (-((D/(2*Real.exp 1*K))^alpha)) ≤ pRad/A := by
    calc
      _ ≤ Real.exp (-Real.log (A/pRad)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_log hr0, inv_div]
  refine ⟨hD, ?_⟩
  calc
    _ ≤ A*(pRad/A) := mul_le_mul hcount hexp (Real.exp_pos _).le (by linarith)
    _ = pRad := by field_simp

/-- The radius union factor divided by p/3 is bounded by a fixed multiple
of the literal source Xi, with all N,J,T,B dependence left inside Xi. -/
theorem source_radius_union_ratio_le_scale (J N : ℕ) (K T B p : ℝ)
    (hK : 0 < K) (hT : 0 ≤ T) (hB : 0 ≤ B) (hp : 0 < p) :
    2*N*(2*((J : ℝ)+1)+B*T/(Real.exp 1*K))/(p/3) ≤
      (4+2/(Real.exp 1*K))*sourceGammaScale N J T B p := by
  have hJ : (1 : ℝ) ≤ (J : ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) J]
  have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp (by norm_num)
  have heK : 0 < Real.exp 1*K := by positivity
  have hcommon : 0 ≤ (Real.exp 1+T)*((J : ℝ)+1)*(1+B) := by positivity
  have hjb : (J : ℝ)+1 ≤ (Real.exp 1+T)*((J : ℝ)+1)*(1+B) := by
    have h1 := mul_le_mul_of_nonneg_right (show 1 ≤ Real.exp 1+T by linarith) (by linarith : 0 ≤ (J : ℝ)+1)
    have h2 := le_mul_of_one_le_right (show 0 ≤ (Real.exp 1+T)*((J : ℝ)+1) by positivity)
      (show 1 ≤ 1+B by linarith)
    nlinarith
  have htb : B*T ≤ (Real.exp 1+T)*((J : ℝ)+1)*(1+B) := by
    have h1 := mul_le_mul_of_nonneg_right (show T ≤ Real.exp 1+T by linarith) hB
    have h2 := le_mul_of_one_le_right (show 0 ≤ (Real.exp 1+T)*B by positivity) hJ
    nlinarith
  have hinner : 2*((J : ℝ)+1)+B*T/(Real.exp 1*K) ≤
      (2+1/(Real.exp 1*K))*((Real.exp 1+T)*((J : ℝ)+1)*(1+B)) := by
    have hdiv := div_le_div_of_nonneg_right htb heK.le
    calc
      _ ≤ 2*((Real.exp 1+T)*((J : ℝ)+1)*(1+B)) +
          ((Real.exp 1+T)*((J : ℝ)+1)*(1+B))/(Real.exp 1*K) :=
        add_le_add (mul_le_mul_of_nonneg_left hjb (by norm_num)) hdiv
      _ = _ := by ring
  have hm := mul_le_mul_of_nonneg_left hinner (show 0 ≤ 6*(N : ℝ)/p by positivity)
  unfold sourceGammaScale
  calc
    _ = (6*(N : ℝ)/p)*(2*((J : ℝ)+1)+B*T/(Real.exp 1*K)) := by ring
    _ ≤ _ := hm
    _ = _ := by ring

/-- One explicit minimum coefficient is chosen before N,J,T,B,p. Every
larger CD makes the actual CD(1+log Xi)^(1/alpha) radius satisfy the printed
logarithmic radius choice with the p/3 budget. -/
theorem source_fixed_radius_coefficient_choice
    (alpha K CD : ℝ) (halpha : 0 < alpha) (hK : 0 < K)
    (hCD : 2*Real.exp 1*K*(1+Real.log (4+2/(Real.exp 1*K)))^(1/alpha) ≤ CD)
    (J N : ℕ) (T B p : ℝ) (hN : 0 < N) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hp : 0 < p) (hp1 : p ≤ 1) :
    2*Real.exp 1*K*(1+Real.log (2*N*(2*((J : ℝ)+1)+B*T/(Real.exp 1*K))/(p/3)))^(1/alpha) ≤
      CD*(1+Real.log (sourceGammaScale N J T B p))^(1/alpha) := by
  let C := 4+2/(Real.exp 1*K)
  let x := sourceGammaScale N J T B p
  have hC : 1 ≤ C := by
    have hh : 0 ≤ 2/(Real.exp 1*K) := by positivity
    dsimp [C]
    linarith
  have hx : 2 ≤ x := (sourceGammaScale_bounds N J T B p hN hT hB hp hp1).1
  have hC0 : 0 < C := by linarith
  have hx0 : 0 < x := by linarith
  have hlC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hratio : 0 < 2*(N : ℝ)*(2*((J : ℝ)+1)+B*T/(Real.exp 1*K))/(p/3) := by positivity
  have hlog := Real.log_le_log hratio (source_radius_union_ratio_le_scale J N K T B p hK hT hB hp)
  change _ ≤ Real.log (C*x) at hlog
  rw [Real.log_mul hC0.ne' hx0.ne'] at hlog
  have hb : 1+Real.log (2*(N : ℝ)*(2*((J : ℝ)+1)+B*T/(Real.exp 1*K))/(p/3)) ≤
      (1+Real.log C)*(1+Real.log x) := by nlinarith
  have hbase : 0 ≤ 1+Real.log (2*(N : ℝ)*(2*((J : ℝ)+1)+B*T/(Real.exp 1*K))/(p/3)) := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hlarge : 1 ≤ 2*(N : ℝ)*(2*((J : ℝ)+1)+B*T/(Real.exp 1*K))/(p/3) := by
      apply (le_div_iff₀ (by positivity : 0 < p/3)).mpr
      have hterm : 0 ≤ B*T/(Real.exp 1*K) := by positivity
      nlinarith [Nat.cast_nonneg (α := ℝ) J]
    linarith [Real.log_nonneg hlarge]
  calc
    _ ≤ 2*Real.exp 1*K*((1+Real.log C)*(1+Real.log x))^(1/alpha) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hbase hb (by positivity)) (by positivity)
    _ = (2*Real.exp 1*K*(1+Real.log C)^(1/alpha))*(1+Real.log x)^(1/alpha) := by
      rw [Real.mul_rpow (by linarith) (by linarith)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hCD (by positivity)

/-- The fixed coefficient gives the actual two-cloud p/3 radius event under
the original law. It may be enlarged for another requirement without changing
the quantifier order or any source marginal hypothesis. -/
theorem source_two_cloud_fixed_radius_tail_le
    {E Ω : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
    (alpha K CD : ℝ) (halpha : 0 < alpha) (hK : 0 < K)
    (hCD : 2*Real.exp 1*K*(1+Real.log (4+2/(Real.exp 1*K)))^(1/alpha) ≤ CD)
    (J N : ℕ) (T p : ℝ) (B : ℝ≥0) (hN : 0 < N) (hT : 0 ≤ T)
    (hp : 0 < p) (hp1 : p ≤ 1)
    (a b : Fin (J+1) → ℝ) (hab : ∀ j, a j ≤ b j) (hbranch : ∑ j, (b j-a j) ≤ T)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (Z : Fin 2 → Fin N → Fin (J+1) → Ω → ℝ → E)
    (hLip : ∀ᵐ ω ∂ν, ∀ c i j, LipschitzOnWith B (Z c i j ω) (Icc (a j) (b j)))
    (hMarginal : ∀ c i j t, t ∈ Icc (a j) (b j) →
      ν.map (fun ω => Z c i j ω t) ∈ sourceMomentClass alpha K) :
    let D := CD*(1+Real.log (sourceGammaScale N J T B p))^(1/alpha)
    2*Real.exp 1*K ≤ D ∧
    ν.real {ω | ∃ c i j t, t ∈ Icc (a j) (b j) ∧ D < ‖Z c i j ω t‖} ≤ p/3 := by
  let D := CD*(1+Real.log (sourceGammaScale N J T B p))^(1/alpha)
  have hc := source_fixed_radius_coefficient_choice alpha K CD halpha hK hCD
    J N T B p hN hT B.coe_nonneg hp hp1
  have hb := source_uniform_radius_bound_le_budget J N alpha K D T B (p/3) hN
    halpha hK hT B.coe_nonneg (by positivity) (by linarith) hc
  exact ⟨hb.1, (source_two_cloud_uniform_radius_tail_le J N alpha K D T B a b
    halpha hK hb.1 hab hbranch ν Z hLip hMarginal).trans hb.2⟩

end PaperFormalization.Manuscript
