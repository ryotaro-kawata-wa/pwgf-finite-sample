import PaperFormalization.Manuscript.SourceGammaSubpolynomial

/-! # Exact source radius substitution and clipping-bias decay

This is the deterministic substitution for D=C_D(1+log Xi)^(1/alpha).
The prefactor in the final Xi^-2 bound remains visible; no large-N claim
is used before a quantitative threshold is supplied.
-/
namespace PaperFormalization.Manuscript

/-- The literal radius has exactly the required linear logarithm after
taking its alpha power, including the original fixed K0 normalization. -/
theorem source_clipping_radius_power (CD K0 alpha x : ℝ)
    (hCD : 0 ≤ CD) (hK0 : 0 < K0) (halpha : 0 < alpha) (hx : 1 ≤ x) :
    ((CD * (1+Real.log x)^(1/alpha))/K0)^alpha =
      (CD/K0)^alpha * (1+Real.log x) := by
  have hbase : 0 ≤ 1+Real.log x := by linarith [Real.log_nonneg hx]
  rw [show CD * (1+Real.log x)^(1/alpha)/K0 =
    (CD/K0) * (1+Real.log x)^(1/alpha) by ring,
    Real.mul_rpow (div_nonneg hCD hK0.le) (Real.rpow_nonneg hbase _),
    ← Real.rpow_mul hbase, one_div_mul_cancel halpha.ne', Real.rpow_one]

/-- A fixed source radius coefficient simultaneously exceeds one and makes
the clipping exponent at least cM/2+3. It is chosen before Xi,N,T,p. -/
theorem exists_source_clipping_radius_coefficient (c0 K0 alpha cM : ℝ)
    (hc0 : 0 < c0) (hK0 : 0 < K0) (halpha : 0 < alpha) (hcM : 0 ≤ cM) :
    ∃ CD : ℝ, 1 ≤ CD ∧ (c0/2)*(CD/K0)^alpha ≥ cM/2+3 := by
  let a := 2*(cM/2+3)/c0
  have ha : 0 ≤ a := by dsimp [a]; positivity
  let CD := 1+K0*a^(1/alpha)
  have hCD : 1 ≤ CD := by
    dsimp [CD]
    linarith [mul_nonneg hK0.le (Real.rpow_nonneg ha (1/alpha))]
  refine ⟨CD,hCD,?_⟩
  have hratio : a^(1/alpha) ≤ CD/K0 := by
    apply (le_div_iff₀ hK0).mpr
    dsimp [CD]
    nlinarith
  have hrpow : a ≤ (CD/K0)^alpha := by
    calc
      _ = (a^(1/alpha))^alpha := by rw [← Real.rpow_mul ha, one_div_mul_cancel halpha.ne', Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg ha _) hratio halpha.le
  have hm := mul_le_mul_of_nonneg_left hrpow (show 0 ≤ c0/2 by positivity)
  have he : (c0/2)*a = cM/2+3 := by dsimp [a]; field_simp
  linarith

/-- The exact original exponential clipping term decays at least as Xi^-2
once S<=CS Xi and Mpop<=CM Xi^cM, with the prefactor explicit. -/
theorem source_clipping_bias_le_inverse_square
    (S Mpop CS CM cM c0 CD K0 alpha x : ℝ)
    (hCS : 0 ≤ CS) (hCM : 0 ≤ CM) (hcM : 0 ≤ cM)
    (hCD : 0 ≤ CD) (hK0 : 0 < K0) (halpha : 0 < alpha) (hx : 1 ≤ x)
    (hS : S ≤ CS*x) (hM : Mpop ≤ CM*x^cM)
    (hdecay : cM/2+3 ≤ (c0/2)*(CD/K0)^alpha) :
    2*S*Real.sqrt Mpop * Real.exp (-(c0*((CD*(1+Real.log x)^(1/alpha))/K0)^alpha)/2) ≤
      (2*CS*Real.sqrt CM)*x^(-2 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  let b := (c0/2)*(CD/K0)^alpha
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hroot : Real.sqrt Mpop ≤ Real.sqrt CM * x^(cM/2) := by
    calc
      _ ≤ Real.sqrt (CM*x^cM) := Real.sqrt_le_sqrt hM
      _ = _ := by
        rw [Real.sqrt_mul hCM, Real.sqrt_eq_rpow (x^cM), ← Real.rpow_mul hx0.le]
        congr 2
        ring
  have hexp : Real.exp (-(c0*((CD*(1+Real.log x)^(1/alpha))/K0)^alpha)/2) ≤
      x^(-(cM/2+3)) := by
    rw [source_clipping_radius_power CD K0 alpha x hCD hK0 halpha hx,
      Real.rpow_def_of_pos hx0]
    apply Real.exp_le_exp.mpr
    have hmult := mul_le_mul_of_nonneg_right hdecay hl
    dsimp [b] at hb
    nlinarith
  calc
    _ ≤ (2*(CS*x)*(Real.sqrt CM*x^(cM/2))) * x^(-(cM/2+3)) :=
      mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hS (by norm_num)) hroot
        (Real.sqrt_nonneg _) (by positivity)) hexp (Real.exp_pos _).le (by positivity)
    _ = (2*CS*Real.sqrt CM) * (x^(1 : ℝ)*x^(cM/2)*x^(-(cM/2+3))) := by rw [Real.rpow_one]; ring
    _ = _ := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
      congr 2
      ring

/-- The explicit inverse-square prefactor yields the required N^-1 bias
once N exceeds it and Xi>=N. This avoids hiding the uniform threshold. -/
theorem source_inverse_square_le_inverse_sample (N : ℕ) (x C : ℝ)
    (hN : 0 < N) (hCN : C ≤ N) (hNx : (N : ℝ) ≤ x) :
    C*x^(-2 : ℝ) ≤ (N : ℝ)⁻¹ := by
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hx0 : 0 < x := hN0.trans_le hNx
  have hp : x^(-2 : ℝ) ≤ (N : ℝ)^(-2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hN0 hNx (by norm_num)
  calc
    _ ≤ (N : ℝ)*(N : ℝ)^(-2 : ℝ) := mul_le_mul hCN hp (by positivity) hN0.le
    _ = _ := by
      rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hN0.le, Real.rpow_two]
      field_simp


/-- Radius enlargement can be requested in advance, so one CD serves both
sample localization and population clipping. Constants still precede Xi. -/
theorem exists_source_clipping_radius_coefficient_above (c0 K0 alpha cM CDmin : ℝ)
    (hc0 : 0 < c0) (hK0 : 0 < K0) (halpha : 0 < alpha) (hcM : 0 ≤ cM) :
    ∃ CD : ℝ, CDmin ≤ CD ∧ 1 ≤ CD ∧ (c0/2)*(CD/K0)^alpha ≥ cM/2+3 := by
  obtain ⟨D,hD,hd⟩ := exists_source_clipping_radius_coefficient c0 K0 alpha cM hc0 hK0 halpha hcM
  refine ⟨max CDmin D,le_max_left _ _,hD.trans (le_max_right _ _),?_⟩
  apply hd.trans
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
    (div_nonneg (by linarith) hK0.le)
    (div_le_div_of_nonneg_right (le_max_right _ _) hK0.le) halpha.le) (by positivity)
end PaperFormalization.Manuscript
