import PaperFormalization.Manuscript.SourceScheduledClosureSupport
import PaperFormalization.Manuscript.SourceGammaRateAlgebra

/-! # One source Xi and one epsilon-independent radius

M13t verified implementation. The appendix Xi includes the fixed jump-count
and speed factors. The main-text Xi omits them. They are related explicitly,
not identified. The same CD works for the literal radius choice at every
N,J,T,p; no probability parameter is silently changed in the covariance bound.
-/
open Set
open scoped NNReal
namespace PaperFormalization.Manuscript

noncomputable def sourceAsymptoticXi (N J : Nat) (T p : Real) (B : NNReal) : Real :=
  sourceGammaScale N J T B (3*p/8)

noncomputable def sourceMainXi (N : Nat) (T p : Real) : Real :=
  (N : Real) * (Real.exp 1+T) / p

noncomputable def sourceRateRadius (N J : Nat) (T p alpha CD : Real) (B : NNReal) : Real :=
  CD * (1+Real.log (sourceAsymptoticXi N J T p B))^(1/alpha)

theorem sourceAsymptoticXi_formula (N J : Nat) (T p : Real) (B : NNReal) :
    sourceAsymptoticXi N J T p B =
      8*N*(Real.exp 1+T)*((J : Real)+1)*(1+(B : Real))/p := by
  unfold sourceAsymptoticXi sourceGammaScale
  by_cases hp : p = 0
  · simp [hp]
  · field_simp [hp]
    <;> ring

theorem sourceAsymptoticXi_bounds (N J : Nat) (T p : Real) (B : NNReal)
    (hN : 0 < N) (hT : 0 ≤ T) (hp : 0 < p) (hp1 : p ≤ 1) :
    2 ≤ sourceAsymptoticXi N J T p B ∧ (N : Real) ≤ sourceAsymptoticXi N J T p B := by
  have h := sourceGammaScale_bounds N J T B (3*p/8) hN hT B.coe_nonneg (by positivity) (by linarith)
  exact ⟨h.1,h.2.1⟩

theorem sourceAsymptoticXi_main (N J : Nat) (T p : Real) (B : NNReal) :
    sourceAsymptoticXi N J T p B =
      (8*((J : Real)+1)*(1+(B : Real))) * sourceMainXi N T p := by
  rw [sourceAsymptoticXi_formula]
  unfold sourceMainXi
  ring

/-- Main-text rate constants may absorb ONLY this fixed bounded-count factor. -/
theorem sourceAsymptoticXi_le_main (N J : Nat) (T p L0 : Real) (B : NNReal)
    (hT : 0 ≤ T) (hp : 0 < p) (hJ : (J : Real) ≤ L0) :
    sourceAsymptoticXi N J T p B ≤ (8*(L0+1)*(1+(B : Real))) * sourceMainXi N T p := by
  rw [sourceAsymptoticXi_main]
  apply mul_le_mul_of_nonneg_right _ (by unfold sourceMainXi; positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  linarith

/-- The covariance constructor uses u=p/(8(J+1)), not its sharper u/4 failure
probability. Its own sampling scale N/u is dominated by this same Xi. -/
theorem sourceAsymptoticXi_covariance_scale (N J : Nat) (T p : Real) (B : NNReal)
    (hT : 0 ≤ T) (hp : 0 < p) :
    (N : Real)/(p/(8*((J : Real)+1))) ≤ sourceAsymptoticXi N J T p B := by
  have hj : 0 < (J : Real)+1 := by positivity
  have he : 1 ≤ Real.exp 1+T := by linarith [Real.add_one_le_exp (1 : Real)]
  have hb : 1 ≤ 1+(B : Real) := by linarith [B.coe_nonneg]
  have hprod := mul_le_mul he hb (by norm_num : (0 : Real) ≤ 1) (by positivity)
  rw [sourceAsymptoticXi_formula]
  have hident : (N : Real)/(p/(8*((J : Real)+1))) = 8*N*((J : Real)+1)/p := by field_simp
  rw [hident]
  have hm := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 8*(N : Real)*((J : Real)+1)/p by positivity)
  calc
    8*(N : Real)*((J : Real)+1)/p ≤
        (8*N*((J : Real)+1)/p)*((Real.exp 1+T)*(1+(B : Real))) := by
      simpa only [one_mul,mul_one] using hm
    _ = _ := by ring

theorem sourceRateRadius_one_le (N J : Nat) (T p alpha CD : Real) (B : NNReal)
    (hN : 0 < N) (hT : 0 ≤ T) (hp : 0 < p) (hp1 : p ≤ 1)
    (ha : 0 < alpha) (hCD : 1 ≤ CD) : 1 ≤ sourceRateRadius N J T p alpha CD B := by
  have hx := (sourceAsymptoticXi_bounds N J T p B hN hT hp hp1).1
  have hl : 1 ≤ 1+Real.log (sourceAsymptoticXi N J T p B) := by
    linarith [Real.log_nonneg (show 1 ≤ sourceAsymptoticXi N J T p B by linarith)]
  have hr := Real.one_le_rpow hl (show 0 ≤ 1/alpha by positivity)
  unfold sourceRateRadius
  nlinarith

noncomputable def sourceRadiusArgumentFactor (K0 : Real) : Real :=
  4 + 2/(Real.exp 1*K0)

noncomputable def sourceRadiusCoefficientMinimum (alpha K0 : Real) : Real :=
  2*Real.exp 1*K0*(1+Real.log (sourceRadiusArgumentFactor K0))^(1/alpha)

/-- Explicit domination of the ORIGINAL radius grid count, uniform in J,T,B. -/
theorem source_radius_argument_bound (N J : Nat) (T p K0 : Real) (B : NNReal)
    (hN : 0 < N) (hT : 0 ≤ T) (hp : 0 < p) (hp1 : p ≤ 1) (hK0 : 0 < K0) :
    let arg := 2*N*(2*((J : Real)+1)+(B : Real)*T/(Real.exp 1*K0))/(p/8)
    1 ≤ arg ∧ arg ≤ sourceRadiusArgumentFactor K0 * sourceAsymptoticXi N J T p B := by
  let u := (Real.exp 1+T)*((J : Real)+1)*(1+(B : Real))
  have hn : (1 : Real) ≤ N := by exact_mod_cast hN
  have hj : 1 ≤ (J : Real)+1 := by linarith [Nat.cast_nonneg (α := Real) J]
  have he : 1 ≤ Real.exp 1+T := by linarith [Real.add_one_le_exp (1 : Real)]
  have hb : 1 ≤ 1+(B : Real) := by linarith [B.coe_nonneg]
  have hden : 0 < Real.exp 1*K0 := by positivity
  have hu1 : (J : Real)+1 ≤ u := by
    dsimp [u]
    exact (le_mul_of_one_le_left (by positivity) he).trans
      (le_mul_of_one_le_right (by positivity) hb)
  have hu2 : (B : Real)*T ≤ u := by
    have ht1 : T ≤ Real.exp 1+T := by linarith [Real.exp_pos (1 : Real)]
    have hm : T*(B : Real) ≤ (Real.exp 1+T)*(1+(B : Real)) :=
      mul_le_mul ht1 (by linarith) B.coe_nonneg (by positivity)
    have hm2 := le_mul_of_one_le_right (show 0 ≤ (Real.exp 1+T)*(1+(B : Real)) by positivity) hj
    dsimp [u]
    nlinarith
  have hH : 1 ≤ 8*(N : Real)/p := (le_div_iff₀ hp).mpr (by nlinarith)
  have harg : 2*(N : Real)*(2*((J : Real)+1)+(B : Real)*T/(Real.exp 1*K0))/(p/8) =
      (8*N/p)*(4*((J : Real)+1)+(2/(Real.exp 1*K0))*((B : Real)*T)) := by
    field_simp [hp.ne',hden.ne']
    <;> ring
  have hXi : sourceAsymptoticXi N J T p B = (8*N/p)*u := by
    rw [sourceAsymptoticXi_formula]; dsimp [u]; ring
  rw [harg,hXi]
  have hbr : 1 ≤ 4*((J : Real)+1)+(2/(Real.exp 1*K0))*((B : Real)*T) := by
    have hh : 0 ≤ (2/(Real.exp 1*K0))*((B : Real)*T) := by positivity
    linarith
  constructor
  · simpa only [one_mul] using mul_le_mul hH hbr (by norm_num : (0 : Real) ≤ 1) (by positivity)
  · have hbnd : 4*((J : Real)+1)+(2/(Real.exp 1*K0))*((B : Real)*T) ≤
        sourceRadiusArgumentFactor K0*u := by
      unfold sourceRadiusArgumentFactor
      nlinarith [mul_le_mul_of_nonneg_left hu2 (div_pos (by norm_num : (0 : Real) < 2) hden).le]
    have hh := mul_le_mul_of_nonneg_left hbnd (show 0 ≤ 8*(N : Real)/p by positivity)
    nlinarith

/-- One sufficiently large CD supplies the precise finite-schedule radius
inequality for EVERY later choice of epsilon. -/
theorem sourceRateRadius_admissible (N J : Nat) (T p alpha K0 CD : Real) (B : NNReal)
    (hN : 0 < N) (hT : 0 ≤ T) (hp : 0 < p) (hp1 : p ≤ 1) (ha : 0 < alpha) (hK0 : 0 < K0)
    (hCD : sourceRadiusCoefficientMinimum alpha K0 ≤ CD) :
    2*Real.exp 1*K0*
      (1+Real.log (2*N*(2*((J : Real)+1)+(B : Real)*T/(Real.exp 1*K0))/(p/8)))^(1/alpha) ≤
        sourceRateRadius N J T p alpha CD B := by
  let x := sourceAsymptoticXi N J T p B
  let C := sourceRadiusArgumentFactor K0
  let arg := 2*N*(2*((J : Real)+1)+(B : Real)*T/(Real.exp 1*K0))/(p/8)
  have hC : 1 ≤ C := by
    dsimp [C,sourceRadiusArgumentFactor]
    have hh : 0 ≤ 2/(Real.exp 1*K0) := by positivity
    linarith
  have hx : 2 ≤ x := (sourceAsymptoticXi_bounds N J T p B hN hT hp hp1).1
  have ha' := source_radius_argument_bound N J T p K0 B hN hT hp hp1 hK0
  have hlog : Real.log arg ≤ Real.log C+Real.log x := by
    rw [← Real.log_mul (by linarith : C ≠ 0) (by linarith : x ≠ 0)]
    exact Real.log_le_log (by dsimp [arg]; positivity) ha'.2
  have hLc : 0 ≤ Real.log C := Real.log_nonneg hC
  have hLx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hbase : 1+Real.log arg ≤ (1+Real.log C)*(1+Real.log x) := by
    nlinarith [mul_nonneg hLc hLx]
  have hlogarg : 0 ≤ Real.log arg := Real.log_nonneg (show 1 ≤ arg from ha'.1)
  have hpow := Real.rpow_le_rpow (by linarith : 0 ≤ 1+Real.log arg) hbase (show 0 ≤ 1/alpha by positivity)
  rw [Real.mul_rpow (by positivity : 0 ≤ 1+Real.log C) (by positivity : 0 ≤ 1+Real.log x)] at hpow
  have hb := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 2*Real.exp 1*K0 by positivity)
  have hc := mul_le_mul_of_nonneg_right hCD (show 0 ≤ (1+Real.log x)^(1/alpha) by positivity)
  change 2*Real.exp 1*K0*(1+Real.log arg)^(1/alpha) ≤ CD*(1+Real.log x)^(1/alpha)
  apply hb.trans
  simpa only [sourceRadiusCoefficientMinimum,C,mul_assoc] using hc

/-- Conversion used only for the previously verified nuclear-envelope API. -/
theorem source_one_add_log_rpow_le (x s : Real) (hx : 2 ≤ x) (hs : 0 ≤ s) :
    (1+Real.log x)^s ≤ (1+1/Real.log 2)^s*(Real.log x)^s := by
  have hl2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hl : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlx : 0 ≤ Real.log x := hl2.le.trans hl
  have hb : 1+Real.log x ≤ (1+1/Real.log 2)*Real.log x := by
    have hh : 1 ≤ Real.log x / Real.log 2 :=
      (le_div_iff₀ hl2).mpr (by simpa using hl)
    calc
      1+Real.log x ≤ Real.log x/Real.log 2+Real.log x := add_le_add hh le_rfl
      _ = _ := by ring
  have hp := Real.rpow_le_rpow (by positivity) hb hs
  simpa only [Real.mul_rpow (show 0 ≤ 1+1/Real.log 2 by positivity) (show 0 ≤ Real.log x by linarith)] using hp

end PaperFormalization.Manuscript
