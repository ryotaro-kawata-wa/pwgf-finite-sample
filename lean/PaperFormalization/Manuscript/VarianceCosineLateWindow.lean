import PaperFormalization.Manuscript.VarianceCosineRateAlgebra

/-! # Explicit waiting window and the unchanged probability budget
M13v VERIFIED UNIT (full example application remains open). The waiting window cancels the full inverse escape radius.
Choosing v=N^(-1/4), rho=d*N^(-1/16) gives the manuscript's late powers.
No event is conditioned on; the last lemma is just a union bound.
-/
open Set MeasureTheory
namespace PaperFormalization.Manuscript

/-- Horizon-independent C response and O(v) one-jump response. -/
theorem varianceCosine_responses_after_wait (a beta tau eta T Z rho v t : Real)
    (ha : 0 < a) (hb : 0 < beta) (htau : 0 <= tau) (heta : 0 <= eta)
    (hr : 0 < rho) (hr1 : rho <= 1) (hv : 0 < v) (hv1 : v <= 1)
    (hland : varianceCosineEscapeLanding rho (varianceCosinePostMeanY a beta eta Z))
    (ht : t ∈ Icc (varianceCosineRecoveryTime beta tau rho) T)
    (hwait : varianceCosineRecoveryTime beta tau rho+
      Real.log ((rho*v)⁻¹)/varianceCosineRecoveryRate a beta <= t) :
    let b := varianceCosineCurvatureScale beta
    let lam := varianceCosineRecoveryRate a beta
    let k := varianceCosineRightCurvature a beta tau eta T Z
    recoveryContinuousResponse k t <= 2*Real.exp (b*tau)/b+lam⁻¹ ∧
    recoveryJumpResponse k tau eta t <= (2*eta*Real.exp (b*tau))*v := by
  let b := varianceCosineCurvatureScale beta
  let lam := varianceCosineRecoveryRate a beta
  let r := varianceCosineRecoveryTime beta tau rho
  have hb' : 0 < b := varianceCosineCurvatureScale_pos hb
  have hlate := varianceCosine_responses_late a beta tau eta T Z rho t ha hb htau heta hr hr1 hland ht
  have hw := recovery_wait_bound lam r rho v t (varianceCosineRecoveryRate_pos ha hb) hr hv hwait
  constructor
  . calc
      _ <= (2*Real.exp (b*tau)/(rho*b))*Real.exp (-lam*(t-r))+lam⁻¹ := hlate.1
      _ <= (2*Real.exp (b*tau)/(rho*b))*(rho*v)+lam⁻¹ := by gcongr
      _ = (2*Real.exp (b*tau)/b)*v+lam⁻¹ := by field_simp <;> ring
      _ <= _ := add_le_add (mul_le_of_le_one_right (by positivity) hv1) le_rfl
  . calc
      _ <= (2*eta*Real.exp (b*tau)/rho)*Real.exp (-lam*(t-r)) := hlate.2
      _ <= (2*eta*Real.exp (b*tau)/rho)*(rho*v) := by gcongr
      _ = _ := by dsimp only [b]; field_simp <;> ring

/-- The scalar energy estimate has the matching squared decay. -/
theorem varianceCosine_energy_after_wait (lam r rho v t E E0 : Real)
    (hl : 0 < lam) (hr : 0 < rho) (hr1 : rho <= 1) (hv : 0 < v) (hE0 : 0 <= E0)
    (hwait : r+Real.log ((rho*v)⁻¹)/lam <= t)
    (hE : E <= E0*Real.exp (-2*lam*(t-r))) : E <= E0*v^2 := by
  have hw := recovery_wait_bound lam r rho v t hl hr hv hwait
  have hvb : rho*v <= v := mul_le_of_le_one_left hv.le hr1
  have hsq := pow_le_pow_left₀ (Real.exp_pos (-lam*(t-r))).le (hw.trans hvb) 2
  have he : Real.exp (-2*lam*(t-r)) = (Real.exp (-lam*(t-r)))^2 := by
    rw [show -2*lam*(t-r)=(-lam*(t-r))+(-lam*(t-r)) by ring,Real.exp_add,pow_two]
  rw [he] at hE
  exact hE.trans (mul_le_mul_of_nonneg_left hsq hE0)

/-- Exact logarithmic window when rho=d*N^(-1/16), v=N^(-1/4).
This exposes the fixed additive constant and coefficient of log N. -/
theorem varianceCosine_wait_logarithmic (n d b lam tau : Real)
    (hn : 0 < n) (hd : 0 < d) (hb : b ≠ 0) (hl : lam ≠ 0) :
    tau+Real.log (2/(d*n^(-(1/16:Real))))/b+
      Real.log (((d*n^(-(1/16:Real)))*n^(-(1/4:Real)))⁻¹)/lam =
    tau+Real.log (2/d)/b+Real.log (d⁻¹)/lam+
      (1/(16*b)+5/(16*lam))*Real.log n := by
  have hn1 : n^(-(1/16:Real)) ≠ 0 := (Real.rpow_pos_of_pos hn _).ne'
  have hn4 : n^(-(1/4:Real)) ≠ 0 := (Real.rpow_pos_of_pos hn _).ne'
  rw [Real.log_div (by norm_num) (mul_ne_zero hd.ne' hn1),
    Real.log_inv,Real.log_mul (mul_ne_zero hd.ne' hn1) hn4,
    Real.log_mul hd.ne' hn1,Real.log_rpow hn,Real.log_rpow hn,
    Real.log_div (by norm_num) hd.ne',Real.log_inv]
  field_simp <;> ring

/-- The sample event and population escape event need not be independent. -/
theorem varianceCosine_same_event_budget {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (A E : Set Omega) (p : Real) (hp : 0 <= p)
    (hA : P Aᶜ <= ENNReal.ofReal (p/2)) (hE : P Eᶜ <= ENNReal.ofReal (p/2)) :
    P (A ∩ E)ᶜ <= ENNReal.ofReal p := by
  rw [compl_inter]
  calc
    _ <= P Aᶜ+P Eᶜ := measure_union_le _ _
    _ <= ENNReal.ofReal (p/2)+ENNReal.ofReal (p/2) := add_le_add hA hE
    _ = ENNReal.ofReal p := by rw [<- ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
end PaperFormalization.Manuscript
