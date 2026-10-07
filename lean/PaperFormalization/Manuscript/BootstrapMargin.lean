import PaperFormalization.Manuscript.ExitAttainment
import PaperFormalization.Continuous.ForcingResponse

/-! # The exact source bootstrap margin and zero-envelope alternative

The positive-envelope case uses the source smallness condition
`T * (delta + c * (2 * J * Bstar)) <= 1/4` without strengthening it.
The stopped forcing envelope remains an explicit premise: this module does
not claim to derive particle drift, concentration, or that envelope estimate.
-/

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace PaperFormalization.Manuscript

open Continuous

/-- A rational upper bound for the source's exponential constant. -/
theorem exp_quarter_lt_three_halves : Real.exp (1 / 4 : ℝ) < 3 / 2 := by
  have h := Real.exp_bound_div_one_sub_of_interval'
    (x := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
  norm_num at h
  linarith

/-- The candidate-exit multiplier is strictly below one. -/
theorem exp_quarter_half_lt_one : Real.exp (1 / 4 : ℝ) / 2 < 1 := by
  have h := exp_quarter_lt_three_halves
  linarith

/-- Nonnegative jump errors make the full amplification at least one. -/
theorem one_le_jump_amplification {ι : Type*} (S : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) : 1 ≤ ∏ i ∈ S, (1 + a i) := by
  exact Finset.one_le_prod fun i hi => by linarith [ha i hi]

/-- Every selected jump subproduct is bounded by the full amplification. -/
theorem jump_subproduct_le_amplification {ι : Type*} (S U : Finset ι) (a : ι → ℝ)
    (hsub : S ⊆ U) (ha : ∀ i ∈ U, 0 ≤ a i) :
    ∏ i ∈ S, (1 + a i) ≤ ∏ i ∈ U, (1 + a i) := by
  apply Finset.prod_le_prod_of_subset_of_one_le hsub
  · intro i hi
    linarith [ha i (hsub hi)]
  · intro i hi _
    linarith [ha i hi]

/-- The exact source smallness event yields its explicit strict candidate margin. -/
theorem stopped_envelope_le_bootstrap_margin (J Bstar Bt T c delta : ℝ)
    (hJ : 0 < J) (hB : 0 < Bstar) (hBt : Bt ≤ Bstar)
    (hsmall : T * (delta + c * (2 * J * Bstar)) ≤ 1 / 4) :
    J * Real.exp (T * (c * (2 * J * Bstar) + delta)) * Bt ≤
      (Real.exp (1 / 4) / 2) * (2 * J * Bstar) := by
  have hexp : Real.exp (T * (c * (2 * J * Bstar) + delta)) ≤ Real.exp (1 / 4) := by
    apply Real.exp_le_exp.mpr
    simpa only [add_comm delta] using hsmall
  calc
    J * Real.exp (T * (c * (2 * J * Bstar) + delta)) * Bt ≤
        J * Real.exp (T * (c * (2 * J * Bstar) + delta)) * Bstar := by
      gcongr
    _ ≤ J * Real.exp (1 / 4) * Bstar := by gcongr
    _ = (Real.exp (1 / 4) / 2) * (2 * J * Bstar) := by ring

/-- In the positive-envelope case every stopped envelope is strictly within `R=2JB*`. -/
theorem stopped_envelope_lt_bootstrap_radius (J Bstar Bt T c delta : ℝ)
    (hJ : 0 < J) (hB : 0 < Bstar) (hBt : Bt ≤ Bstar)
    (hsmall : T * (delta + c * (2 * J * Bstar)) ≤ 1 / 4) :
    J * Real.exp (T * (c * (2 * J * Bstar) + delta)) * Bt < 2 * J * Bstar := by
  have hR : 0 < 2 * J * Bstar := by positivity
  exact (stopped_envelope_le_bootstrap_margin J Bstar Bt T c delta hJ hB hBt hsmall).trans_lt
    (by nlinarith [mul_lt_mul_of_pos_right exp_quarter_half_lt_one hR])

/-- The source's stopped forcing estimate and exact smallness event give the global bound.
Right continuity is only from the right within the finite horizon. -/
theorem tracking_bound_of_smallness (r Benv : ℝ → ℝ) (J Bstar T c delta : ℝ)
    (hJ : 0 < J) (hB : 0 < Bstar)
    (hsmall : T * (delta + c * (2 * J * Bstar)) ≤ 1 / 4)
    (hBenv : ∀ t ∈ Icc 0 T, 0 ≤ Benv t ∧ Benv t ≤ Bstar)
    (hr : ∀ t ∈ Icc 0 T, ContinuousWithinAt r (Icc t T) t)
    (hstop : ∀ t ∈ Icc 0 T,
      (t : WithTop ℝ) ≤ exitTime r (2 * J * Bstar) T →
      r t ≤ J * Real.exp (T * (c * (2 * J * Bstar) + delta)) * Benv t) :
    exitTime r (2 * J * Bstar) T = ⊤ ∧
      ∀ t ∈ Icc 0 T, r t ≤ Real.exp (1 / 4) * J * Benv t := by
  have hglobal := bound_on_horizon_of_strict_stopped_envelope r
    (fun t => J * Real.exp (T * (c * (2 * J * Bstar) + delta)) * Benv t)
    (2 * J * Bstar) T hr hstop (fun t ht =>
      stopped_envelope_lt_bootstrap_radius J Bstar (Benv t) T c delta
        hJ hB (hBenv t ht).2 hsmall)
  refine ⟨hglobal.1, ?_⟩
  intro t ht
  have hexp : Real.exp (T * (c * (2 * J * Bstar) + delta)) ≤ Real.exp (1 / 4) := by
    apply Real.exp_le_exp.mpr
    simpa only [add_comm delta] using hsmall
  calc
    r t ≤ J * Real.exp (T * (c * (2 * J * Bstar) + delta)) * Benv t := hglobal.2 t ht
    _ ≤ J * Real.exp (1 / 4) * Benv t := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hJ.le) (hBenv t ht).1
    _ = Real.exp (1 / 4) * J * Benv t := by ring

/-- The source's strict `3/2` improvement is valid exactly when the envelope is positive. -/
theorem tracking_strict_three_halves (r J B : ℝ) (hJ : 0 < J) (hB : 0 < B)
    (hr : r ≤ Real.exp (1 / 4) * J * B) : r < (3 / 2) * J * B := by
  exact hr.trans_lt (mul_lt_mul_of_pos_right
    (mul_lt_mul_of_pos_right exp_quarter_lt_three_halves hJ) hB)

/-- The same global estimate forces zero discrepancy at a zero of the envelope. -/
theorem tracking_eq_zero_at_zero_envelope (r J B : ℝ) (hr0 : 0 ≤ r)
    (hr : r ≤ Real.exp (1 / 4) * J * B) (hB : B = 0) : r = 0 := by
  subst B
  simp only [mul_zero] at hr
  exact le_antisymm hr hr0

/-- The continuous curvature response is strictly positive over a positive horizon. -/
theorem continuous_response_pos (kappa : ℝ → ℝ) (T : ℝ) (hT : 0 < T)
    (hkappa : IntervalIntegrable kappa volume 0 T) :
    0 < ∫ s in (0 : ℝ)..T, propagator kappa T s := by
  have hc : ContinuousOn (propagator kappa T) (Icc 0 T) := by
    simpa only [uIcc_of_le hT.le] using
      (propagator_terminal_ac kappa 0 T hkappa).continuousOn
  apply intervalIntegral.integral_pos hT hc
  · intro s _
    exact propagator_nonneg kappa T s
  · exact ⟨T, ⟨hT.le, le_rfl⟩, propagator_pos kappa T T⟩

/-- A zero forcing envelope at the positive horizon forces both delta and every
nonnegative additive jump forcing to vanish; all full-schedule jumps appear here. -/
theorem zero_forcing_of_zero_envelope (kappa : ℝ → ℝ) (tau b : ℕ → ℝ)
    (L : ℕ) (T delta : ℝ) (hT : 0 < T) (hdelta : 0 ≤ delta)
    (hkappa : IntervalIntegrable kappa volume 0 T)
    (hb : ∀ i < L, 0 ≤ b i)
    (hzero : delta * (∫ s in (0 : ℝ)..T, propagator kappa T s) +
      ∑ i ∈ Finset.range L, propagator kappa T (tau (i + 1)) * b i ≤ 0) :
    delta = 0 ∧ ∀ i < L, b i = 0 := by
  have hC := continuous_response_pos kappa T hT hkappa
  have hsum : 0 ≤ ∑ i ∈ Finset.range L, propagator kappa T (tau (i + 1)) * b i := by
    exact Finset.sum_nonneg fun i hi => mul_nonneg (propagator_nonneg _ _ _) (hb i (Finset.mem_range.mp hi))
  have hdelta0 : delta = 0 := by nlinarith
  refine ⟨hdelta0, ?_⟩
  intro i hi
  have hterm : propagator kappa T (tau (i + 1)) * b i ≤
      ∑ j ∈ Finset.range L, propagator kappa T (tau (j + 1)) * b j := by
    exact Finset.single_le_sum
      (fun j hj => mul_nonneg (propagator_nonneg kappa T (tau (j + 1)))
        (hb j (Finset.mem_range.mp hj)))
      (Finset.mem_range.mpr hi)
  have hpos := propagator_pos kappa T (tau (i + 1))
  have hbi := hb i hi
  rw [hdelta0] at hzero
  nlinarith

end PaperFormalization.Manuscript
