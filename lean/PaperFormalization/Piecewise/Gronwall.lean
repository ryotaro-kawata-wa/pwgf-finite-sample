import PaperFormalization.Piecewise.KernelPartition

/-! # Finite piecewise Gronwall comparison with forced multiplicative jumps

The result is proved from absolutely continuous branch trajectories, explicit
coefficient/forcing integrability, almost-everywhere differential inequalities,
and nonnegative jump multipliers. Pre-jump traces are the branch endpoints;
post-jump values are separate inputs connected by the jump inequalities.

This file does not construct those inputs from the particle model or prove the
stopping-radius/first-exit argument. Those are separate manuscript obligations.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PaperFormalization.Piecewise

open Continuous

/-- The finite analytic comparison in single-integral and discrete-jump form. -/
theorem finite_piecewise_comparison (tau : ℕ → ℝ) (r : ℕ → ℝ → ℝ)
    (post J b : ℕ → ℝ) (beta f q : ℝ → ℝ) (n : ℕ) (t : ℝ)
    (htime : ∀ k < n, tau k ≤ tau (k + 1))
    (hr : ∀ k < n, AbsolutelyContinuousOnInterval (r k) (tau k) (tau (k + 1)))
    (hbeta : IntervalIntegrable beta volume (tau 0) t)
    (hf : IntervalIntegrable f volume (tau 0) t)
    (hineq : ∀ k < n, ∀ᵐ u ∂volume.restrict (Ioo (tau k) (tau (k + 1))),
      deriv (r k) u ≤ -beta u * r k u + f u)
    (hstart : ∀ k < n, r k (tau k) = post k)
    (hJ : ∀ k < n, 0 ≤ J k)
    (hjump : ∀ k < n, post (k + 1) ≤ J k * r k (tau (k + 1)) + b k)
    (ht : tau n ≤ t) (hq : AbsolutelyContinuousOnInterval q (tau n) t)
    (hineq_final : ∀ᵐ u ∂volume.restrict (Ioo (tau n) t), deriv q u ≤ -beta u * q u + f u)
    (hqstart : q (tau n) = post n) :
    q t ≤ propagator beta t (tau 0) * (∏ k ∈ Finset.range n, J k) * post 0 +
      (∫ v in tau 0..t, propagator beta t v * jumpWeight tau J n v * f v) +
      ∑ i ∈ Finset.range n, propagator beta t (tau (i + 1)) *
        (∏ j ∈ Finset.Ico (i + 1) n, J j) * b i := by
  rw [← observationBound_eq_integral_form tau J b beta f (post 0) n t htime ht hbeta hf]
  have hb : ∀ k < n, IntervalIntegrable beta volume (tau k) (tau (k + 1)) := by
    intro k hk
    exact hbeta.mono_set (uIcc_subset_uIcc
      (time_mem_observation_interval tau n t htime ht k hk.le)
      (time_mem_observation_interval tau n t htime ht (k + 1) (Nat.succ_le_of_lt hk)))
  have hforcing : ∀ k < n, IntervalIntegrable f volume (tau k) (tau (k + 1)) := by
    intro k hk
    exact hf.mono_set (uIcc_subset_uIcc
      (time_mem_observation_interval tau n t htime ht k hk.le)
      (time_mem_observation_interval tau n t htime ht (k + 1) (Nat.succ_le_of_lt hk)))
  have hlast := time_mem_observation_interval tau n t htime ht n (le_refl n)
  exact finite_observation_bound tau r post J b beta f q n t htime hr hb hforcing hineq
    hstart hJ hjump ht hq (hbeta.mono_set (uIcc_subset_uIcc_right hlast))
    (hf.mono_set (uIcc_subset_uIcc_right hlast)) hineq_final hqstart

/-- With zero initial discrepancy, the bound contains only continuous and jump forcing. -/
theorem finite_piecewise_gronwall (tau : ℕ → ℝ) (r : ℕ → ℝ → ℝ)
    (post J b : ℕ → ℝ) (beta f q : ℝ → ℝ) (n : ℕ) (t : ℝ)
    (htime : ∀ k < n, tau k ≤ tau (k + 1))
    (hr : ∀ k < n, AbsolutelyContinuousOnInterval (r k) (tau k) (tau (k + 1)))
    (hbeta : IntervalIntegrable beta volume (tau 0) t)
    (hf : IntervalIntegrable f volume (tau 0) t)
    (hineq : ∀ k < n, ∀ᵐ u ∂volume.restrict (Ioo (tau k) (tau (k + 1))),
      deriv (r k) u ≤ -beta u * r k u + f u)
    (hstart : ∀ k < n, r k (tau k) = post k)
    (hJ : ∀ k < n, 0 ≤ J k)
    (hjump : ∀ k < n, post (k + 1) ≤ J k * r k (tau (k + 1)) + b k)
    (ht : tau n ≤ t) (hq : AbsolutelyContinuousOnInterval q (tau n) t)
    (hineq_final : ∀ᵐ u ∂volume.restrict (Ioo (tau n) t), deriv q u ≤ -beta u * q u + f u)
    (hqstart : q (tau n) = post n)
    (hzero : post 0 = 0) :
    q t ≤ (∫ v in tau 0..t, propagator beta t v * jumpWeight tau J n v * f v) +
      ∑ i ∈ Finset.range n, propagator beta t (tau (i + 1)) *
        (∏ j ∈ Finset.Ico (i + 1) n, J j) * b i := by
  simpa only [hzero, mul_zero, zero_add] using
    finite_piecewise_comparison tau r post J b beta f q n t htime hr hbeta hf hineq
      hstart hJ hjump ht hq hineq_final hqstart

/-- For a strict schedule, both continuous and discrete forcing use exactly
 the time-filtered product of subsequent jump factors. -/
theorem finite_piecewise_gronwall_strict_schedule (tau : ℕ → ℝ) (r : ℕ → ℝ → ℝ)
    (post J b : ℕ → ℝ) (beta f q : ℝ → ℝ) (n : ℕ) (t : ℝ)
    (htime : ∀ k < n, tau k < tau (k + 1))
    (hr : ∀ k < n, AbsolutelyContinuousOnInterval (r k) (tau k) (tau (k + 1)))
    (hbeta : IntervalIntegrable beta volume (tau 0) t)
    (hf : IntervalIntegrable f volume (tau 0) t)
    (hineq : ∀ k < n, ∀ᵐ u ∂volume.restrict (Ioo (tau k) (tau (k + 1))),
      deriv (r k) u ≤ -beta u * r k u + f u)
    (hstart : ∀ k < n, r k (tau k) = post k)
    (hJ : ∀ k < n, 0 ≤ J k)
    (hjump : ∀ k < n, post (k + 1) ≤ J k * r k (tau (k + 1)) + b k)
    (ht : tau n ≤ t) (hq : AbsolutelyContinuousOnInterval q (tau n) t)
    (hineq_final : ∀ᵐ u ∂volume.restrict (Ioo (tau n) t), deriv q u ≤ -beta u * q u + f u)
    (hqstart : q (tau n) = post n) (hzero : post 0 = 0) :
    q t ≤ (∫ v in tau 0..t, propagator beta t v * jumpWeight tau J n v * f v) +
      ∑ i ∈ Finset.range n, propagator beta t (tau (i + 1)) *
        jumpWeight tau J n (tau (i + 1)) * b i := by
  have hsum :
      (∑ i ∈ Finset.range n, propagator beta t (tau (i + 1)) *
        jumpWeight tau J n (tau (i + 1)) * b i) =
      ∑ i ∈ Finset.range n, propagator beta t (tau (i + 1)) *
        (∏ j ∈ Finset.Ico (i + 1) n, J j) * b i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [jumpWeight_at_jump tau J n i htime (Finset.mem_range.mp hi)]
  rw [hsum]
  exact finite_piecewise_gronwall tau r post J b beta f q n t
    (fun k hk => (htime k hk).le) hr hbeta hf hineq hstart hJ hjump ht hq
    hineq_final hqstart hzero

end PaperFormalization.Piecewise
