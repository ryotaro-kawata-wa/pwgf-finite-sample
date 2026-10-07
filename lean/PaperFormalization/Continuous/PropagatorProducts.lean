import PaperFormalization.Continuous.Propagator
import Mathlib.Algebra.BigOperators.Intervals

/-! # Products of propagators across finitely many adjacent intervals

The identities use oriented integrals and do not require an ordering of the
real endpoints. Integrability is required only for the finite set of intervals.
-/

open MeasureTheory
open scoped BigOperators

namespace PaperFormalization.Continuous

/-- Consecutive propagators collapse to the propagator between the two outer endpoints. -/
theorem prod_propagator_Ico (beta : ℝ → ℝ) (tau : ℕ → ℝ) (m n : ℕ)
    (hmn : m ≤ n)
    (hbeta : ∀ k, m ≤ k → k < n →
      IntervalIntegrable beta volume (tau k) (tau (k + 1))) :
    (∏ k ∈ Finset.Ico m n, propagator beta (tau (k + 1)) (tau k)) =
      propagator beta (tau n) (tau m) := by
  unfold propagator
  rw [← Real.exp_sum, Finset.sum_neg_distrib,
    intervalIntegral.sum_integral_adjacent_intervals_Ico hmn
      (fun k hk => hbeta k hk.1 hk.2)]

/-- The jump multipliers remain as a finite product while the propagators collapse. -/
theorem prod_jump_propagator_Ico (beta : ℝ → ℝ) (tau J : ℕ → ℝ) (m n : ℕ)
    (hmn : m ≤ n)
    (hbeta : ∀ k, m ≤ k → k < n →
      IntervalIntegrable beta volume (tau k) (tau (k + 1))) :
    (∏ k ∈ Finset.Ico m n, J k * propagator beta (tau (k + 1)) (tau k)) =
      (∏ k ∈ Finset.Ico m n, J k) * propagator beta (tau n) (tau m) := by
  rw [Finset.prod_mul_distrib, prod_propagator_Ico beta tau m n hmn hbeta]

end PaperFormalization.Continuous
