import PaperFormalization.Affine.Comparison
import PaperFormalization.Piecewise.Step

/-! # Finite comparison for explicitly supplied continuous branches and jumps

Each branch starts at the preceding post-jump value and ends at its own
pre-jump trace. The theorem derives the affine recurrence from the analytic
hypotheses; it does not assume the Duhamel conclusion as an input.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PaperFormalization.Piecewise

open Continuous

/-- Apply one-branch Duhamel and the terminal jump on every step of a finite prefix. -/
theorem finite_branch_jump_bound (tau : ℕ → ℝ) (r : ℕ → ℝ → ℝ)
    (post J b : ℕ → ℝ) (beta f : ℝ → ℝ) (n : ℕ)
    (htime : ∀ k < n, tau k ≤ tau (k + 1))
    (hr : ∀ k < n, AbsolutelyContinuousOnInterval (r k) (tau k) (tau (k + 1)))
    (hbeta : ∀ k < n, IntervalIntegrable beta volume (tau k) (tau (k + 1)))
    (hf : ∀ k < n, IntervalIntegrable f volume (tau k) (tau (k + 1)))
    (hineq : ∀ k < n, ∀ᵐ u ∂volume.restrict (Ioo (tau k) (tau (k + 1))),
      deriv (r k) u ≤ -beta u * r k u + f u)
    (hstart : ∀ k < n, r k (tau k) = post k)
    (hJ : ∀ k < n, 0 ≤ J k)
    (hjump : ∀ k < n, post (k + 1) ≤ J k * r k (tau (k + 1)) + b k) :
    post n ≤ Affine.closedForm
      (fun k => J k * propagator beta (tau (k + 1)) (tau k))
      (fun k => J k * forcingResponse beta f (tau (k + 1)) (tau k) + b k)
      (post 0) n := by
  apply Affine.le_closedForm
  · intro k hk
    exact mul_nonneg (hJ k hk) (propagator_nonneg beta (tau (k + 1)) (tau k))
  · intro k hk
    have h := branch_jump_bound (r k) beta f (tau k) (tau (k + 1))
      (J k) (b k) (post (k + 1)) (htime k hk) (hr k hk) (hbeta k hk)
      (hf k hk) (hineq k hk) (hJ k hk) (hjump k hk)
    simpa only [hstart k hk] using h

/-- Zero initial value removes the homogeneous contribution from the finite bound. -/
theorem finite_branch_jump_bound_of_initial_eq_zero (tau : ℕ → ℝ) (r : ℕ → ℝ → ℝ)
    (post J b : ℕ → ℝ) (beta f : ℝ → ℝ) (n : ℕ)
    (htime : ∀ k < n, tau k ≤ tau (k + 1))
    (hr : ∀ k < n, AbsolutelyContinuousOnInterval (r k) (tau k) (tau (k + 1)))
    (hbeta : ∀ k < n, IntervalIntegrable beta volume (tau k) (tau (k + 1)))
    (hf : ∀ k < n, IntervalIntegrable f volume (tau k) (tau (k + 1)))
    (hineq : ∀ k < n, ∀ᵐ u ∂volume.restrict (Ioo (tau k) (tau (k + 1))),
      deriv (r k) u ≤ -beta u * r k u + f u)
    (hstart : ∀ k < n, r k (tau k) = post k)
    (hJ : ∀ k < n, 0 ≤ J k)
    (hjump : ∀ k < n, post (k + 1) ≤ J k * r k (tau (k + 1)) + b k)
    (hzero : post 0 = 0) :
    post n ≤ ∑ i ∈ Finset.range n,
      (J i * forcingResponse beta f (tau (i + 1)) (tau i) + b i) *
        ∏ j ∈ Finset.Ico (i + 1) n, J j * propagator beta (tau (j + 1)) (tau j) := by
  simpa only [Affine.closedForm, hzero, zero_mul, zero_add] using
    finite_branch_jump_bound tau r post J b beta f n htime hr hbeta hf hineq hstart hJ hjump

end PaperFormalization.Piecewise
