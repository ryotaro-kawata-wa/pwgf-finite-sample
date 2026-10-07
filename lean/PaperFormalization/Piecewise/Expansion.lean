import PaperFormalization.Piecewise.Finite
import PaperFormalization.Continuous.PropagatorProducts

/-! # Separate continuous forcing and jump errors in the finite comparison

Jump index `i` belongs to the right endpoint `tau (i + 1)`. A forcing term
from branch `i` receives all factors starting at `i`; the jump error `b i`
receives only factors strictly after `i`.
-/

open MeasureTheory
open scoped BigOperators

namespace PaperFormalization.Piecewise

open Continuous

/-- The propagated initial value, branch forcing, and discrete jump errors. -/
noncomputable def expandedBound (tau J b : ℕ → ℝ) (beta f : ℝ → ℝ)
    (x0 : ℝ) (n : ℕ) : ℝ :=
  propagator beta (tau n) (tau 0) * (∏ k ∈ Finset.range n, J k) * x0 +
    (∑ i ∈ Finset.range n, (∏ j ∈ Finset.Ico i n, J j) *
      ∫ v in tau i..tau (i + 1), propagator beta (tau n) v * f v) +
    ∑ i ∈ Finset.range n, propagator beta (tau n) (tau (i + 1)) *
      (∏ j ∈ Finset.Ico (i + 1) n, J j) * b i

@[simp] theorem expandedBound_zero (tau J b : ℕ → ℝ) (beta f : ℝ → ℝ) (x0 : ℝ) :
    expandedBound tau J b beta f x0 0 = x0 := by
  simp [expandedBound]

/-- Expand one propagated affine forcing term into its branch and jump contributions. -/
theorem propagated_step_eq (tau J b : ℕ → ℝ) (beta f : ℝ → ℝ) (i n : ℕ)
    (hi : i < n)
    (hbeta : ∀ k < n, IntervalIntegrable beta volume (tau k) (tau (k + 1))) :
    (J i * forcingResponse beta f (tau (i + 1)) (tau i) + b i) *
        (∏ j ∈ Finset.Ico (i + 1) n, J j * propagator beta (tau (j + 1)) (tau j)) =
      (∏ j ∈ Finset.Ico i n, J j) *
        (∫ v in tau i..tau (i + 1), propagator beta (tau n) v * f v) +
      propagator beta (tau n) (tau (i + 1)) *
        (∏ j ∈ Finset.Ico (i + 1) n, J j) * b i := by
  have hin : i + 1 ≤ n := Nat.succ_le_of_lt hi
  have htail : IntervalIntegrable beta volume (tau (i + 1)) (tau n) :=
    IntervalIntegrable.trans_iterate_Ico hin (fun k hk => hbeta k hk.2)
  rw [prod_jump_propagator_Ico beta tau J (i + 1) n hin (fun k _ hk => hbeta k hk),
    Finset.prod_eq_prod_Ico_succ_bot hi J,
    ← propagator_mul_forcingResponse beta f (tau i) (tau (i + 1)) (tau n) (hbeta i hi) htail]
  ring

/-- The affine closed form equals the branch-integral and jump-sum expression. -/
theorem affine_closedForm_eq_expandedBound (tau J b : ℕ → ℝ) (beta f : ℝ → ℝ)
    (x0 : ℝ) (n : ℕ)
    (hbeta : ∀ k < n, IntervalIntegrable beta volume (tau k) (tau (k + 1))) :
    Affine.closedForm
      (fun k => J k * propagator beta (tau (k + 1)) (tau k))
      (fun k => J k * forcingResponse beta f (tau (k + 1)) (tau k) + b k) x0 n =
      expandedBound tau J b beta f x0 n := by
  have hp := prod_jump_propagator_Ico beta tau J 0 n (Nat.zero_le n)
    (fun k _ hk => hbeta k hk)
  simp only [Nat.Ico_zero_eq_range] at hp
  have hs :
      (∑ i ∈ Finset.range n,
        (J i * forcingResponse beta f (tau (i + 1)) (tau i) + b i) *
          (∏ j ∈ Finset.Ico (i + 1) n, J j * propagator beta (tau (j + 1)) (tau j))) =
      (∑ i ∈ Finset.range n, (∏ j ∈ Finset.Ico i n, J j) *
        ∫ v in tau i..tau (i + 1), propagator beta (tau n) v * f v) +
      ∑ i ∈ Finset.range n, propagator beta (tau n) (tau (i + 1)) *
        (∏ j ∈ Finset.Ico (i + 1) n, J j) * b i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i hi =>
      propagated_step_eq tau J b beta f i n (Finset.mem_range.mp hi) hbeta)
  unfold Affine.closedForm expandedBound
  dsimp only
  rw [hp, hs]
  ring

/-- Finite branch and jump comparison, with every contribution transported to the terminal time. -/
theorem finite_branch_jump_expanded_bound (tau : ℕ → ℝ) (r : ℕ → ℝ → ℝ)
    (post J b : ℕ → ℝ) (beta f : ℝ → ℝ) (n : ℕ)
    (htime : ∀ k < n, tau k ≤ tau (k + 1))
    (hr : ∀ k < n, AbsolutelyContinuousOnInterval (r k) (tau k) (tau (k + 1)))
    (hbeta : ∀ k < n, IntervalIntegrable beta volume (tau k) (tau (k + 1)))
    (hf : ∀ k < n, IntervalIntegrable f volume (tau k) (tau (k + 1)))
    (hineq : ∀ k < n, ∀ᵐ u ∂volume.restrict (Set.Ioo (tau k) (tau (k + 1))),
      deriv (r k) u ≤ -beta u * r k u + f u)
    (hstart : ∀ k < n, r k (tau k) = post k)
    (hJ : ∀ k < n, 0 ≤ J k)
    (hjump : ∀ k < n, post (k + 1) ≤ J k * r k (tau (k + 1)) + b k) :
    post n ≤ expandedBound tau J b beta f (post 0) n := by
  rw [← affine_closedForm_eq_expandedBound tau J b beta f (post 0) n hbeta]
  exact finite_branch_jump_bound tau r post J b beta f n htime hr hbeta hf hineq hstart hJ hjump

end PaperFormalization.Piecewise
