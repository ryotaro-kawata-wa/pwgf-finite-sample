import PaperFormalization.Affine.Expansion

/-!
# Comparison for a finite affine recurrence

The hypotheses are restricted to the prefix `k < n`. Only the multiplier `a k`
must be nonnegative; neither the sequence `x` nor the forcing `b` needs a sign
assumption. This module proves the algebraic comparison only: deriving the
recurrence from an absolutely continuous trajectory remains a separate task.
-/

open scoped BigOperators

namespace PaperFormalization.Affine

/-- A finite affine subsolution is bounded by the exact closed-form solution. -/
theorem le_closedForm (x a b : ℕ → ℝ) (n : ℕ) :
    (∀ k < n, 0 ≤ a k) →
    (∀ k < n, x (k + 1) ≤ a k * x k + b k) →
      x n ≤ closedForm a b (x 0) n := by
  induction n with
  | zero => intro _ _; simp
  | succ n ih =>
      intro hnonneg hstep
      have hnonneg_prefix : ∀ k < n, 0 ≤ a k :=
        fun k hk => hnonneg k (Nat.lt_trans hk (Nat.lt_succ_self n))
      have hstep_prefix : ∀ k < n, x (k + 1) ≤ a k * x k + b k :=
        fun k hk => hstep k (Nat.lt_trans hk (Nat.lt_succ_self n))
      calc
        x (n + 1) ≤ a n * x n + b n := hstep n (Nat.lt_succ_self n)
        _ ≤ a n * closedForm a b (x 0) n + b n :=
          add_le_add
            (mul_le_mul_of_nonneg_left (ih hnonneg_prefix hstep_prefix)
              (hnonneg n (Nat.lt_succ_self n))) (le_refl (b n))
        _ = closedForm a b (x 0) (n + 1) := (closedForm_succ a b (x 0) n).symm

/-- With zero initial value, only the forcing terms and their later factors remain. -/
theorem le_forcing_sum_of_initial_eq_zero (x a b : ℕ → ℝ) (n : ℕ)
    (hzero : x 0 = 0)
    (hnonneg : ∀ k < n, 0 ≤ a k)
    (hstep : ∀ k < n, x (k + 1) ≤ a k * x k + b k) :
    x n ≤ ∑ i ∈ Finset.range n, b i * ∏ j ∈ Finset.Ico (i + 1) n, a j := by
  simpa only [closedForm, hzero, zero_mul, zero_add] using
    le_closedForm x a b n hnonneg hstep

end PaperFormalization.Affine
