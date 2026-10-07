import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

/-!
# Exact finite affine recurrence expansion

This is the algebraic part of Step 2 of `lem:piecewise-gronwall-forced-jumps`.
There are no sign assumptions in this module. Index `i` contributes the forcing
`b i`, multiplied by exactly the later multipliers with `i < j < n`.
-/

open scoped BigOperators

namespace PaperFormalization.Affine

/-- Exact iteration of `x (k+1) = a k * x k + b k`, starting from `x0`. -/
noncomputable def iterate (a b : ℕ → ℝ) (x0 : ℝ) : ℕ → ℝ
  | 0 => x0
  | n + 1 => a n * iterate a b x0 n + b n

/-- The initial value and each forcing term are propagated by later multipliers. -/
noncomputable def closedForm (a b : ℕ → ℝ) (x0 : ℝ) (n : ℕ) : ℝ :=
  x0 * (∏ k ∈ Finset.range n, a k) +
    ∑ i ∈ Finset.range n, b i * ∏ j ∈ Finset.Ico (i + 1) n, a j

@[simp] theorem closedForm_zero (a b : ℕ → ℝ) (x0 : ℝ) :
    closedForm a b x0 0 = x0 := by
  simp [closedForm]

/-- Appending one step multiplies all earlier contributions, then adds the new one. -/
theorem closedForm_succ (a b : ℕ → ℝ) (x0 : ℝ) (n : ℕ) :
    closedForm a b x0 (n + 1) = a n * closedForm a b x0 n + b n := by
  classical
  have hsum :
      (∑ i ∈ Finset.range n, b i * ∏ j ∈ Finset.Ico (i + 1) (n + 1), a j) =
        (∑ i ∈ Finset.range n, b i * ∏ j ∈ Finset.Ico (i + 1) n, a j) * a n := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.prod_Ico_succ_top (Nat.succ_le_of_lt (Finset.mem_range.mp hi)) a,
      mul_assoc]
  unfold closedForm
  rw [Finset.prod_range_succ, Finset.sum_range_succ, hsum]
  simp only [Finset.Ico_self, Finset.prod_empty, mul_one]
  rw [mul_add]
  ac_rfl

/-- The explicit finite sum equals the recursively defined solution. -/
theorem iterate_eq_closedForm (a b : ℕ → ℝ) (x0 : ℝ) (n : ℕ) :
    iterate a b x0 n = closedForm a b x0 n := by
  induction n with
  | zero => simp [iterate]
  | succ n ih => rw [iterate, ih, closedForm_succ]

/-- Any real sequence satisfying the exact recurrence on this prefix has this form. -/
theorem eq_closedForm_of_recurrence (x a b : ℕ → ℝ) (n : ℕ) :
    (∀ k < n, x (k + 1) = a k * x k + b k) →
      x n = closedForm a b (x 0) n := by
  induction n with
  | zero => intro _; simp
  | succ n ih =>
      intro hstep
      have hprefix : ∀ k < n, x (k + 1) = a k * x k + b k :=
        fun k hk => hstep k (Nat.lt_trans hk (Nat.lt_succ_self n))
      rw [hstep n (Nat.lt_succ_self n), ih hprefix, closedForm_succ]

end PaperFormalization.Affine
