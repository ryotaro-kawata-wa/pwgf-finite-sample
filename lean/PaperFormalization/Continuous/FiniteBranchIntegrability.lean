import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Integrability from finitely many branch representatives

A real path can have different pre-jump and post-jump endpoint values.
Representatives need agree with it only on each open branch interior;
Lebesgue measure ignores the finitely many endpoints. Nondecreasing schedules
allow empty intervals, including a terminal interval after a jump at T.

This is a deterministic regularity bridge. It does not derive branch
representatives or their integrability from the manuscript's particle model.
-/

open MeasureTheory Set

namespace PaperFormalization.Continuous

/-- Endpoint values need not match an integrable representative. -/
theorem intervalIntegrable_of_open_branch_eq (f q : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hq : IntervalIntegrable q volume a b)
    (heq : EqOn q f (Ioo a b)) : IntervalIntegrable f volume a b := by
  apply hq.congr_uIoo
  simpa only [uIoo_of_le hab] using heq

/-- Finitely many integrable branch representatives give full-interval integrability. -/
theorem intervalIntegrable_of_finite_branch_representatives
    (tau : ℕ → ℝ) (q : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (n : ℕ)
    (htime : ∀ k < n, tau k ≤ tau (k + 1))
    (hq : ∀ k < n, IntervalIntegrable (q k) volume (tau k) (tau (k + 1)))
    (heq : ∀ k < n, EqOn (q k) f (Ioo (tau k) (tau (k + 1)))) :
    IntervalIntegrable f volume (tau 0) (tau n) := by
  apply IntervalIntegrable.trans_iterate
  intro k hk
  exact intervalIntegrable_of_open_branch_eq f (q k) (tau k) (tau (k + 1))
    (htime k hk) (hq k hk) (heq k hk)

/-- Continuous closed-branch representatives suffice, despite arbitrary endpoint path values. -/
theorem intervalIntegrable_of_finite_continuous_branch_representatives
    (tau : ℕ → ℝ) (q : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (n : ℕ)
    (htime : ∀ k < n, tau k ≤ tau (k + 1))
    (hq : ∀ k < n, ContinuousOn (q k) (Icc (tau k) (tau (k + 1))))
    (heq : ∀ k < n, EqOn (q k) f (Ioo (tau k) (tau (k + 1)))) :
    IntervalIntegrable f volume (tau 0) (tau n) := by
  apply intervalIntegrable_of_finite_branch_representatives tau q f n htime
  · intro k hk
    exact ContinuousOn.intervalIntegrable_of_Icc (htime k hk) (hq k hk)
  · exact heq

/-- Append the last observation branch; an empty final interval is allowed. -/
theorem intervalIntegrable_of_finite_branch_representatives_and_final
    (tau : ℕ → ℝ) (q : ℕ → ℝ → ℝ) (f qfinal : ℝ → ℝ) (n : ℕ) (t : ℝ)
    (htime : ∀ k < n, tau k ≤ tau (k + 1))
    (hq : ∀ k < n, IntervalIntegrable (q k) volume (tau k) (tau (k + 1)))
    (heq : ∀ k < n, EqOn (q k) f (Ioo (tau k) (tau (k + 1))))
    (ht : tau n ≤ t) (hqfinal : IntervalIntegrable qfinal volume (tau n) t)
    (heqfinal : EqOn qfinal f (Ioo (tau n) t)) :
    IntervalIntegrable f volume (tau 0) t :=
  (intervalIntegrable_of_finite_branch_representatives tau q f n htime hq heq).trans
    (intervalIntegrable_of_open_branch_eq f qfinal (tau n) t ht hqfinal heqfinal)

end PaperFormalization.Continuous
