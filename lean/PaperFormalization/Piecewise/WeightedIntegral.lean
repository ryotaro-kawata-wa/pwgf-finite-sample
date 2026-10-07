import PaperFormalization.Piecewise.JumpWeight
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Reassemble branch integrals into the jump-weighted integral

The filtered jump weight is constant on each open branch. Equalities on open
intervals suffice because endpoints have zero Lebesgue measure. Integrability
is proved rather than presumed for the new weighted integrand.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PaperFormalization.Piecewise

/-- Integrability of the weighted integrand on an individual branch. -/
theorem jumpWeight_mul_intervalIntegrable_branch (tau J : ℕ → ℝ) (g : ℝ → ℝ)
    (n i : ℕ) (htime : ∀ k < n, tau k ≤ tau (k + 1)) (hi : i < n)
    (hg : IntervalIntegrable g volume (tau i) (tau (i + 1))) :
    IntervalIntegrable (fun v => jumpWeight tau J n v * g v) volume (tau i) (tau (i + 1)) := by
  apply (hg.const_mul (∏ j ∈ Finset.Ico i n, J j)).congr_uIoo
  intro v hv
  have hvo : v ∈ Ioo (tau i) (tau (i + 1)) := by
    simpa only [uIoo_of_le (htime i hi)] using hv
  dsimp only
  rw [jumpWeight_on_branch tau J n i htime hi v hvo]

/-- A branch integral has the product of that branch's subsequent jump factors. -/
theorem integral_jumpWeight_mul_branch (tau J : ℕ → ℝ) (g : ℝ → ℝ)
    (n i : ℕ) (htime : ∀ k < n, tau k ≤ tau (k + 1)) (hi : i < n) :
    (∫ v in tau i..tau (i + 1), jumpWeight tau J n v * g v) =
      (∏ j ∈ Finset.Ico i n, J j) * ∫ v in tau i..tau (i + 1), g v := by
  calc
    _ = ∫ v in tau i..tau (i + 1), (∏ j ∈ Finset.Ico i n, J j) * g v := by
      apply intervalIntegral.integral_congr_Ioo_of_le (htime i hi)
      intro v hv
      dsimp only
      rw [jumpWeight_on_branch tau J n i htime hi v hv]
    _ = _ := intervalIntegral.integral_const_mul _ _

/-- Integrability after the last jump, where the jump weight is one. -/
theorem jumpWeight_mul_intervalIntegrable_final (tau J : ℕ → ℝ) (g : ℝ → ℝ)
    (n : ℕ) (t : ℝ) (htime : ∀ k < n, tau k ≤ tau (k + 1)) (ht : tau n ≤ t)
    (hg : IntervalIntegrable g volume (tau n) t) :
    IntervalIntegrable (fun v => jumpWeight tau J n v * g v) volume (tau n) t := by
  apply hg.congr_uIoo
  intro v hv
  have hvo : v ∈ Ioo (tau n) t := by simpa only [uIoo_of_le ht] using hv
  dsimp only
  rw [jumpWeight_after_last tau J n htime v hvo.1.le, one_mul]

/-- No jump factor multiplies forcing on the final observation interval. -/
theorem integral_jumpWeight_mul_final (tau J : ℕ → ℝ) (g : ℝ → ℝ)
    (n : ℕ) (t : ℝ) (htime : ∀ k < n, tau k ≤ tau (k + 1)) (ht : tau n ≤ t) :
    (∫ v in tau n..t, jumpWeight tau J n v * g v) = ∫ v in tau n..t, g v := by
  apply intervalIntegral.integral_congr_Ioo_of_le ht
  intro v hv
  dsimp only
  rw [jumpWeight_after_last tau J n htime v hv.1.le, one_mul]

/-- The jump-weighted integrand is integrable on the full observation interval. -/
theorem intervalIntegrable_jumpWeight_mul (tau J : ℕ → ℝ) (g : ℝ → ℝ)
    (n : ℕ) (t : ℝ) (htime : ∀ k < n, tau k ≤ tau (k + 1)) (ht : tau n ≤ t)
    (hg : ∀ k < n, IntervalIntegrable g volume (tau k) (tau (k + 1)))
    (hg_final : IntervalIntegrable g volume (tau n) t) :
    IntervalIntegrable (fun v => jumpWeight tau J n v * g v) volume (tau 0) t := by
  exact (IntervalIntegrable.trans_iterate (fun k hk =>
    jumpWeight_mul_intervalIntegrable_branch tau J g n k htime hk (hg k hk))).trans
      (jumpWeight_mul_intervalIntegrable_final tau J g n t htime ht hg_final)

/-- Split the full weighted integral into its constant-weight branch pieces and final interval. -/
theorem integral_jumpWeight_mul (tau J : ℕ → ℝ) (g : ℝ → ℝ)
    (n : ℕ) (t : ℝ) (htime : ∀ k < n, tau k ≤ tau (k + 1)) (ht : tau n ≤ t)
    (hg : ∀ k < n, IntervalIntegrable g volume (tau k) (tau (k + 1)))
    (hg_final : IntervalIntegrable g volume (tau n) t) :
    (∫ v in tau 0..t, jumpWeight tau J n v * g v) =
      (∑ i ∈ Finset.range n, (∏ j ∈ Finset.Ico i n, J j) *
        ∫ v in tau i..tau (i + 1), g v) + ∫ v in tau n..t, g v := by
  have hbranches : ∀ k < n,
      IntervalIntegrable (fun v => jumpWeight tau J n v * g v) volume (tau k) (tau (k + 1)) :=
    fun k hk => jumpWeight_mul_intervalIntegrable_branch tau J g n k htime hk (hg k hk)
  have hlast := jumpWeight_mul_intervalIntegrable_final tau J g n t htime ht hg_final
  calc
    _ = (∫ v in tau 0..tau n, jumpWeight tau J n v * g v) +
        ∫ v in tau n..t, jumpWeight tau J n v * g v :=
      (intervalIntegral.integral_add_adjacent_intervals
        (IntervalIntegrable.trans_iterate hbranches) hlast).symm
    _ = (∑ i ∈ Finset.range n,
        ∫ v in tau i..tau (i + 1), jumpWeight tau J n v * g v) +
        ∫ v in tau n..t, jumpWeight tau J n v * g v := by
      rw [intervalIntegral.sum_integral_adjacent_intervals hbranches]
    _ = _ := by
      rw [integral_jumpWeight_mul_final tau J g n t htime ht]
      congr 1
      exact Finset.sum_congr rfl (fun i hi =>
        integral_jumpWeight_mul_branch tau J g n i htime (Finset.mem_range.mp hi))

end PaperFormalization.Piecewise
