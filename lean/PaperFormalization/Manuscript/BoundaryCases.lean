import PaperFormalization.Manuscript.StoppedComparison

/-! # Stopped comparison with no jumps or immediately after the last jump

These corollaries discharge the vacuous final-interval premises rather than
leaving them as inputs. The final jump may coincide with the candidate exit.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PaperFormalization.Manuscript

open Continuous Piecewise

/-- With no jumps and zero initial discrepancy, only the continuous forcing remains. -/
theorem stopped_duhamel_bound (r beta f : ℝ → ℝ) (R T t : ℝ)
    (ht : 0 ≤ t) (htExit : (t : WithTop ℝ) ≤ exitTime r R T)
    (hr : AbsolutelyContinuousOnInterval r 0 t)
    (hbeta : IntervalIntegrable beta volume 0 t)
    (hf : IntervalIntegrable f volume 0 t)
    (hineq : ∀ᵐ (u : ℝ) ∂volume.restrict (Ioo 0 t),
      (u : WithTop ℝ) < exitTime r R T → deriv r u ≤ -beta u * r u + f u)
    (hzero : r 0 = 0) :
    r t ≤ ∫ v in 0..t, propagator beta t v * f v := by
  have h := duhamel_bound_of_ae_on_Ioo r beta f 0 t ht hr hbeta hf
    (ae_deriv_le_of_before_exit r beta f R T 0 t htExit hineq)
  simpa only [hzero, mul_zero, zero_add] using h

/-- Observation immediately after the last selected jump, including a candidate exit jump. -/
theorem stopped_piecewise_gronwall_at_last_jump (tau pre J b : ℕ → ℝ) (r beta f : ℝ → ℝ)
    (R T : ℝ) (n : ℕ) (htau0 : tau 0 = 0)
    (htime : ∀ k < n, tau k < tau (k + 1))
    (hbranch : ∀ k < n, AbsolutelyContinuousOnInterval
      (closedBranch r (tau (k + 1)) (pre k)) (tau k) (tau (k + 1)))
    (hbeta : IntervalIntegrable beta volume 0 (tau n))
    (hf : IntervalIntegrable f volume 0 (tau n))
    (hineq : ∀ k < n, ∀ᵐ (u : ℝ) ∂volume.restrict (Ioo (tau k) (tau (k + 1))),
      (u : WithTop ℝ) < exitTime r R T → deriv r u ≤ -beta u * r u + f u)
    (hJ : ∀ k < n, 0 ≤ J k)
    (hjump : ∀ k < n, (tau (k + 1) : WithTop ℝ) ≤ exitTime r R T →
      r (tau (k + 1)) ≤ J k * pre k + b k)
    (htExit : (tau n : WithTop ℝ) ≤ exitTime r R T)
    (hzero : r 0 = 0) :
    r (tau n) ≤ (∫ v in 0..tau n, propagator beta (tau n) v * jumpWeight tau J n v * f v) +
      ∑ i ∈ Finset.range n, propagator beta (tau n) (tau (i + 1)) *
        jumpWeight tau J n (tau (i + 1)) * b i := by
  exact stopped_piecewise_gronwall tau pre J b r beta f R T (tau n) n htau0 htime hbranch
    hbeta hf hineq hJ hjump (le_refl _) htExit (ac_singleton r (tau n)) (by simp) hzero

end PaperFormalization.Manuscript
