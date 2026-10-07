import PaperFormalization.Manuscript.FullSchedule
import PaperFormalization.Manuscript.ZeroDiscrepancy

/-! # Full-schedule comparison from the positive-discrepancy nonlinear inequality

This connects the paper's nonlinear positive-r estimate to the checked stopped
comparison. The zero case and the radius bound before exit are proved internally.
The particle derivation of the positive-r estimate and jump estimates remains
an explicit application obligation.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PaperFormalization.Manuscript

open Continuous Piecewise

/-- The full manuscript-shaped stopped inequality from the nonlinear drift bound. -/
theorem nonlinear_full_schedule_gronwall
    (tau pre J b : ℕ → ℝ) (r kappa gamma : ℝ → ℝ) (c R T t : ℝ) (L : ℕ)
    (htau0 : tau 0 = 0) (htime : ∀ k < L, tau k < tau (k + 1))
    (hT : tau L ≤ T) (hc : 0 ≤ c)
    (hbranch : ∀ k < L, AbsolutelyContinuousOnInterval
      (closedBranch r (tau (k + 1)) (pre k)) (tau k) (tau (k + 1)))
    (hkappa : IntervalIntegrable kappa volume 0 T)
    (hgamma : IntervalIntegrable gamma volume 0 T)
    (hr : ∀ u ∈ Icc 0 T, 0 ≤ r u)
    (hgamma_nonneg : ∀ u ∈ Icc 0 T, 0 ≤ gamma u)
    (hpos : ∀ k < L, ∀ᵐ (u : ℝ) ∂volume.restrict (Ioo (tau k) (tau (k + 1))),
      (u : WithTop ℝ) < exitTime r R T → 0 < r u →
      deriv r u ≤ -kappa u * r u + c * (r u) ^ 2 + gamma u * r u + gamma u)
    (hJ : ∀ k < L, 0 ≤ J k)
    (hjump : ∀ k < L, (tau (k + 1) : WithTop ℝ) ≤ exitTime r R T →
      r (tau (k + 1)) ≤ J k * pre k + b k)
    (hfinal : AbsolutelyContinuousOnInterval r (tau L) T)
    (hpos_final : ∀ᵐ (u : ℝ) ∂volume.restrict (Ioo (tau L) T),
      (u : WithTop ℝ) < exitTime r R T → 0 < r u →
      deriv r u ≤ -kappa u * r u + c * (r u) ^ 2 + gamma u * r u + gamma u)
    (hzero : r 0 = 0) (ht0 : 0 ≤ t) (htT : t ≤ T)
    (htExit : (t : WithTop ℝ) ≤ exitTime r R T) :
    r t ≤ (∫ v in 0..t, propagator (stoppedCoefficient kappa gamma c R) t v *
      (∏ k ∈ (Finset.range L).filter
        (fun k => v < tau (k + 1) ∧ tau (k + 1) ≤ t), J k) * gamma v) +
      ∑ i ∈ (Finset.range L).filter (fun i => tau (i + 1) ≤ t),
        propagator (stoppedCoefficient kappa gamma c R) t (tau (i + 1)) *
          (∏ k ∈ (Finset.range L).filter
            (fun k => tau (i + 1) < tau (k + 1) ∧ tau (k + 1) ≤ t), J k) * b i := by
  have htime' : ∀ k < L, tau k ≤ tau (k + 1) := fun k hk => (htime k hk).le
  have htimes : ∀ i ≤ L, tau i ∈ Icc 0 T := by
    intro i hi
    constructor
    · rw [← htau0]
      exact time_mono_prefix tau L htime' 0 i (Nat.zero_le i) hi
    · exact le_trans (time_mono_prefix tau L htime' i L hi le_rfl) hT
  have hlinear : ∀ a e : ℝ, 0 ≤ a → e ≤ T →
      (∀ᵐ (u : ℝ) ∂volume.restrict (Ioo a e),
        (u : WithTop ℝ) < exitTime r R T → 0 < r u →
        deriv r u ≤ -kappa u * r u + c * (r u) ^ 2 + gamma u * r u + gamma u) →
      ∀ᵐ (u : ℝ) ∂volume.restrict (Ioo a e),
        (u : WithTop ℝ) < exitTime r R T →
        deriv r u ≤ -stoppedCoefficient kappa gamma c R u * r u + gamma u := by
    intro a e ha he hp
    apply ae_deriv_le_stoppedCoefficient_before_exit_of_pos r kappa gamma c R T a e
      hc ha he
    · intro u hu
      exact hr u ⟨le_trans ha hu.1.le, le_trans hu.2.le he⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      exact hgamma_nonneg u ⟨le_trans ha hu.1.le, le_trans hu.2.le he⟩
    · exact hp
  exact stopped_full_schedule_gronwall tau pre J b r (stoppedCoefficient kappa gamma c R)
    gamma R T t L htau0 htime hT hbranch
    (stoppedCoefficient_intervalIntegrable kappa gamma c R 0 T hkappa hgamma) hgamma
    (fun k hk => hlinear (tau k) (tau (k + 1)) (htimes k hk.le).1
      (htimes (k + 1) (Nat.succ_le_of_lt hk)).2 (hpos k hk)) hJ hjump hfinal
    (hlinear (tau L) T (htimes L le_rfl).1 le_rfl hpos_final) hzero ht0 htT htExit

end PaperFormalization.Manuscript
