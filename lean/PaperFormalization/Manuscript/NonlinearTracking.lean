import PaperFormalization.Manuscript.NonlinearComparison
import PaperFormalization.Manuscript.StoppedEnvelope
import PaperFormalization.Manuscript.BootstrapMargin

/-! # End-to-end deterministic nonlinear tracking under the source smallness condition

This theorem assembles the nonlinear stopped comparison, the directly derived
forcing envelope, and attained-exit contradiction. It remains conditional on
the particle-model differential/jump estimates and the supplied forcing majorant.
The probability of those inputs is not a conclusion of this deterministic theorem.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PaperFormalization.Manuscript

open Continuous Piecewise

/-- Amplification over the whole prescribed schedule. -/
noncomputable def jumpAmplification (a : ℕ → ℝ) (L : ℕ) : ℝ :=
  ∏ k ∈ Finset.range L, (1 + a k)

/-- Curvature response to uniform continuous forcing and the actual additive jumps. -/
noncomputable def curvatureEnvelope (kappa : ℝ → ℝ) (tau b : ℕ → ℝ)
    (delta : ℝ) (L : ℕ) (t : ℝ) : ℝ :=
  delta * (∫ s in (0 : ℝ)..t, propagator kappa t s) +
    ∑ i ∈ (Finset.range L).filter (fun i => tau (i + 1) ≤ t),
      propagator kappa t (tau (i + 1)) * b i

/-- The actual forcing response is nonnegative. -/
theorem curvatureEnvelope_nonneg (kappa : ℝ → ℝ) (tau b : ℕ → ℝ)
    (delta : ℝ) (L : ℕ) (t : ℝ) (hdelta : 0 ≤ delta) (ht : 0 ≤ t)
    (hb : ∀ i < L, 0 ≤ b i) : 0 ≤ curvatureEnvelope kappa tau b delta L t := by
  apply add_nonneg
  · exact mul_nonneg hdelta
      (intervalIntegral.integral_nonneg_of_forall ht (fun s => propagator_nonneg kappa t s))
  · apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (propagator_nonneg _ _ _) (hb i
      (Finset.mem_range.mp (Finset.mem_filter.mp hi).1))

/-- The paper's positive-envelope deterministic tracking conclusion, with no assumed
stopped forcing estimate or exit attainment. The exact source smallness is retained. -/
theorem nonlinear_tracking_bound
    (tau pre a b : ℕ → ℝ) (r kappa gamma Benv : ℝ → ℝ)
    (c R delta T Bstar : ℝ) (L : ℕ)
    (htau0 : tau 0 = 0) (htime : ∀ k < L, tau k < tau (k + 1)) (hT : tau L ≤ T)
    (hc : 0 ≤ c) (hdelta : 0 ≤ delta) (hBstar : 0 < Bstar)
    (hR : R = 2 * jumpAmplification a L * Bstar)
    (hsmall : T * (delta + c * R) ≤ 1 / 4)
    (hbranch : ∀ k < L, AbsolutelyContinuousOnInterval
      (closedBranch r (tau (k + 1)) (pre k)) (tau k) (tau (k + 1)))
    (hkappa : IntervalIntegrable kappa volume 0 T)
    (hgamma : IntervalIntegrable gamma volume 0 T)
    (hr : ∀ u ∈ Icc 0 T, 0 ≤ r u)
    (hgamma_bound : ∀ u ∈ Icc 0 T, 0 ≤ gamma u ∧ gamma u ≤ delta)
    (hpos : ∀ k < L, ∀ᵐ (u : ℝ) ∂volume.restrict (Ioo (tau k) (tau (k + 1))),
      (u : WithTop ℝ) < exitTime r R T → 0 < r u →
      deriv r u ≤ -kappa u * r u + c * (r u) ^ 2 + gamma u * r u + gamma u)
    (ha : ∀ k < L, 0 ≤ a k) (hb : ∀ k < L, 0 ≤ b k)
    (hjump : ∀ k < L, (tau (k + 1) : WithTop ℝ) ≤ exitTime r R T →
      r (tau (k + 1)) ≤ (1 + a k) * pre k + b k)
    (hfinal : AbsolutelyContinuousOnInterval r (tau L) T)
    (hpos_final : ∀ᵐ (u : ℝ) ∂volume.restrict (Ioo (tau L) T),
      (u : WithTop ℝ) < exitTime r R T → 0 < r u →
      deriv r u ≤ -kappa u * r u + c * (r u) ^ 2 + gamma u * r u + gamma u)
    (hzero : r 0 = 0)
    (hEnvelope : ∀ t ∈ Icc 0 T, curvatureEnvelope kappa tau b delta L t ≤ Benv t)
    (hBenv : ∀ t ∈ Icc 0 T, Benv t ≤ Bstar) :
    exitTime r R T = ⊤ ∧
      ∀ t ∈ Icc 0 T, r t ≤ Real.exp (1 / 4) * jumpAmplification a L * Benv t := by
  subst R
  have hJ : 0 < jumpAmplification a L := lt_of_lt_of_le zero_lt_one
    (one_le_jump_amplification (Finset.range L) a (fun k hk => ha k (Finset.mem_range.mp hk)))
  have hR0 : 0 ≤ 2 * jumpAmplification a L * Bstar := by positivity
  have hmono : ∀ k < L, tau k ≤ tau (k + 1) := fun k hk => (htime k hk).le
  apply tracking_bound_of_smallness r Benv (jumpAmplification a L) Bstar T c delta
    hJ hBstar hsmall
  · intro t ht
    exact ⟨(curvatureEnvelope_nonneg kappa tau b delta L t hdelta ht.1 hb).trans
      (hEnvelope t ht), hBenv t ht⟩
  · intro t ht
    exact finite_schedule_right_continuous tau pre r L T t hmono hbranch hfinal
      (by simpa only [htau0] using ht.1) ht.2
  · intro t ht hstop
    have hcomp := nonlinear_full_schedule_gronwall tau pre (fun k => 1 + a k) b
      r kappa gamma c (2 * jumpAmplification a L * Bstar) T t L htau0 htime hT hc
      hbranch hkappa hgamma hr (fun u hu => (hgamma_bound u hu).1) hpos
      (fun k hk => by linarith [ha k hk]) hjump hfinal hpos_final hzero ht.1 ht.2 hstop
    have hbound := hcomp.trans (stopped_comparison_rhs_le_envelope tau a b kappa gamma L
      c (2 * jumpAmplification a L * Bstar) delta T t htau0 hmono hc hR0 hdelta
      ht.1 ht.2 hkappa hgamma hgamma_bound ha hb)
    change r t ≤ jumpAmplification a L *
      Real.exp (T * (c * (2 * jumpAmplification a L * Bstar) + delta)) *
        curvatureEnvelope kappa tau b delta L t at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_left (hEnvelope t ht)
      (mul_nonneg hJ.le (Real.exp_pos _).le))

end PaperFormalization.Manuscript
