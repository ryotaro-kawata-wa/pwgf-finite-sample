import PaperFormalization.Manuscript.SourceTrackingAllCases
import PaperFormalization.Manuscript.SourcePreJumpTracking

/-! # All source tracking cases, including the actual left traces

M13o declarations checked with the pinned toolchain; see verification/latest.json.
The pre-jump envelope contains only strictly earlier jumps. A zero full
supremum is handled by continuity of the actual closed branch, not by a
positive-radius assumption. No positive final-branch length is required.
-/
open MeasureTheory Set
namespace PaperFormalization.Manuscript
open Continuous Piecewise

/-- Right/post tracking and strict-prefix left/pre tracking, with both zero
conclusions, from the same unconditional scalar inputs. -/
theorem source_tracking_all_cases_with_pre
    (tau pre eta gammaPre gammaTildePre : ℕ → ℝ) (r kappa gamma : ℝ → ℝ)
    (c delta deltaTilde A T : ℝ) (L : ℕ)
    (htau0 : tau 0=0) (htime : ∀ k < L, tau k < tau (k+1)) (hT : tau L ≤ T)
    (hc : 0 ≤ c) (hdelta : 0 ≤ delta) (hA : 0 ≤ A)
    (hsmall : T*(delta+c*(2*jumpAmplification (sourceJumpError A eta) L*
      sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A L T)) ≤ 1/4)
    (hbranch : ∀ k < L, AbsolutelyContinuousOnInterval
      (closedBranch r (tau (k+1)) (pre k)) (tau k) (tau (k+1)))
    (hkappa : IntervalIntegrable kappa volume 0 T)
    (hgamma : IntervalIntegrable gamma volume 0 T)
    (hr : ∀ t ∈ Icc 0 T, 0 ≤ r t)
    (hgamma_bound : ∀ t ∈ Icc 0 T, 0 ≤ gamma t ∧ gamma t ≤ delta)
    (hdrift : ∀ k < L, ∀ᵐ t ∂volume.restrict (Ioo (tau k) (tau (k+1))),
      deriv r t ≤ -kappa t*r t+c*(r t)^2+gamma t*r t+gamma t)
    (heta : ∀ k < L, 0 ≤ eta k)
    (hgammaPre : ∀ k < L, gammaPre k ≤ delta)
    (hgammaTildePre : ∀ k < L, gammaTildePre k ≤ deltaTilde)
    (hjump : ∀ k < L, r (tau (k+1)) ≤ (1+sourceJumpError A eta k)*pre k+
      sourceJumpForcing A eta gammaPre gammaTildePre k)
    (hfinal : AbsolutelyContinuousOnInterval r (tau L) T)
    (hdrift_final : ∀ᵐ t ∂volume.restrict (Ioo (tau L) T),
      deriv r t ≤ -kappa t*r t+c*(r t)^2+gamma t*r t+gamma t)
    (hzero : r 0=0) :
    ((∀ t ∈ Icc 0 T, r t ≤ Real.exp (1/4) *
      jumpAmplification (sourceJumpError A eta) L *
        sourceCurvatureEnvelope kappa tau eta delta deltaTilde A L t) ∧
      (sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A L T = 0 →
        ∀ t ∈ Icc 0 T, r t = 0)) ∧
    ((∀ n < L, pre n ≤ Real.exp (1/4) *
      jumpAmplification (sourceJumpError A eta) L *
        sourceCurvatureEnvelope kappa tau eta delta deltaTilde A n (tau (n+1))) ∧
      (sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A L T = 0 →
        ∀ n < L, pre n = 0)) := by
  have htrack := source_tracking_all_cases
    tau pre eta gammaPre gammaTildePre r kappa gamma c delta deltaTilde A T L
    htau0 htime hT hc hdelta hA hsmall hbranch hkappa hgamma hr hgamma_bound
    hdrift heta hgammaPre hgammaTildePre hjump hfinal hdrift_final hzero
  have htimes : ∀ i ≤ L, tau i ∈ Icc 0 T := by
    intro i hi
    constructor
    · rw [← htau0]
      exact time_mono_prefix tau L (fun k hk => (htime k hk).le)
        0 i (Nat.zero_le _) hi
    · exact (time_mono_prefix tau L (fun k hk => (htime k hk).le)
        i L hi le_rfl).trans hT
  have hzpre : sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A L T = 0 →
      ∀ n < L, pre n = 0 := by
    intro hB n hn
    apply pre_trace_eq_zero_of_path_zero r (tau n) (tau (n+1)) (pre n)
      (htime n hn) (hbranch n hn)
    intro t ht
    exact htrack.2 hB t ⟨(htimes n hn.le).1.trans ht.1.le,
      ht.2.le.trans (htimes (n+1) (Nat.succ_le_of_lt hn)).2⟩
  have hAmp : 0 ≤ jumpAmplification (sourceJumpError A eta) L := by
    exact Finset.prod_nonneg fun k hk => by
      have he := sourceJumpError_nonneg A eta k hA (heta k (Finset.mem_range.mp hk))
      linarith
  have hBnonneg := sourceCurvatureEnvelopeSup_nonneg kappa tau eta delta deltaTilde A L T
    ((htimes L le_rfl).1.trans hT) hdelta hA hkappa
    (fun k hk => (htimes (k+1) (Nat.succ_le_of_lt hk)).1) heta
  refine ⟨htrack, ?_, hzpre⟩
  intro n hn
  rcases eq_or_lt_of_le hBnonneg with hB | hB
  · rw [hzpre hB.symm n hn]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le hAmp)
      (sourceCurvatureEnvelope_nonneg kappa tau eta delta deltaTilde A n (tau (n+1))
        hdelta hA (htimes (n+1) (Nat.succ_le_of_lt hn)).1
        (fun k hk => heta k (lt_trans hk hn)))
  · let R := 2 * jumpAmplification (sourceJumpError A eta) L *
        sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A L T
    have hR : 0 ≤ R := mul_nonneg (mul_nonneg (by norm_num) hAmp) hBnonneg
    have hnoexit := (source_tracking_bound
      tau pre eta gammaPre gammaTildePre r kappa gamma c R delta deltaTilde A T L
      htau0 htime hT hc hdelta hA hB rfl hsmall hbranch hkappa hgamma hr hgamma_bound
      (fun k hk => (hdrift k hk).mono (fun _ hu _ _ => hu))
      heta hgammaPre hgammaTildePre (fun k hk _ => hjump k hk)
      hfinal (hdrift_final.mono (fun _ hu _ _ => hu)) hzero).1
    apply source_pre_jump_tracking_bound
      tau pre eta gammaPre gammaTildePre r kappa gamma c R delta deltaTilde A T L n hn
      htau0 htime hT hc hR hdelta hA hsmall hbranch hkappa hgamma hr hgamma_bound
      (fun k hk => (hdrift k hk).mono (fun _ hu _ _ => hu))
      heta hgammaPre hgammaTildePre (fun k hk _ => hjump k hk)
      _ hzero
    rw [hnoexit]
    exact le_top
end PaperFormalization.Manuscript
