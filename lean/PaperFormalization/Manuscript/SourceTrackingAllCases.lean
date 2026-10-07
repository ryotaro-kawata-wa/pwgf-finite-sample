import PaperFormalization.Manuscript.SourceTracking

/-! # Source tracking with both actual-envelope cases resolved

Actual path adapters supply unconditional branch drifts and jump recursion.
This unit resolves the positive/zero actual supremum internally, so the final
path bound needs no positivity assumption on that supremum and works at T=0.
-/
open MeasureTheory Set
namespace PaperFormalization.Manuscript
open Continuous Piecewise

/-- The source path bound, including zero actual forcing, from unconditional
branch/jump estimates supplied by the actual-model adapters. -/
theorem source_tracking_all_cases
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
    (∀ t ∈ Icc 0 T, r t ≤ Real.exp (1/4)*jumpAmplification (sourceJumpError A eta) L*
      sourceCurvatureEnvelope kappa tau eta delta deltaTilde A L t) ∧
    (sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A L T=0 →
      ∀ t ∈ Icc 0 T, r t=0) := by
  have hz : sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A L T=0 →
      ∀ t ∈ Icc 0 T, r t=0 := by
    intro hB
    exact source_tracking_zero tau pre eta gammaPre gammaTildePre r kappa gamma
      c 1 delta deltaTilde A T L htau0 htime hT hc hdelta hA hB (by norm_num)
      hbranch hkappa hr hgamma_bound
      (fun k hk => (hdrift k hk).mono (fun _ hu _ _ => hu)) heta hgammaPre hgammaTildePre
      (fun k hk _ => hjump k hk) hfinal (hdrift_final.mono (fun _ hu _ _ => hu)) hzero
  refine ⟨?_,hz⟩
  have htimes : ∀ i ≤ L, 0 ≤ tau i := by
    intro i hi
    rw [← htau0]
    exact time_mono_prefix tau L (fun k hk => (htime k hk).le) 0 i (Nat.zero_le _) hi
  have hT0 : 0 ≤ T := (htimes L le_rfl).trans hT
  have hB0 := sourceCurvatureEnvelopeSup_nonneg kappa tau eta delta deltaTilde A L T
    hT0 hdelta hA hkappa (fun i hi => htimes (i+1) (Nat.succ_le_of_lt hi)) heta
  rcases eq_or_lt_of_le hB0 with hB | hB
  · intro t ht
    rw [hz hB.symm t ht]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le
      (show 0 ≤ jumpAmplification (sourceJumpError A eta) L from
        Finset.prod_nonneg (fun i hi => by
          have he := sourceJumpError_nonneg A eta i hA (heta i (Finset.mem_range.mp hi))
          linarith)))
      (sourceCurvatureEnvelope_nonneg kappa tau eta delta deltaTilde A L t hdelta hA ht.1 heta)
  · exact (source_tracking_bound tau pre eta gammaPre gammaTildePre r kappa gamma
      c _ delta deltaTilde A T L htau0 htime hT hc hdelta hA hB rfl hsmall
      hbranch hkappa hgamma hr hgamma_bound
      (fun k hk => (hdrift k hk).mono (fun _ hu _ _ => hu)) heta hgammaPre hgammaTildePre
      (fun k hk _ => hjump k hk) hfinal (hdrift_final.mono (fun _ hu _ _ => hu)) hzero).2
end PaperFormalization.Manuscript
