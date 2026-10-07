import PaperFormalization.Manuscript.SourceEnvelope
import PaperFormalization.Manuscript.ZeroForcingTracking

/-! # The deterministic tracking theorem in the manuscript's literal source notation

The response and its supremum are now defined quantities, not supplied majorants.
Particle-model differential and Gaussian jump estimates remain explicit inputs.
The conditional probability of those inputs is not asserted here.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PaperFormalization.Manuscript

open Continuous Piecewise

/-- With a positive actual source-envelope supremum, the source smallness condition
implies no exit and the source tracking bound over the entire observation horizon. -/
theorem source_tracking_bound
    (tau pre eta gammaPre gammaTildePre : ℕ → ℝ) (r kappa gamma : ℝ → ℝ)
    (c R delta deltaTilde A T : ℝ) (L : ℕ)
    (htau0 : tau 0 = 0) (htime : ∀ k < L, tau k < tau (k + 1)) (hT : tau L ≤ T)
    (hc : 0 ≤ c) (hdelta : 0 ≤ delta) (hA : 0 ≤ A)
    (hBstar : 0 < sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A L T)
    (hR : R = 2 * jumpAmplification (sourceJumpError A eta) L *
      sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A L T)
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
    (heta : ∀ k < L, 0 ≤ eta k)
    (hgammaPre : ∀ k < L, gammaPre k ≤ delta)
    (hgammaTildePre : ∀ k < L, gammaTildePre k ≤ deltaTilde)
    (hjump : ∀ k < L, (tau (k + 1) : WithTop ℝ) ≤ exitTime r R T →
      r (tau (k + 1)) ≤ (1 + sourceJumpError A eta k) * pre k +
        sourceJumpForcing A eta gammaPre gammaTildePre k)
    (hfinal : AbsolutelyContinuousOnInterval r (tau L) T)
    (hpos_final : ∀ᵐ (u : ℝ) ∂volume.restrict (Ioo (tau L) T),
      (u : WithTop ℝ) < exitTime r R T → 0 < r u →
      deriv r u ≤ -kappa u * r u + c * (r u) ^ 2 + gamma u * r u + gamma u)
    (hzero : r 0 = 0) :
    exitTime r R T = ⊤ ∧
      ∀ t ∈ Icc 0 T, r t ≤ Real.exp (1 / 4) * jumpAmplification (sourceJumpError A eta) L *
        sourceCurvatureEnvelope kappa tau eta delta deltaTilde A L t := by
  have hmono : ∀ k < L, tau k ≤ tau (k + 1) := fun k hk => (htime k hk).le
  have htau : ∀ i < L, 0 ≤ tau (i + 1) := by
    intro i hi
    rw [← htau0]
    exact time_mono_prefix tau L hmono 0 (i + 1) (Nat.zero_le _) (Nat.succ_le_of_lt hi)
  apply nonlinear_tracking_bound tau pre (sourceJumpError A eta)
    (sourceJumpForcing A eta gammaPre gammaTildePre) r kappa gamma
    (sourceCurvatureEnvelope kappa tau eta delta deltaTilde A L)
    c R delta T (sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A L T) L
    htau0 htime hT hc hdelta hBstar hR hsmall hbranch hkappa hgamma hr hgamma_bound hpos
    (fun k hk => sourceJumpError_nonneg A eta k hA (heta k hk))
    (fun k hk => sourceJumpForcing_nonneg A eta gammaPre gammaTildePre k hA (heta k hk))
    hjump hfinal hpos_final hzero
  · intro t _
    exact curvatureEnvelope_sourceJumpForcing_le kappa tau eta gammaPre gammaTildePre
      delta deltaTilde A L t hA heta hgammaPre hgammaTildePre
  · intro t ht
    exact sourceCurvatureEnvelope_le_sup kappa tau eta delta deltaTilde A L t T
      hdelta hA hkappa htau heta ht

/-- A zero actual source-envelope supremum gives zero discrepancy everywhere.
The localization radius is positive and no smallness condition is required. -/
theorem source_tracking_zero
    (tau pre eta gammaPre gammaTildePre : ℕ → ℝ) (r kappa gamma : ℝ → ℝ)
    (c R delta deltaTilde A T : ℝ) (L : ℕ)
    (htau0 : tau 0 = 0) (htime : ∀ k < L, tau k < tau (k + 1)) (hT : tau L ≤ T)
    (hc : 0 ≤ c) (hdelta : 0 ≤ delta) (hA : 0 ≤ A)
    (hBstar : sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A L T = 0)
    (hR : 0 < R)
    (hbranch : ∀ k < L, AbsolutelyContinuousOnInterval
      (closedBranch r (tau (k + 1)) (pre k)) (tau k) (tau (k + 1)))
    (hkappa : IntervalIntegrable kappa volume 0 T)
    (hr : ∀ u ∈ Icc 0 T, 0 ≤ r u)
    (hgamma_bound : ∀ u ∈ Icc 0 T, 0 ≤ gamma u ∧ gamma u ≤ delta)
    (hpos : ∀ k < L, ∀ᵐ (u : ℝ) ∂volume.restrict (Ioo (tau k) (tau (k + 1))),
      (u : WithTop ℝ) < exitTime r R T → 0 < r u →
      deriv r u ≤ -kappa u * r u + c * (r u) ^ 2 + gamma u * r u + gamma u)
    (heta : ∀ k < L, 0 ≤ eta k)
    (hgammaPre : ∀ k < L, gammaPre k ≤ delta)
    (hgammaTildePre : ∀ k < L, gammaTildePre k ≤ deltaTilde)
    (hjump : ∀ k < L, (tau (k + 1) : WithTop ℝ) ≤ exitTime r R T →
      r (tau (k + 1)) ≤ (1 + sourceJumpError A eta k) * pre k +
        sourceJumpForcing A eta gammaPre gammaTildePre k)
    (hfinal : AbsolutelyContinuousOnInterval r (tau L) T)
    (hpos_final : ∀ᵐ (u : ℝ) ∂volume.restrict (Ioo (tau L) T),
      (u : WithTop ℝ) < exitTime r R T → 0 < r u →
      deriv r u ≤ -kappa u * r u + c * (r u) ^ 2 + gamma u * r u + gamma u)
    (hzero : r 0 = 0) :
    ∀ t ∈ Icc 0 T, r t = 0 := by
  by_cases hTpos : 0 < T
  · have hmono : ∀ k < L, tau k ≤ tau (k + 1) := fun k hk => (htime k hk).le
    have htimes : ∀ i ≤ L, tau i ∈ Icc 0 T := by
      intro i hi
      constructor
      · rw [← htau0]
        exact time_mono_prefix tau L hmono 0 i (Nat.zero_le _) hi
      · exact (time_mono_prefix tau L hmono i L hi le_rfl).trans hT
    obtain ⟨hdelta0, hb0⟩ := zero_forcing_of_zero_source_sup
      kappa tau eta gammaPre gammaTildePre delta deltaTilde A L T hTpos hdelta hA hkappa
      (fun i hi => (htimes (i + 1) (Nat.succ_le_of_lt hi)).1)
      (fun i hi => (htimes (i + 1) (Nat.succ_le_of_lt hi)).2)
      heta hgammaPre hgammaTildePre hBstar
    have hgamma0 : ∀ u ∈ Icc 0 T, gamma u = 0 := by
      intro u hu
      have hg := hgamma_bound u hu
      rw [hdelta0] at hg
      exact le_antisymm hg.2 hg.1
    have hreduce : ∀ a e : ℝ, 0 ≤ a → e ≤ T →
        (∀ᵐ (u : ℝ) ∂volume.restrict (Ioo a e),
          (u : WithTop ℝ) < exitTime r R T → 0 < r u →
          deriv r u ≤ -kappa u * r u + c * (r u) ^ 2 + gamma u * r u + gamma u) →
        ∀ᵐ (u : ℝ) ∂volume.restrict (Ioo a e),
          (u : WithTop ℝ) < exitTime r R T → 0 < r u →
          deriv r u ≤ -kappa u * r u + c * (r u) ^ 2 := by
      intro a e ha he hp
      filter_upwards [ae_restrict_mem measurableSet_Ioo, hp] with u hu hpu
      simpa only [hgamma0 u ⟨ha.trans hu.1.le, hu.2.le.trans he⟩, zero_mul, add_zero]
        using hpu
    apply zero_forcing_tracking tau pre (fun k => 1 + sourceJumpError A eta k)
      r kappa c R T L htau0 htime hT hc hR hbranch hkappa hr
      (fun k hk => hreduce (tau k) (tau (k + 1)) (htimes k hk.le).1
        (htimes (k + 1) (Nat.succ_le_of_lt hk)).2 (hpos k hk))
      (fun k hk => by linarith [sourceJumpError_nonneg A eta k hA (heta k hk)])
      (fun k hk hstop => by simpa only [hb0 k hk, add_zero] using hjump k hk hstop)
      hfinal (hreduce (tau L) T (htimes L le_rfl).1 le_rfl hpos_final) hzero
  · intro t ht
    have ht0 : t = 0 := le_antisymm (ht.2.trans (le_of_not_gt hTpos)) ht.1
    simpa only [ht0] using hzero

end PaperFormalization.Manuscript
