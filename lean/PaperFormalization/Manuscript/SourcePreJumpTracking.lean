import PaperFormalization.Manuscript.SourceTracking
import PaperFormalization.Manuscript.PreJumpComparison

/-! # Literal source tracking for actual pre-jump traces

The forcing envelope at jump n includes only its n earlier jumps. The full
schedule amplification is used once; the candidate jump's additive forcing is
excluded. An observation at or before the exit suffices, and the global
no-exit theorem discharges that premise. No envelope-limit assumption is used.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace PaperFormalization.Manuscript

open Continuous Piecewise

/-- The actual pre-jump trace satisfies the source bound with precisely the
strictly earlier jump prefix. The exact source smallness condition is retained. -/
theorem source_pre_jump_tracking_bound
    (tau pre eta gammaPre gammaTildePre : ℕ → ℝ) (r kappa gamma : ℝ → ℝ)
    (c R delta deltaTilde A T : ℝ) (L n : ℕ) (hn : n < L)
    (htau0 : tau 0 = 0) (htime : ∀ k < L, tau k < tau (k + 1)) (hT : tau L ≤ T)
    (hc : 0 ≤ c) (hR : 0 ≤ R) (hdelta : 0 ≤ delta) (hA : 0 ≤ A)
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
    (htExit : (tau (n + 1) : WithTop ℝ) ≤ exitTime r R T) (hzero : r 0 = 0) :
    pre n ≤ Real.exp (1 / 4) * jumpAmplification (sourceJumpError A eta) L *
      sourceCurvatureEnvelope kappa tau eta delta deltaTilde A n (tau (n + 1)) := by
  classical
  let a := sourceJumpError A eta
  let b := sourceJumpForcing A eta gammaPre gammaTildePre
  have hmono : ∀ k < L, tau k ≤ tau (k + 1) := fun k hk => (htime k hk).le
  have htimes : ∀ i ≤ L, tau i ∈ Icc 0 T := by
    intro i hi
    constructor
    · rw [← htau0]
      exact time_mono_prefix tau L hmono 0 i (Nat.zero_le _) hi
    · exact (time_mono_prefix tau L hmono i L hi le_rfl).trans hT
  have hn1 : n + 1 ≤ L := Nat.succ_le_of_lt hn
  have hkn : ∀ k < n, k < L := fun k hk => lt_trans hk hn
  have hkn1 : ∀ k < n + 1, k < L := fun k hk => lt_of_lt_of_le hk hn1
  have ha : ∀ k < L, 0 ≤ a k := fun k hk => sourceJumpError_nonneg A eta k hA (heta k hk)
  have hb : ∀ k < L, 0 ≤ b k := fun k hk =>
    sourceJumpForcing_nonneg A eta gammaPre gammaTildePre k hA (heta k hk)
  have hend := htimes (n + 1) hn1
  have hsub : uIcc 0 (tau (n + 1)) ⊆ uIcc 0 T := by
    rw [uIcc_of_le hend.1, uIcc_of_le (hend.1.trans hend.2)]
    exact Icc_subset_Icc_right hend.2
  have hkt := hkappa.mono_set hsub
  have hgt := hgamma.mono_set hsub
  have hlinear : ∀ k < n + 1, ∀ᵐ (u : ℝ) ∂volume.restrict (Ioo (tau k) (tau (k + 1))),
      (u : WithTop ℝ) < exitTime r R T →
      deriv r u ≤ -stoppedCoefficient kappa gamma c R u * r u + gamma u := by
    intro k hk
    have hkL := hkn1 k hk
    have hstart := (htimes k hkL.le).1
    have hendk := (htimes (k + 1) (Nat.succ_le_of_lt hkL)).2
    apply ae_deriv_le_stoppedCoefficient_before_exit_of_pos r kappa gamma c R T
      (tau k) (tau (k + 1)) hc hstart hendk
    · intro u hu
      exact hr u ⟨hstart.trans hu.1.le, hu.2.le.trans hendk⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      exact (hgamma_bound u ⟨hstart.trans hu.1.le, hu.2.le.trans hendk⟩).1
    · exact hpos k hkL
  have hcomp := stopped_piecewise_gronwall_pre_jump tau pre (fun k => 1 + a k) b
    r (stoppedCoefficient kappa gamma c R) gamma R T n htau0
    (fun k hk => htime k (hkn1 k hk)) (fun k hk => hbranch k (hkn1 k hk))
    (stoppedCoefficient_intervalIntegrable kappa gamma c R 0 (tau (n + 1)) hkt hgt) hgt
    hlinear (fun k hk => by linarith [ha k (hkn k hk)])
    (fun k hk => hjump k (hkn k hk)) htExit hzero
  have hmonon : ∀ k < n, tau k ≤ tau (k + 1) := fun k hk => hmono k (hkn k hk)
  have hlast : tau n ≤ tau (n + 1) := (htime n hn).le
  simp_rw [jumpWeight_eq_time_filter tau (fun k => 1 + a k) n (tau (n + 1)) _ hmonon hlast]
    at hcomp
  have hfilter : (Finset.range n).filter (fun i => tau (i + 1) ≤ tau (n + 1)) = Finset.range n := by
    apply Finset.filter_eq_self.mpr
    intro i hi
    exact time_mono_prefix tau L hmono (i + 1) (n + 1)
      (Nat.succ_le_succ (Finset.mem_range.mp hi).le) hn1
  have henv := stopped_comparison_rhs_le_envelope tau a b kappa gamma n c R delta T (tau (n + 1))
    htau0 hmonon hc hR hdelta hend.1 hend.2 hkappa hgamma hgamma_bound
    (fun k hk => ha k (hkn k hk)) (fun k hk => hb k (hkn k hk))
  rw [hfilter] at henv
  have hpre := hcomp.trans henv
  have hcurv : pre n ≤ jumpAmplification a n * Real.exp (T * (c * R + delta)) *
      curvatureEnvelope kappa tau b delta n (tau (n + 1)) := by
    simpa only [jumpAmplification, curvatureEnvelope, hfilter] using hpre
  have hsource := curvatureEnvelope_sourceJumpForcing_le kappa tau eta gammaPre gammaTildePre
    delta deltaTilde A n (tau (n + 1)) hA
    (fun k hk => heta k (hkn k hk)) (fun k hk => hgammaPre k (hkn k hk))
    (fun k hk => hgammaTildePre k (hkn k hk))
  have hsource0 := sourceCurvatureEnvelope_nonneg kappa tau eta delta deltaTilde A n (tau (n + 1))
    hdelta hA hend.1 (fun k hk => heta k (hkn k hk))
  have hJn0 : 0 ≤ jumpAmplification a n := by
    exact Finset.prod_nonneg fun k hk => by linarith [ha k (hkn k (Finset.mem_range.mp hk))]
  have hJprefix : jumpAmplification a n ≤ jumpAmplification a L :=
    jump_subproduct_le_amplification (Finset.range n) (Finset.range L) a
      (Finset.range_mono hn.le) (fun k hk => ha k (Finset.mem_range.mp hk))
  have hJL0 : 0 ≤ jumpAmplification a L := hJn0.trans hJprefix
  have hexp : Real.exp (T * (c * R + delta)) ≤ Real.exp (1 / 4) := by
    apply Real.exp_le_exp.mpr
    simpa only [add_comm delta] using hsmall
  calc
    pre n ≤ jumpAmplification a n * Real.exp (T * (c * R + delta)) *
        sourceCurvatureEnvelope kappa tau eta delta deltaTilde A n (tau (n + 1)) :=
      hcurv.trans (mul_le_mul_of_nonneg_left hsource (mul_nonneg hJn0 (Real.exp_pos _).le))
    _ ≤ jumpAmplification a L * Real.exp (T * (c * R + delta)) *
        sourceCurvatureEnvelope kappa tau eta delta deltaTilde A n (tau (n + 1)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hJprefix (Real.exp_pos _).le) hsource0
    _ ≤ jumpAmplification a L * Real.exp (1 / 4) *
        sourceCurvatureEnvelope kappa tau eta delta deltaTilde A n (tau (n + 1)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hJL0) hsource0
    _ = _ := by dsimp only [a]; ring

/-- A zero path on a nonempty open branch has zero actual pre-jump trace.
This closes the zero-envelope alternative without any smallness premise. -/
theorem pre_trace_eq_zero_of_path_zero (r : ℝ → ℝ) (a b pre : ℝ) (hab : a < b)
    (hbranch : AbsolutelyContinuousOnInterval (closedBranch r b pre) a b)
    (hzero : ∀ u ∈ Ioo a b, r u = 0) : pre = 0 := by
  have htrace := tendsto_left_of_closedBranch_ac r a b pre hab hbranch
  have heq : r =ᶠ[𝓝[<] b] (fun _ => (0 : ℝ)) := by
    have hleft : Ioi a ∈ 𝓝[<] b := nhdsWithin_le_nhds (Ioi_mem_nhds hab)
    filter_upwards [hleft, self_mem_nhdsWithin] with u hau hub
    exact hzero u ⟨hau, hub⟩
  have htrace0 : Tendsto r (𝓝[<] b) (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.congr' heq.symm
  exact tendsto_nhds_unique htrace htrace0

/-- Nonnegativity on a nonempty branch passes to its actual pre-jump trace. -/
theorem pre_trace_nonneg (r : ℝ → ℝ) (a b pre : ℝ) (hab : a < b)
    (hbranch : AbsolutelyContinuousOnInterval (closedBranch r b pre) a b)
    (hnonneg : ∀ u ∈ Ioo a b, 0 ≤ r u) : 0 ≤ pre := by
  apply ge_of_tendsto (tendsto_left_of_closedBranch_ac r a b pre hab hbranch)
  have hleft : Ioi a ∈ 𝓝[<] b := nhdsWithin_le_nhds (Ioi_mem_nhds hab)
  filter_upwards [hleft, self_mem_nhdsWithin] with u hau hub
  exact hnonneg u ⟨hau, hub⟩

end PaperFormalization.Manuscript
