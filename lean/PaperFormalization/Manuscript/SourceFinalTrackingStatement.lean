import PaperFormalization.Manuscript.SourceFinalReferenceTransport
import PaperFormalization.Manuscript.SourceActualTracking

/-! # Literal final tracking statement and its original path restriction
M13s verified unit; see CODEX_HANDOFF_M13S.md. These definitions only name the final conclusion and smallness
condition. They are not independent hypotheses of the stochastic model.
The pretrace envelope uses the strict prefix k, not k+1.
-/
open MeasureTheory Set Filter
open scoped BigOperators NNReal Topology
namespace PaperFormalization.Manuscript
open Continuous Piecewise
variable {N d : Nat}

def sourceScheduleLeft (tau : Nat -> Real) (J : Nat) (j : Fin (J+1)) := tau j

def sourceScheduleRight (tau : Nat -> Real) (J : Nat) (T : Real) (j : Fin (J+1)) :=
  if j.val < J then tau (j.val+1) else T

theorem sourceSchedule_ordered (tau : Nat -> Real) (J : Nat) (T : Real)
    (htime : ∀ k, k < J -> tau k < tau (k+1)) (hT : tau J ≤ T) :
    ∀ j, sourceScheduleLeft tau J j ≤ sourceScheduleRight tau J T j := by
  intro j
  by_cases hj : j.val < J
  . simpa only [sourceScheduleLeft,sourceScheduleRight,if_pos hj] using (htime j hj).le
  . have he : j.val = J := by omega
    simpa [sourceScheduleLeft,sourceScheduleRight,he] using hT

/-- The lengths telescope exactly, including a singleton final branch. -/
theorem sourceSchedule_total_length (tau : Nat -> Real) (J : Nat) (T : Real) (htau : tau 0 = 0) :
    (∑ j : Fin (J+1), (sourceScheduleRight tau J T j-sourceScheduleLeft tau J j)) = T := by
  classical
  rw [Fin.sum_univ_castSucc]
  have hterms : (∑ j : Fin J, (sourceScheduleRight tau J T j.castSucc-sourceScheduleLeft tau J j.castSucc)) =
      tau J - tau 0 := by
    simp only [sourceScheduleRight,sourceScheduleLeft,Fin.val_castSucc,if_pos (Fin.isLt _)]
    change (∑ j : Fin J, (tau (j.val+1)-tau j.val)) = tau J-tau 0
    exact (Fin.sum_univ_eq_sum_range (fun n => tau (n+1)-tau n) J).trans
      (Finset.sum_range_sub tau J)
  rw [hterms]
  simp only [sourceScheduleRight,sourceScheduleLeft,Fin.val_last,lt_self_iff_false,if_false,htau]
  ring

/-- The original third-to-second moment path restriction, completed harmlessly
at zero discrepancy. No probability estimate for this restriction is asserted. -/
def SourceRightAntiSpikiness (X Y : Real -> SourceFiniteConfiguration N d) (T A_sp : Real) : Prop :=
  ∀ t, t ∈ Icc 0 T ->
    (N : Real)⁻¹ * ∑ i : Fin N, norm ((X t-Y t) i)^3 ≤
      A_sp * (norm (X t-Y t)/Real.sqrt N)^3

theorem sourceRightAntiSpikiness_of_positive
    (X Y : Real -> SourceFiniteConfiguration N d) (T A_sp : Real) (hN : 0 < N)
    (h : ∀ t, t ∈ Icc 0 T -> 0 < norm (X t-Y t)/Real.sqrt N ->
      (N : Real)⁻¹ * ∑ i : Fin N, norm ((X t-Y t) i)^3 ≤
        A_sp * (norm (X t-Y t)/Real.sqrt N)^3) : SourceRightAntiSpikiness X Y T A_sp := by
  intro t ht
  by_cases hz : X t-Y t = 0
  . simp [hz]
  . apply h t ht
    exact div_pos (norm_pos_iff.mpr hz) (Real.sqrt_pos.mpr (by exact_mod_cast hN))

/-- Transfer the right-path restriction to the old open branches; endpoints
are measure-zero and are deliberately not confused with post-jump values. -/
theorem sourceRightAntiSpikiness_branches
    (tau : Nat -> Real) (J : Nat) (T A_sp : Real)
    (htau0 : tau 0 = 0) (htime : ∀ k, k < J -> tau k < tau (k+1)) (hT : tau J ≤ T)
    (XB YB : Nat -> Real -> SourceFiniteConfiguration N d)
    (hsp : SourceRightAntiSpikiness (sourceGlue tau J XB) (sourceGlue tau J YB) T A_sp)
    (k : Nat) (hk : k ≤ J) :
    ∀ᵐ t ∂ volume.restrict (Ioo (tau k) (if k < J then tau (k+1) else T)),
      (N : Real)⁻¹ * ∑ i : Fin N, norm ((XB k t-YB k t) i)^3 ≤
        A_sp * (norm (XB k t-YB k t)/Real.sqrt N)^3 := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hr := source_closed_time_in_horizon tau J T htau0 htime hT k hk t (Ioo_subset_Icc_self ht)
  have hn : k < J -> t < tau (k+1) := fun h => by simpa only [if_pos h] using ht.2
  have hs := hsp t hr
  rw [sourceGlue_on_branch tau J XB htime k hk t ht.1.le hn,
    sourceGlue_on_branch tau J YB htime k hk t ht.1.le hn] at hs
  exact hs

/-- Exact source nonlinear radius and smallness, with kappa on real time. -/
def SourceTrackingSmallness (kappa : Real -> Real) (tau eta : Nat -> Real)
    (J : Nat) (T delta deltaTilde A cD : Real) : Prop :=
  T * (delta + cD * (2 * jumpAmplification (sourceJumpError A eta) J *
    sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A J T)) ≤ 1/4

/-- Four original conclusions: right/post bound, zero case, strict-prefix
left/pre bound, and its zero case. The norm remains the original particle l2 norm. -/
def SourceTrackingConclusion
    (X Y : Real -> SourceFiniteConfiguration N d)
    (preX preY : Nat -> SourceFiniteConfiguration N d)
    (kappa : Real -> Real) (tau eta : Nat -> Real)
    (J : Nat) (T delta deltaTilde A : Real) : Prop :=
    (∀ t, t ∈ Icc 0 T -> norm (X t-Y t)/Real.sqrt N ≤
      Real.exp (1/4) * jumpAmplification (sourceJumpError A eta) J *
        sourceCurvatureEnvelope kappa tau eta delta deltaTilde A J t) ∧
    (sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A J T = 0 ->
      ∀ t, t ∈ Icc 0 T -> X t = Y t) ∧
    (∀ k, k < J -> norm (preX k-preY k)/Real.sqrt N ≤
      Real.exp (1/4) * jumpAmplification (sourceJumpError A eta) J *
        sourceCurvatureEnvelope kappa tau eta delta deltaTilde A k (tau (k+1))) ∧
    (sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A J T = 0 ->
      ∀ k, k < J -> preX k = preY k)
end PaperFormalization.Manuscript
