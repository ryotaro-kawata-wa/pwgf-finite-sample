import PaperFormalization.Manuscript.SourceScheduledTrackingClosure

/-! # Canonical paths equal the original source branch solutions
M13s verified unit; see CODEX_HANDOFF_M13S.md. The hypotheses below are the actual vector ODE, the original
initial condition and prescribed finite coupling update. They contain no scalar
comparison, law identification or moment/concentration conclusion. Induction
supplies the visited-lifetime witness used by the final theorem and identifies
both pretraces and every right value with the supplied source solutions.
-/
open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal Topology ProbabilityTheory Matrix.Norms.Frobenius
namespace PaperFormalization.Manuscript
variable {W : Type*} [MeasurableSpace W] {N d : Nat}
variable {H : Nat -> Type*} [∀ m, NormedAddCommGroup (H m)]
  [∀ m, InnerProductSpace Real (H m)] [∀ m, CompleteSpace (H m)]

variable (mu0 : Measure (EuclideanSpace Real (Fin d)))
  (c p alpha : Real) (phi : ∀ m, EuclideanSpace Real (Fin d) -> H m)
  (G : lp H 2 -> Real) (U : Set (lp H 2)) (hU : IsOpen U)
  (hDomains : SourceAllMomentDomains (sourceWeightedFeatureMap c p phi) alpha U)
  (hG : ContDiffOn Real 2 G U) (hN : 0 < N)
  (tau eta : Nat -> Real) (flowX flowY field)

/-- The finite-history version of the already verified tower-step identity. -/
theorem sourceActualFinitePost_finite_step
    (J k : Nat) (hk : k < J) (h : Fin J -> W × SourceStepNormal N d) (u : SourceFiniteConfiguration N d) :
    let post := sourceActualFinitePost mu0 c p alpha phi G U hU hDomains hG hN tau eta flowX flowY field
    let past := sourceFinitePrefix h k hk.le
    let pop := sourcePopulationPrefix past
    let pre := sourceCoupledBranch post flowX flowY k past u (tau (k+1))
    let v := WithLp.toLp 2 (fun i => field k pop (h ⟨k,hk⟩).1 (pre.2 i))
    post (k+1) (sourceFinitePrefix h (k+1) (Nat.succ_le_of_lt hk)) u =
      sourceCanonicalCoupledStep (sourceEmpiricalKernelFactor c p phi G)
        (source_empirical_factor_hermitian_all_domains c p alpha phi G U hU hDomains hG hN)
        (eta k) (sourceActualCovarianceVersion mu0 c p phi G U tau eta flowY field k pop pre.2)
        pre.1 pre.2 v (h ⟨k,hk⟩).2 := by
  rfl

/-- A primitive raw branch specification. The reference array is the original
characteristic; only the empirical branch trajectory is supplied. -/
def SourceRawEmpiricalSchedule
    (J : Nat) (T : Real) (h : Fin J -> W × SourceStepNormal N d) (u : SourceFiniteConfiguration N d)
    (XB : Nat -> Real -> SourceFiniteConfiguration N d) : Prop :=
    XB 0 (tau 0) = u ∧
    (∀ k, k ≤ J -> ContinuousOn (XB k) (Icc (tau k) (if k < J then tau (k+1) else T))) ∧
    (∀ k, k ≤ J -> ∀ t, t ∈ Ioo (tau k) (if k < J then tau (k+1) else T) ->
      HasDerivAt (XB k) (sourceExactEmpiricalDrift c p phi G (XB k t)) t) ∧
    (∀ k (hk : k < J),
      let pop := sourcePopulationPrefix (sourceFinitePrefix h k hk.le)
      let Y := WithLp.toLp 2 (fun i => sourceReferencePre tau flowY (sourcePopulationFieldJump eta field) k pop (u i))
      let v := WithLp.toLp 2 (fun i => field k pop (h ⟨k,hk⟩).1 (Y i))
      XB (k+1) (tau (k+1)) =
        (sourceCanonicalCoupledStep (sourceEmpiricalKernelFactor c p phi G)
          (source_empirical_factor_hermitian_all_domains c p alpha phi G U hU hDomains hG hN)
          (eta k) (sourceActualCovarianceVersion mu0 c p phi G U tau eta flowY field k pop Y)
          (XB k (tau (k+1))) Y v (h ⟨k,hk⟩).2).1)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 6000000 in
/-- Source vector equations and actual updates give BOTH the canonical lifetime
condition and exact agreement with the source branches. No existence theorem
for all initial states is used. -/
theorem source_canonical_schedule_agrees_with_source
    (hf : ContDiff Real 1 (sourceExactEmpiricalDrift (N := N) c p phi G))
    (J : Nat) (T : Real) (htime : ∀ k, k < J -> tau k < tau (k+1)) (hT : tau J ≤ T)
    (h : Fin J -> W × SourceStepNormal N d) (u : SourceFiniteConfiguration N d)
    (XB : Nat -> Real -> SourceFiniteConfiguration N d)
    (hRaw : SourceRawEmpiricalSchedule mu0 c p alpha phi G U hU hDomains hG hN tau eta flowY field J T h u XB) :
    let flow := sourceCanonicalEmpiricalFlow (N := N) c p phi G tau J T htime hT
    let post := sourceActualFinitePost mu0 c p alpha phi G U hU hDomains hG hN tau eta flow flowY field
    SourceVisitedEmpiricalSolutions (sourceExactEmpiricalDrift c p phi G) post tau J T h u ∧
    ∀ k, k ≤ J -> EqOn
      (fun t => (sourceFiniteHorizonBranch post flow flowY J h u k t).1) (XB k)
      (Icc (tau k) (if k < J then tau (k+1) else T)) := by
  let flow := sourceCanonicalEmpiricalFlow (N := N) c p phi G tau J T htime hT
  let post := sourceActualFinitePost mu0 c p alpha phi G U hU hDomains hG hN tau eta flow flowY field
  have hFlowEq (k : Nat) (hk : k ≤ J) :
      EqOn (fun t => flow k t (XB k (tau k))) (XB k)
        (Icc (tau k) (if k < J then tau (k+1) else T)) := by
    have hh := (sourceCanonicalEmpiricalFlow_eq_source c p phi G hf tau J T htime hT k (XB k)
      (by simpa only [sourceHorizonEndpoint_used tau J T k hk] using hRaw.2.1 k hk)
      (by simpa only [sourceHorizonEndpoint_used tau J T k hk] using hRaw.2.2.1 k hk)).2
    simpa only [sourceHorizonEndpoint_used tau J T k hk] using hh
  have hStarts : ∀ k (hk : k ≤ J), (post k (sourceFinitePrefix h k hk) u).1 = XB k (tau k) := by
    intro k
    induction k with
    | zero =>
      intro hk
      exact hRaw.1.symm
    | succ k ih =>
      intro hk
      have hkJ : k < J := Nat.lt_of_succ_le hk
      have hprev := ih hkJ.le
      have hx : (sourceCoupledBranch post flow flowY k (sourceFinitePrefix h k hkJ.le) u (tau (k+1))).1 = XB k (tau (k+1)) := by
        change flow k (tau (k+1)) (post k (sourceFinitePrefix h k hkJ.le) u).1 = _
        rw [hprev]
        exact hFlowEq k hkJ.le (by simpa only [if_pos hkJ] using ⟨(htime k hkJ).le,le_rfl⟩)
      have hy : (sourceCoupledBranch post flow flowY k (sourceFinitePrefix h k hkJ.le) u (tau (k+1))).2 =
          WithLp.toLp 2 (fun i => sourceReferencePre tau flowY (sourcePopulationFieldJump eta field) k
            (sourcePopulationPrefix (sourceFinitePrefix h k hkJ.le)) (u i)) := by
        ext i j
        exact congrArg (fun x => x j) (sourceActualFiniteBranch_reference mu0 c p alpha phi G U hU hDomains hG hN
          tau eta flow flowY field k (sourceFinitePrefix h k hkJ.le) u (tau (k+1)) i)
      have hs := congrArg Prod.fst (sourceActualFinitePost_finite_step mu0 c p alpha phi G U hU hDomains hG hN
        tau eta flow flowY field J k hkJ h u)
      rw [hx,hy] at hs
      exact hs.trans (hRaw.2.2.2 k hkJ).symm
  constructor
  . intro k hk
    exact ⟨XB k,(hStarts k hk).symm,hRaw.2.1 k hk,hRaw.2.2.1 k hk⟩
  . intro k hk t ht
    change (sourceFiniteHorizonBranch post flow flowY J h u k t).1 = XB k t
    rw [sourceFiniteHorizonBranch_eq post flow flowY J h u k hk]
    change flow k t (post k (sourceFinitePrefix h k hk) u).1 = XB k t
    rw [hStarts k hk]
    exact hFlowEq k hk ht

/-- Closed-branch agreement gives the same full right-continuous path on [0,T]. -/
theorem source_glued_paths_eq_of_closed_agreement
    {E : Type*} (tau : Nat -> Real) (J : Nat) (T : Real)
    (htau0 : tau 0 = 0) (htime : ∀ k, k < J -> tau k < tau (k+1))
    (F G : Nat -> Real -> E)
    (hFG : ∀ k, k ≤ J -> EqOn (F k) (G k) (Icc (tau k) (if k < J then tau (k+1) else T))) :
    EqOn (sourceGlue tau J F) (sourceGlue tau J G) (Icc 0 T) := by
  intro t ht
  let k := Piecewise.jumpCount tau J t
  have hk := Piecewise.jumpCount_le tau J t
  have hleft := Piecewise.time_jumpCount_le tau J t (fun k hk => (htime k hk).le) (by simpa [htau0] using ht.1)
  have hright : t ≤ if k < J then tau (k+1) else T := by
    split_ifs with hkJ
    . exact (Piecewise.lt_next_jump tau J t (fun k hk => (htime k hk).le) hkJ).le
    . exact ht.2
  exact hFG k hk ⟨hleft,hright⟩
end PaperFormalization.Manuscript
