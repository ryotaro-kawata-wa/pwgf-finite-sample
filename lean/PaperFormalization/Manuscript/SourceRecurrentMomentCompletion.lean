import PaperFormalization.Manuscript.SourceRecurrentExchangeability
import PaperFormalization.Manuscript.SourceMomentLeftTrace

/-! # First-particle right-path moments give every particle and closed branch label
M13s verified unit; see CODEX_HANDOFF_M13S.md. Exchangeability is a law identity, not independence. Left
endpoints use the actual closed representative and Fatou with the SAME original
all-real-order moment scale. At the last singleton branch the right value is
used directly; no positive terminal length is assumed.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ProbabilityTheory
namespace PaperFormalization.Manuscript

/-- Every used closed-branch time belongs to the original horizon. -/
theorem source_closed_time_in_horizon (tau : Nat -> Real) (J : Nat) (T : Real)
    (htau0 : tau 0 = 0) (htime : forall k, k < J -> tau k < tau (k+1)) (hT : tau J ≤ T)
    (k : Nat) (hk : k ≤ J) (t : Real)
    (ht : t ∈ Icc (tau k) (if k < J then tau (k+1) else T)) : t ∈ Icc 0 T := by
  have hzero := Piecewise.time_mono_prefix tau J (fun k hk => (htime k hk).le) 0 k (Nat.zero_le k) hk
  rw [htau0] at hzero
  refine ⟨hzero.trans ht.1,?_⟩
  by_cases hkJ : k < J
  . have hend := Piecewise.time_mono_prefix tau J (fun k hk => (htime k hk).le) (k+1) J
      (Nat.succ_le_of_lt hkJ) le_rfl
    exact (show t ≤ tau (k+1) by simpa only [if_pos hkJ] using ht.2).trans (hend.trans hT)
  . simpa only [if_neg hkJ] using ht.2

/-- A closed representative has the same moment class at its old endpoint as
its interior, with no assumption about the post-jump value. -/
theorem source_closed_branch_moment_from_right
    {S E : Type*} [MeasurableSpace S] [MeasurableSpace E]
    [NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E]
    (rho : Measure S) [IsProbabilityMeasure rho]
    (tau : Nat -> Real) (J : Nat) (T alpha K0 : Real)
    (htau0 : tau 0 = 0) (htime : forall k, k < J -> tau k < tau (k+1)) (hT : tau J ≤ T)
    (X : Nat -> S -> Real -> E) (hX : forall k t, Measurable (fun z => X k z t))
    (hcont : forall k, k ≤ J -> ∀ᵐ z ∂ rho,
      ContinuousOn (X k z) (Icc (tau k) (if k < J then tau (k+1) else T)))
    (hfirst : ∀ t ∈ Icc 0 T,
      rho.map (fun z => sourceGlue tau J (fun k => X k z) t) ∈ sourceMomentClass alpha K0)
    (k : Nat) (hk : k ≤ J) (t : Real)
    (ht : t ∈ Icc (tau k) (if k < J then tau (k+1) else T)) :
    rho.map (fun z => X k z t) ∈ sourceMomentClass alpha K0 := by
  by_cases hkJ : k < J
  . by_cases hend : t = tau (k+1)
    . subst t
      have hmeas (s : Real) : Measurable (fun z => sourceGlue tau J (fun l => X l z) s) := by
        exact hX _ s
      have hlim : ∀ᵐ z ∂ rho, Tendsto (sourceGlue tau J (fun l => X l z))
          (nhdsWithin (tau (k+1)) (Iio (tau (k+1)))) (nhds (X k z (tau (k+1)))) := by
        filter_upwards [hcont k hk] with z hz
        exact (sourceGlue_traces tau J (fun l => X l z) htime k hkJ
          (by simpa only [if_pos hkJ] using hz)).2
      exact (sourceMomentClass_map_leftTrace rho alpha K0 (tau k) (tau (k+1)) (htime k hkJ)
        (fun s z => sourceGlue tau J (fun l => X l z) s) (fun z => X k z (tau (k+1)))
        (fun s _ => (hmeas s).aestronglyMeasurable)
        (fun s hs => hfirst s (source_closed_time_in_horizon tau J T htau0 htime hT k hk s
          (by simpa only [if_pos hkJ] using Ioo_subset_Icc_self hs))) hlim).2
    . have hlt : t < tau (k+1) := lt_of_le_of_ne (by simpa only [if_pos hkJ] using ht.2) hend
      have heq : (fun z => sourceGlue tau J (fun l => X l z) t) = (fun z => X k z t) := by
        funext z
        exact sourceGlue_on_branch tau J (fun l => X l z) htime k hk t ht.1 (fun _ => hlt)
      rw [<- heq]
      exact hfirst t (source_closed_time_in_horizon tau J T htau0 htime hT k hk t ht)
  . have heq : (fun z => sourceGlue tau J (fun l => X l z) t) = (fun z => X k z t) := by
      funext z
      exact sourceGlue_on_branch tau J (fun l => X l z) htime k hk t ht.1 (fun h => (hkJ h).elim)
    rw [<- heq]
    exact hfirst t (source_closed_time_in_horizon tau J T htau0 htime hT k hk t ht)

variable {O W : Type*} [MeasurableSpace O] [MeasurableSpace W] {N d : Nat}

/-- Complete all-particle/all-label moments for the actual fixed recurrence.
The only moment hypothesis is on ONE particle of the two RIGHT processes. -/
theorem sourceFinalBranch_all_closed_moments
    (post : SourcePostMap W N d) (flowX flowY)
    (hpost : forall n, Measurable (fun z : (Fin n -> W × SourceStepNormal N d) × SourceFiniteConfiguration N d => post n z.1 z.2))
    (hX : forall n t, Measurable (flowX n t))
    (hY : forall n t, Measurable (fun z : (Fin n -> W) × EuclideanSpace Real (Fin d) => flowY n z.1 t z.2))
    (hpostPerm : forall s n h u, post n (sourcePackedPermute s h) (sourceParticlePermute s u) = sourcePairPermute s (post n h u))
    (hXPerm : forall s n t x, flowX n t (sourceParticlePermute s x) = sourceParticlePermute s (flowX n t x))
    (nu : Measure O) [IsProbabilityMeasure nu]
    (mu0 : Measure (EuclideanSpace Real (Fin d))) [IsProbabilityMeasure mu0]
    (initial : O -> SourceFiniteConfiguration N d) (innovation : Nat -> O -> W)
    (hinit : Measurable initial) (hInnovation : forall k, Measurable (innovation k))
    (hiid : iIndepFun (fun i o => initial o i) nu)
    (hind : IndepFun (fun o k => innovation k o) (fun o i => initial o i) nu)
    (hlaw : forall i, nu.map (fun o => initial o i) = mu0)
    (tau : Nat -> Real) (J : Nat) (T alpha K0 : Real)
    (htau0 : tau 0 = 0) (htime : forall k, k < J -> tau k < tau (k+1)) (hT : tau J ≤ T)
    (i0 : Fin N)
    (hcont : forall c k, k ≤ J -> ∀ᵐ z ∂ sourceAuxiliaryMeasure nu (stdGaussian (SourceStepNormal N d)) J,
      ContinuousOn (fun t => sourcePairCloud c (sourceFinalBranch post flowX flowY initial innovation J z k t) i0)
        (Icc (tau k) (if k < J then tau (k+1) else T)))
    (hfirst : forall c, ∀ t ∈ Icc 0 T,
      (sourceAuxiliaryMeasure nu (stdGaussian (SourceStepNormal N d)) J).map
        (fun z => sourcePairCloud c (sourceFinalRight post flowX flowY tau initial innovation J z t) i0)
          ∈ sourceMomentClass alpha K0) :
    forall c i k, k ≤ J -> ∀ t ∈ Icc (tau k) (if k < J then tau (k+1) else T),
      (sourceAuxiliaryMeasure nu (stdGaussian (SourceStepNormal N d)) J).map
        (fun z => sourcePairCloud c (sourceFinalBranch post flowX flowY initial innovation J z k t) i)
          ∈ sourceMomentClass alpha K0 := by
  let law := sourceAuxiliaryMeasure nu (stdGaussian (SourceStepNormal N d)) J
  have hm k t := sourceFinalBranch_measurable post flowX flowY hpost hX hY initial innovation hinit hInnovation J k t
  have hcoord c i k t : Measurable (fun z => sourcePairCloud c
      (sourceFinalBranch post flowX flowY initial innovation J z k t) i) :=
    ((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 _)).comp ((sourcePairCloud_measurable c).comp (hm k t))
  intro c i k hk t ht
  have heq := source_pair_marginals_of_permutation law _ (hm k t)
    (fun s => sourceFinalBranch_exchangeable post flowX flowY hpost hX hY hpostPerm hXPerm
      nu mu0 initial innovation hinit hInnovation hiid hind hlaw J k t s) c i i0
  rw [heq]
  apply source_closed_branch_moment_from_right law tau J T alpha K0 htau0 htime hT
    (fun k z t => sourcePairCloud c (sourceFinalBranch post flowX flowY initial innovation J z k t) i0)
    (fun k t => hcoord c i0 k t) (hcont c) _ k hk t ht
  intro s hs
  have h := hfirst c s hs
  simpa only [sourceFinalRight,sourceFiniteHorizonPath,sourceFinalBranch,sourcePairCloud,sourceGlue] using h
end PaperFormalization.Manuscript
