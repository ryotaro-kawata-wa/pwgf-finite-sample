import PaperFormalization.Manuscript.SourceFinitePermutationEquivariance

/-! # Exchangeability of the actual recurrent particle pair under the original law
M13s verified unit; see CODEX_HANDOFF_M13S.md. The proof moves to the exact law of population innovations,
initial cloud and auxiliary normals, applies its invariant transformation, and
pulls the resulting output-law identity back. No action on the original abstract
sample space, conditional empirical independence, or localized iid is assumed.
-/
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
namespace PaperFormalization.Manuscript
variable {O W : Type*} [MeasurableSpace O] [MeasurableSpace W] {N d : Nat}

noncomputable def sourceFinalBranch (post : SourcePostMap W N d) (flowX flowY)
    (initial : O -> SourceFiniteConfiguration N d) (innovation : Nat -> O -> W)
    (J : Nat) (z : SourceAuxiliarySpace O (SourceStepNormal N d) J) (n : Nat) (t : Real) :=
  sourceFiniteHorizonBranch post flowX flowY J (sourceTowerPacked innovation J z)
    (initial (sourceAuxiliaryOriginal J z)) n t

noncomputable def sourceFinalRight (post : SourcePostMap W N d) (flowX flowY)
    (tau : Nat -> Real) (initial : O -> SourceFiniteConfiguration N d) (innovation : Nat -> O -> W)
    (J : Nat) (z : SourceAuxiliarySpace O (SourceStepNormal N d) J) (t : Real) :=
  sourceFiniteHorizonPath post flowX flowY tau J (sourceTowerPacked innovation J z)
    (initial (sourceAuxiliaryOriginal J z)) t

def sourcePairCloud (c : Fin 2)
    (x : SourceFiniteConfiguration N d × SourceFiniteConfiguration N d) : SourceFiniteConfiguration N d :=
  if c = 0 then x.1 else x.2

theorem sourcePairCloud_measurable (c : Fin 2) : Measurable (sourcePairCloud (N := N) (d := d) c) := by
  unfold sourcePairCloud
  split_ifs <;> first | exact measurable_fst | exact measurable_snd

theorem sourceFiniteHorizonBranch_measurable (post : SourcePostMap W N d) (flowX flowY)
    (hpost : forall n, Measurable (fun z : (Fin n -> W × SourceStepNormal N d) × SourceFiniteConfiguration N d => post n z.1 z.2))
    (hX : forall n t, Measurable (flowX n t))
    (hY : forall n t, Measurable (fun z : (Fin n -> W) × EuclideanSpace Real (Fin d) => flowY n z.1 t z.2))
    (J n : Nat) (t : Real) :
    Measurable (fun z : (Fin J -> W × SourceStepNormal N d) × SourceFiniteConfiguration N d =>
      sourceFiniteHorizonBranch post flowX flowY J z.1 z.2 n t) := by
  classical
  by_cases hn : n ≤ J
  . simp only [sourceFiniteHorizonBranch,dif_pos hn]
    have hp : Measurable (fun z : (Fin J -> W × SourceStepNormal N d) × SourceFiniteConfiguration N d =>
        (sourceFinitePrefix z.1 n hn,z.2)) :=
      (measurable_pi_lambda _ (fun i => (measurable_pi_apply (Fin.castLE hn i)).comp measurable_fst)).prodMk measurable_snd
    exact (sourceCoupledBranch_measurable post flowX flowY hpost hX hY n t).comp hp
  . simpa only [sourceFiniteHorizonBranch,dif_neg hn] using measurable_snd.prodMk measurable_snd

theorem sourceFinalBranch_measurable (post : SourcePostMap W N d) (flowX flowY)
    (hpost : forall n, Measurable (fun z : (Fin n -> W × SourceStepNormal N d) × SourceFiniteConfiguration N d => post n z.1 z.2))
    (hX : forall n t, Measurable (flowX n t))
    (hY : forall n t, Measurable (fun z : (Fin n -> W) × EuclideanSpace Real (Fin d) => flowY n z.1 t z.2))
    (initial : O -> SourceFiniteConfiguration N d) (innovation : Nat -> O -> W)
    (hinit : Measurable initial) (hInnovation : forall k, Measurable (innovation k))
    (J n : Nat) (t : Real) : Measurable (fun z => sourceFinalBranch post flowX flowY initial innovation J z n t) :=
  (sourceFiniteHorizonBranch_measurable post flowX flowY hpost hX hY J n t).comp
    ((sourceTowerPacked_measurable innovation hInnovation J).prodMk
      (hinit.comp (sourceAuxiliaryOriginal_measurable J)))

/-- The data-space representation keeps all population inputs but never uses
future inputs while evaluating an earlier branch. -/
noncomputable def sourceInputFinalBranch (post : SourcePostMap W N d) (flowX flowY)
    (J : Nat)
    (z : SourceAuxiliarySpace ((Nat -> W) × SourceFiniteConfiguration N d) (SourceStepNormal N d) J)
    (n : Nat) (t : Real) :=
  sourceFinalBranch post flowX flowY Prod.snd (fun k (x : (Nat -> W) × SourceFiniteConfiguration N d) => x.1 k) J z n t

theorem sourceInputFinalBranch_observation (post : SourcePostMap W N d) (flowX flowY)
    (initial : O -> SourceFiniteConfiguration N d) (innovation : Nat -> O -> W)
    (J : Nat) (z : SourceAuxiliarySpace O (SourceStepNormal N d) J) (n : Nat) (t : Real) :
    sourceInputFinalBranch post flowX flowY J
      (sourceAuxiliaryHistory (fun o => ((fun k => innovation k o),initial o)) J z) n t =
      sourceFinalBranch post flowX flowY initial innovation J z n t := by
  unfold sourceInputFinalBranch sourceFinalBranch
  rw [sourceAuxiliaryHistory_original]
  congr 1
  funext i
  apply Prod.ext
  . simp only [sourceTowerPacked,sourceAuxiliaryHistory_original]
  . exact congrFun (sourceAuxiliaryArray_history _ J z) i

/-- Equivariance is applied to the whole history, including every auxiliary. -/
theorem sourceInputFinalBranch_transform (post : SourcePostMap W N d) (flowX flowY)
    (s : Equiv.Perm (Fin N))
    (hpost : forall n h u, post n (sourcePackedPermute s h) (sourceParticlePermute s u) = sourcePairPermute s (post n h u))
    (hX : forall n t x, flowX n t (sourceParticlePermute s x) = sourceParticlePermute s (flowX n t x))
    (J : Nat)
    (z : SourceAuxiliarySpace ((Nat -> W) × SourceFiniteConfiguration N d) (SourceStepNormal N d) J)
    (n : Nat) (t : Real) :
    sourceInputFinalBranch post flowX flowY J
      (sourceAuxiliaryTransform (sourceInputPermute s)
        (sourceEuclideanPermute (sourceParticleIndexPermute s)) J z) n t =
      sourcePairPermute s (sourceInputFinalBranch post flowX flowY J z n t) := by
  unfold sourceInputFinalBranch sourceFinalBranch
  rw [sourceAuxiliaryTransform_original]
  have hp : sourceTowerPacked (fun k (x : (Nat -> W) × SourceFiniteConfiguration N d) => x.1 k) J
      (sourceAuxiliaryTransform (sourceInputPermute s) (sourceEuclideanPermute (sourceParticleIndexPermute s)) J z) =
        sourcePackedPermute s (sourceTowerPacked (fun k (x : (Nat -> W) × SourceFiniteConfiguration N d) => x.1 k) J z) := by
    funext i
    apply Prod.ext
    . simp only [sourceTowerPacked,sourceAuxiliaryTransform_original,sourceInputPermute,sourcePackedPermute]
    . exact sourceAuxiliaryTransform_array _ _ J z i
  rw [hp]
  exact sourceFiniteHorizonBranch_permute post flowX flowY s hpost hX J _ _ n t

set_option maxHeartbeats 3000000 in
/-- The actual final branch pair has permutation-invariant law. -/
theorem sourceFinalBranch_exchangeable
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
    (J n : Nat) (t : Real) (s : Equiv.Perm (Fin N)) :
    let law := sourceAuxiliaryMeasure nu (stdGaussian (SourceStepNormal N d)) J
    law.map (fun z => sourcePairPermute s (sourceFinalBranch post flowX flowY initial innovation J z n t)) =
      law.map (fun z => sourceFinalBranch post flowX flowY initial innovation J z n t) := by
  let data := fun o => ((fun k => innovation k o),initial o)
  have henv := measurable_pi_lambda _ hInnovation
  have hd : Measurable data := henv.prodMk hinit
  let normal := stdGaussian (SourceStepNormal N d)
  let rho := nu.map data
  letI : IsProbabilityMeasure rho := Measure.isProbabilityMeasure_map hd.aemeasurable
  let obs := sourceAuxiliaryHistory (A := SourceStepNormal N d) data J
  let trans : SourceAuxiliarySpace ((Nat -> W) × SourceFiniteConfiguration N d) (SourceStepNormal N d) J ->
      SourceAuxiliarySpace ((Nat -> W) × SourceFiniteConfiguration N d) (SourceStepNormal N d) J :=
    sourceAuxiliaryTransform (sourceInputPermute s)
      (sourceEuclideanPermute (sourceParticleIndexPermute s)) J
  let B := fun z => sourceInputFinalBranch post flowX flowY J z n t
  have hB : Measurable B := sourceFinalBranch_measurable post flowX flowY hpost hX hY
    Prod.snd (fun k (x : (Nat -> W) × SourceFiniteConfiguration N d) => x.1 k) measurable_snd (fun k => (measurable_pi_apply k).comp measurable_fst) J n t
  have ho := sourceAuxiliaryHistory_preserving nu normal data hd J
  have ht := sourceAuxiliaryTransform_preserving rho normal (sourceInputPermute s)
    (sourceEuclideanPermute (sourceParticleIndexPermute s))
    (sourceInputPermute_preserving nu mu0 (fun o k => innovation k o) initial henv hinit hiid hind hlaw s)
    (source_step_normal_permutation s) J
  have hobs : forall z, B (obs z) = sourceFinalBranch post flowX flowY initial innovation J z n t :=
    fun z => sourceInputFinalBranch_observation post flowX flowY initial innovation J z n t
  have heq : forall z, B (trans z) = sourcePairPermute s (B z) :=
    fun z => sourceInputFinalBranch_transform post flowX flowY s (hpostPerm s) (hXPerm s) J z n t
  have hp : Measurable (sourcePairPermute (d := d) s) :=
    ((sourceParticlePermute_measurable s).comp measurable_fst).prodMk
      ((sourceParticlePermute_measurable s).comp measurable_snd)
  calc
    _ = ((sourceAuxiliaryMeasure nu normal J).map obs).map (sourcePairPermute s ∘ B) := by
      rw [Measure.map_map (hp.comp hB) ho.measurable]
      congr 1
      funext z
      exact congrArg (sourcePairPermute s) (hobs z).symm
    _ = (sourceAuxiliaryMeasure rho normal J).map (B ∘ trans) := by
      rw [ho.map_eq]
      congr 1
      funext z
      exact (heq z).symm
    _ = ((sourceAuxiliaryMeasure rho normal J).map trans).map B := by
      rw [Measure.map_map hB ht.measurable]
    _ = (sourceAuxiliaryMeasure rho normal J).map B := by rw [ht.map_eq]
    _ = _ := by
      rw [<- ho.map_eq,Measure.map_map hB ho.measurable]
      congr 1
      funext z
      exact hobs z

/-- Same one-particle law follows by a swap, without empirical independence. -/
theorem source_pair_marginals_of_permutation
    {S : Type*} [MeasurableSpace S] (rho : Measure S)
    (X : S -> SourceFiniteConfiguration N d × SourceFiniteConfiguration N d) (hX : Measurable X)
    (hinv : forall s : Equiv.Perm (Fin N), rho.map (fun z => sourcePairPermute s (X z)) = rho.map X)
    (c : Fin 2) (i i0 : Fin N) :
    rho.map (fun z => sourcePairCloud c (X z) i) = rho.map (fun z => sourcePairCloud c (X z) i0) := by
  let s := Equiv.swap i i0
  have hp : Measurable (fun x : SourceFiniteConfiguration N d × SourceFiniteConfiguration N d => sourcePairCloud c x i0) :=
    ((measurable_pi_apply i0).comp (WithLp.measurable_ofLp 2 _)).comp (sourcePairCloud_measurable c)
  have hs := congrArg (fun m => m.map (fun x => sourcePairCloud c x i0)) (hinv s)
  have hperm : Measurable (fun z => sourcePairPermute s (X z)) :=
    ((sourceParticlePermute_measurable s).comp hX.fst).prodMk
      ((sourceParticlePermute_measurable s).comp hX.snd)
  rw [Measure.map_map hp hperm,Measure.map_map hp hX] at hs
  by_cases hc : c = 0 <;>
    simpa [sourcePairCloud,sourcePairPermute,sourceParticlePermute,Function.comp_def,s,hc] using hs
end PaperFormalization.Manuscript
