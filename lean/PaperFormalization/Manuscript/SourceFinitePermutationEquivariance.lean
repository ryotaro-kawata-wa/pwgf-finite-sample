import PaperFormalization.Manuscript.SourceInputPermutationLaw
import PaperFormalization.Manuscript.SourceFixedCanonicalJumpView
import PaperFormalization.Manuscript.SourceFiniteHorizonPaths

/-! # Equivariance of the complete fixed finite recurrence, not only its coefficients
M13s verified unit; see CODEX_HANDOFF_M13S.md. Initial configurations and every auxiliary vector are permuted
simultaneously; population innovations are unchanged. This induction uses the
same canonical seed and fixed Gram version as sourceActualFinitePost.
-/
open Matrix MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory Matrix.Norms.Frobenius
namespace PaperFormalization.Manuscript
attribute [local instance] sourceGramMeasurableMatrix sourceGramBorelMatrix
variable {N d : Nat} {W : Type*}

def sourcePairPermute (s : Equiv.Perm (Fin N))
    (x : SourceFiniteConfiguration N d × SourceFiniteConfiguration N d) :=
  (sourceParticlePermute s x.1,sourceParticlePermute s x.2)

def sourcePackedPermute {n : Nat} (s : Equiv.Perm (Fin N))
    (h : Fin n -> W × SourceStepNormal N d) : Fin n -> W × SourceStepNormal N d :=
  fun i => ((h i).1,sourceEuclideanPermute (sourceParticleIndexPermute s) (h i).2)

@[simp] theorem sourcePackedPermute_population {n : Nat} (s : Equiv.Perm (Fin N))
    (h : Fin n -> W × SourceStepNormal N d) :
    sourcePopulationPrefix (sourcePackedPermute s h) = sourcePopulationPrefix h := rfl

@[simp] theorem sourcePackedPermute_init {n : Nat} (s : Equiv.Perm (Fin N))
    (h : Fin (n+1) -> W × SourceStepNormal N d) :
    sourceHistoryInit (sourcePackedPermute s h) = sourcePackedPermute s (sourceHistoryInit h) := rfl

/-- The entire coupled step, including the RAW reference update, is equivariant. -/
theorem sourceCanonicalCoupledStep_permute
    (M : SourceFiniteConfiguration N d -> Matrix (Fin N × Fin d) (Fin N × Fin d) Real)
    (hM : forall x, (M x).IsHermitian)
    (s : Equiv.Perm (Fin N))
    (hMs : forall x, M (sourceParticlePermute s x) = sourceMatrixPermute (sourceParticleIndexPermute s) (M x))
    (eta : Real) (C : Matrix (Fin N × Fin d) (Fin N × Fin d) Real)
    (X Y V : SourceFiniteConfiguration N d) (a : SourceStepNormal N d) :
    sourceCanonicalCoupledStep M hM eta (sourceMatrixPermute (sourceParticleIndexPermute s) C)
      (sourceParticlePermute s X) (sourceParticlePermute s Y) (sourceParticlePermute s V)
      (sourceEuclideanPermute (sourceParticleIndexPermute s) a) =
    sourcePairPermute s (sourceCanonicalCoupledStep M hM eta C X Y V a) := by
  have hseed : sourceCanonicalWhiteningSeed (M (sourceParticlePermute s Y))
      (hM (sourceParticlePermute s Y)) (sourceMatrixPermute (sourceParticleIndexPermute s) C)
      (particleFlatten (sourceParticlePermute s V))
      (sourceEuclideanPermute (sourceParticleIndexPermute s) a) =
        sourceEuclideanPermute (sourceParticleIndexPermute s)
          (sourceCanonicalWhiteningSeed (M Y) (hM Y) C (particleFlatten V) a) := by
    simp only [hMs Y,sourceParticlePermute_flatten]
    exact sourceCanonicalWhiteningSeed_permute (sourceParticleIndexPermute s) (hM Y) C (particleFlatten V) a
  apply Prod.ext
  . apply sourceParticleFlattenIsometry.injective
    change particleFlatten _ = particleFlatten _
    simp only [sourceCanonicalCoupledStep,sourcePairPermute]
    rw [hseed]
    simp only [sourceCanonicalCoupledStep,sourcePairPermute,particleFlatten_sourceParticleUnflatten,
      sourceParticlePermute_flatten,hseed,hMs X,source_matrixEuclideanOperator_eq_toEuclideanCLM,
      source_toEuclideanCLM_permute]
    rfl
  . rfl

section Recursion
variable (tau eta : Nat -> Real)
  (flowX : Nat -> Real -> SourceFiniteConfiguration N d -> SourceFiniteConfiguration N d)
  (flowY : (n : Nat) -> (Fin n -> W) -> Real -> EuclideanSpace Real (Fin d) -> EuclideanSpace Real (Fin d))
  (field : (n : Nat) -> (Fin n -> W) -> W -> EuclideanSpace Real (Fin d) -> EuclideanSpace Real (Fin d))
  (M : SourceFiniteConfiguration N d -> Matrix (Fin N × Fin d) (Fin N × Fin d) Real)
  (hM : forall x, (M x).IsHermitian)
  (C : (n : Nat) -> (Fin n -> W) -> SourceFiniteConfiguration N d -> Matrix (Fin N × Fin d) (Fin N × Fin d) Real)

theorem sourceCanonicalCoupledPost_permute
    (s : Equiv.Perm (Fin N))
    (hFX : forall n t x, flowX n t (sourceParticlePermute s x) = sourceParticlePermute s (flowX n t x))
    (hMs : forall x, M (sourceParticlePermute s x) = sourceMatrixPermute (sourceParticleIndexPermute s) (M x))
    (hCs : forall n h x, C n h (sourceParticlePermute s x) = sourceMatrixPermute (sourceParticleIndexPermute s) (C n h x))
    (n : Nat) (h : Fin n -> W × SourceStepNormal N d) (u : SourceFiniteConfiguration N d) :
    sourceCanonicalCoupledPost tau eta flowX flowY field M hM C n (sourcePackedPermute s h)
      (sourceParticlePermute s u) =
      sourcePairPermute s (sourceCanonicalCoupledPost tau eta flowX flowY field M hM C n h u) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let pop := sourcePopulationPrefix (sourceHistoryInit h)
    let prev := sourceCanonicalCoupledPost tau eta flowX flowY field M hM C n (sourceHistoryInit h) u
    let X := flowX n (tau (n+1)) prev.1
    let Y : SourceFiniteConfiguration N d := WithLp.toLp 2 (fun i => flowY n pop (tau (n+1)) (prev.2 i))
    let V : SourceFiniteConfiguration N d := WithLp.toLp 2 (fun i => field n pop (h (Fin.last n)).1 (Y i))
    simp only [sourceCanonicalCoupledPost,sourcePackedPermute_init,sourcePackedPermute_population,ih,
      sourcePairPermute,hFX]
    change sourceCanonicalCoupledStep M hM (eta n) (C n pop (sourceParticlePermute s Y))
        (sourceParticlePermute s X) (sourceParticlePermute s Y) (sourceParticlePermute s V)
        (sourceEuclideanPermute (sourceParticleIndexPermute s) (h (Fin.last n)).2) =
      sourcePairPermute s (sourceCanonicalCoupledStep M hM (eta n) (C n pop Y) X Y V (h (Fin.last n)).2)
    rw [hCs]
    exact sourceCanonicalCoupledStep_permute M hM s hMs (eta n) _ X Y V _

end Recursion

section Source
variable [MeasurableSpace W]
variable {H : Nat -> Type*} [forall m, NormedAddCommGroup (H m)]
  [forall m, InnerProductSpace Real (H m)] [forall m, CompleteSpace (H m)]

/-- The actual fixed covariance version, not a newly chosen representative,
commutes with block permutations for every prefix. -/
theorem sourceActualCovarianceVersion_permute
    (mu0 : Measure (EuclideanSpace Real (Fin d))) [IsProbabilityMeasure mu0]
    (c p : Real) (phi : forall m, EuclideanSpace Real (Fin d) -> H m)
    (G : lp H 2 -> Real) (U : Set (lp H 2)) (tau eta : Nat -> Real) (flowY field)
    (hFY : forall n t, Measurable (fun z : (Fin n -> W) × EuclideanSpace Real (Fin d) => flowY n z.1 t z.2))
    (hfield : forall n, Measurable (fun z : ((Fin n -> W) × W) × EuclideanSpace Real (Fin d) => field n z.1.1 z.1.2 z.2))
    (s : Equiv.Perm (Fin N)) (n : Nat) (past : Fin n -> W) (Y : SourceFiniteConfiguration N d) :
    sourceActualCovarianceVersion mu0 c p phi G U tau eta flowY field n past (sourceParticlePermute s Y) =
      sourceMatrixPermute (sourceParticleIndexPermute s)
        (sourceActualCovarianceVersion mu0 c p phi G U tau eta flowY field n past Y) := by
  let F := sourceWeightedFeatureMap c p phi
  let k := characteristicKernel mu0 (fun h : (Fin n -> W) × SourceFiniteConfiguration N d =>
    sourceReferencePre tau flowY (sourcePopulationFieldJump eta field) n h.1)
  have hj : forall k, Measurable (fun z : ((Fin k -> W) × W) × EuclideanSpace Real (Fin d) =>
      sourcePopulationFieldJump eta field k z.1.1 z.1.2 z.2) :=
    fun k => measurable_snd.add ((hfield k).const_smul (eta k))
  have hm : Measurable (fun z : ((Fin n -> W) × SourceFiniteConfiguration N d) × EuclideanSpace Real (Fin d) =>
      sourceReferencePre tau flowY (sourcePopulationFieldJump eta field) n z.1.1 z.2) :=
    (sourceReferenceBranch_measurable tau flowY (sourcePopulationFieldJump eta field)
    hFY hj n (tau (n+1))).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hk : k (past,sourceParticlePermute s Y) = k (past,Y) := by
    rw [(characteristicKernel_properties mu0 _ hm).2,(characteristicKernel_properties mu0 _ hm).2]
  calc
    _ = sourcePopulationGramVersion k F G U (F 0) (fun h i => h.2 (s i)) (past,Y) :=
      sourcePopulationGramVersion_congr_at k k F G U (F 0)
        (fun h i => h.2 i) (fun h i => h.2 (s i)) _ _ hk rfl
    _ = _ := sourcePopulationGramVersion_permute k F G U (F 0) (fun h i => h.2 i) s (past,Y)

theorem sourceActualFinitePost_permute
    (mu0 : Measure (EuclideanSpace Real (Fin d))) [IsProbabilityMeasure mu0]
    (c p alpha : Real) (phi : forall m, EuclideanSpace Real (Fin d) -> H m)
    (G : lp H 2 -> Real) (U : Set (lp H 2)) (hU : IsOpen U)
    (hDomains : SourceAllMomentDomains (sourceWeightedFeatureMap c p phi) alpha U)
    (hG : ContDiffOn Real 2 G U) (hN : 0 < N)
    (tau eta : Nat -> Real) (flowX flowY field)
    (hFY : forall n t, Measurable (fun z : (Fin n -> W) × EuclideanSpace Real (Fin d) => flowY n z.1 t z.2))
    (hfield : forall n, Measurable (fun z : ((Fin n -> W) × W) × EuclideanSpace Real (Fin d) => field n z.1.1 z.1.2 z.2))
    (s : Equiv.Perm (Fin N))
    (hFX : forall n t x, flowX n t (sourceParticlePermute s x) = sourceParticlePermute s (flowX n t x))
    (n : Nat) (h : Fin n -> W × SourceStepNormal N d) (u : SourceFiniteConfiguration N d) :
    sourceActualFinitePost mu0 c p alpha phi G U hU hDomains hG hN tau eta flowX flowY field n
      (sourcePackedPermute s h) (sourceParticlePermute s u) =
    sourcePairPermute s (sourceActualFinitePost mu0 c p alpha phi G U hU hDomains hG hN tau eta flowX flowY field n h u) :=
  sourceCanonicalCoupledPost_permute tau eta flowX flowY field _ _ _ s hFX
    (source_empiricalKernelFactor_permute c p phi G s)
    (sourceActualCovarianceVersion_permute mu0 c p phi G U tau eta flowY field hFY hfield s) n h u
end Source

/-- The same symmetry holds on ∀ closed branch labels, not only at jumps. -/
theorem sourceFiniteHorizonBranch_permute (post : SourcePostMap W N d) (flowX flowY)
    (s : Equiv.Perm (Fin N))
    (hpost : forall n h u, post n (sourcePackedPermute s h) (sourceParticlePermute s u) = sourcePairPermute s (post n h u))
    (hFX : forall n t x, flowX n t (sourceParticlePermute s x) = sourceParticlePermute s (flowX n t x))
    (J : Nat) (h : Fin J -> W × SourceStepNormal N d) (u : SourceFiniteConfiguration N d) (n : Nat) (t : Real) :
    sourceFiniteHorizonBranch post flowX flowY J (sourcePackedPermute s h) (sourceParticlePermute s u) n t =
      sourcePairPermute s (sourceFiniteHorizonBranch post flowX flowY J h u n t) := by
  classical
  by_cases hn : n ≤ J
  . rw [sourceFiniteHorizonBranch_eq _ _ _ _ _ _ n hn,
      sourceFiniteHorizonBranch_eq _ _ _ _ _ _ n hn]
    have hp : sourceFinitePrefix (sourcePackedPermute s h) n hn =
        sourcePackedPermute s (sourceFinitePrefix h n hn) := rfl
    simp only [sourceCoupledBranch, hp, hpost, sourcePairPermute,
      sourcePackedPermute_population, hFX]
    rfl
  . simp only [sourceFiniteHorizonBranch,dif_neg hn,sourcePairPermute]
end PaperFormalization.Manuscript
