import PaperFormalization.Manuscript.SourceFiniteHorizonPaths
import PaperFormalization.Manuscript.SourceGluedTrackingPaths
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! # Literal coordinate ODEs of the recurrent branches give tracking paths
M13r verified unit (see CODEX_HANDOFF_M13R.md). The output is the actual finite-history glued path, not a free
SourceTrackingPaths input. Only the ORIGINAL coordinate ODEs, branch regularity,
localization, population moments and anti-spikiness are used. This adapter does
not assert global empirical flow existence, exchangeability or their probability.
-/
open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal Topology ProbabilityTheory Matrix.Norms.Frobenius
namespace PaperFormalization.Manuscript
variable {N d : Nat}

/-- Finite coordinate derivatives determine the derivative in the original
PiLp configuration space, without changing its norm or particle normalization. -/
theorem source_configuration_hasDerivAt
    (X : Real -> SourceFiniteConfiguration N d) (V : SourceFiniteConfiguration N d) (t : Real)
    (h : forall i, HasDerivAt (fun s => X s i) (V i) t) : HasDerivAt X V t := by
  let e := (PiLp.continuousLinearEquiv 2 Real
    (fun _ : Fin N => EuclideanSpace Real (Fin d))).symm.toContinuousLinearMap
  have hpi : HasDerivAt (fun s i => X s i) (fun i => V i) t := hasDerivAt_pi.mpr h
  have he := e.hasFDerivAt.comp_hasDerivAt t hpi
  convert he using 1 <;> rfl

/-- Separate AE coordinate equations can be joined since the particle index is
finite; this does not interchange an uncountable collection of null sets. -/
theorem source_configuration_ae_ode
    (X : Real -> SourceFiniteConfiguration N d)
    (V : Real -> SourceFiniteConfiguration N d) (a b : Real)
    (h : forall i, ∀ᵐ t ∂ volume.restrict (Ioo a b),
      HasDerivAt (fun s => X s i) (V t i) t) :
    ∀ᵐ t ∂ volume.restrict (Ioo a b), HasDerivAt X (V t) t := by
  filter_upwards [ae_all_iff.mpr h] with t ht
  exact source_configuration_hasDerivAt X (V t) t ht

variable {W : Type*} [MeasurableSpace W]
variable {H : Nat -> Type*} [forall m, NormedAddCommGroup (H m)]
  [forall m, InnerProductSpace Real (H m)] [forall m, CompleteSpace (H m)]

/-- The finite-history population characteristic, totalized outside the used
schedule only. On every used label it is the original causal characteristic. -/
noncomputable def sourceFiniteReferenceBranch
    (tau eta : Nat -> Real)
    (flowY : (n : Nat) -> (Fin n -> W) -> Real -> EuclideanSpace Real (Fin d) -> EuclideanSpace Real (Fin d))
    (field : (n : Nat) -> (Fin n -> W) -> W -> EuclideanSpace Real (Fin d) -> EuclideanSpace Real (Fin d))
    (J : Nat)
    (h : Fin J -> W × SourceStepNormal N d) (n : Nat)
    (u : EuclideanSpace Real (Fin d)) (t : Real) : EuclideanSpace Real (Fin d) :=
  if hn : n ≤ J then sourceReferenceBranch tau flowY (sourcePopulationFieldJump eta field)
    n (sourcePopulationPrefix (sourceFinitePrefix h n hn)) u t else u

/-- A concrete tracking-path record for the finite recurrence. Coordinate ODEs
are supplied only on the actually used branches; no all-initial-state lifetime
or scalar comparison assumption is inserted. -/
noncomputable def sourceFiniteTrackingPaths
    (mu0 : Measure (EuclideanSpace Real (Fin d)))
    (c p alpha K D A_sp : Real) (phi : forall m, EuclideanSpace Real (Fin d) -> H m)
    (G : lp H 2 -> Real) (U : Set (lp H 2)) (hU : IsOpen U)
    (hDomains : SourceAllMomentDomains (sourceWeightedFeatureMap c p phi) alpha U)
    (hG : ContDiffOn Real 2 G U) (hN : 0 < N)
    (tau eta : Nat -> Real) (flowX flowY field) (J : Nat) (T : Real) (B : NNReal)
    (htau0 : tau 0 = 0) (htime : forall k, k < J -> tau k < tau (k+1)) (hT : tau J ≤ T)
    (h : Fin J -> W × SourceStepNormal N d) (u : SourceFiniteConfiguration N d)
    (hXstart : forall n x, flowX n (tau n) x = x)
    (hYstart : forall n past x, flowY n past (tau n) x = x) :
    let post := sourceActualFinitePost mu0 c p alpha phi G U hU hDomains hG hN tau eta flowX flowY field
    let branches := sourceFiniteHorizonBranch post flowX flowY J h u
    let Z := sourceFiniteReferenceBranch tau eta flowY field J h
    (forall k, k ≤ J -> forall t, t ∈ uIcc (tau k) (if k < J then tau (k+1) else T) ->
      mu0.map (fun z => Z k z t) ∈ sourceMomentClass alpha K) ->
    (forall k, k ≤ J -> ∀ᵐ z ∂ mu0, LipschitzOnWith B (Z k z)
      (uIcc (tau k) (if k < J then tau (k+1) else T))) ->
    (forall k, k ≤ J -> forall i, LipschitzOnWith B (fun t => (branches k t).1 i)
      (uIcc (tau k) (if k < J then tau (k+1) else T))) ->
    (forall k, k ≤ J -> forall i, LipschitzOnWith B (fun t => (branches k t).2 i)
      (uIcc (tau k) (if k < J then tau (k+1) else T))) ->
    (forall k, k ≤ J -> forall t, t ∈ uIcc (tau k) (if k < J then tau (k+1) else T) ->
      forall i, norm ((branches k t).1 i) ≤ D ∧ norm ((branches k t).2 i) ≤ D) ->
    (forall k, k ≤ J -> ∀ᵐ t ∂ volume.restrict (Ioo (tau k) (if k < J then tau (k+1) else T)),
      (N : Real)⁻¹ * ∑ i : Fin N, norm (((branches k t).1-(branches k t).2) i)^3 ≤
        A_sp * (norm ((branches k t).1-(branches k t).2) / Real.sqrt N)^3) ->
    (forall k, k ≤ J -> forall i,
      ∀ᵐ t ∂ volume.restrict (Ioo (tau k) (if k < J then tau (k+1) else T)),
        HasDerivAt (fun s => (branches k s).1 i)
          ((empiricalConfigurationField (sourceWeightedFeatureMap c p phi)
            (momentGradientField (fderiv Real (sourceWeightedFeatureMap c p phi)) (gradient G))
            ((branches k t).1)) i) t) ->
    (forall k, k ≤ J -> forall i,
      ∀ᵐ t ∂ volume.restrict (Ioo (tau k) (if k < J then tau (k+1) else T)),
        HasDerivAt (fun s => (branches k s).2 i)
          ((frozenMomentConfigurationField
            (momentGradientField (fderiv Real (sourceWeightedFeatureMap c p phi)) (gradient G))
            (∫ z, sourceWeightedFeatureMap c p phi z ∂ mu0.map (fun z => Z k z t))
            ((branches k t).2)) i) t) ->
    SourceTrackingPaths (N := N) mu0 J tau T B c p K D alpha A_sp phi G := by
  dsimp only
  intro hclass hZlip hXlip hYlip hlocal hsp hXode hYode
  let post := sourceActualFinitePost mu0 c p alpha phi G U hU hDomains hG hN tau eta flowX flowY field
  let branches := sourceFiniteHorizonBranch post flowX flowY J h u
  let Z := sourceFiniteReferenceBranch tau eta flowY field J h
  apply sourceTrackingPathsOfClosedBranches mu0 J tau T B c p K D alpha A_sp phi G
    htau0 htime hT Z (fun k t => (branches k t).1) (fun k t => (branches k t).2)
    hclass hZlip hXlip hYlip
  · intro k hk i
    exact (hlocal k hk.le (tau (k+1)) (by rw [if_pos hk]; exact right_mem_uIcc) i).1
  · intro k hk i t ht
    exact (hlocal k hk t ht i).2
  · have hstart := sourceCoupledBranch_start post flowX flowY tau hXstart hYstart
      0 (sourceFinitePrefix h 0 (Nat.zero_le J)) u
    rw [htau0] at hstart
    have hb : branches 0 0 = (u,u) := by
      change sourceFiniteHorizonBranch post flowX flowY J h u 0 0 = (u,u)
      rw [sourceFiniteHorizonBranch_eq post flowX flowY J h u 0 (Nat.zero_le J)]
      exact hstart
    exact congrArg Prod.fst hb |>.trans (congrArg Prod.snd hb).symm
  · intro k hk
    have hx := source_configuration_ae_ode _ _ _ _ (hXode k hk)
    have hy := source_configuration_ae_ode _ _ _ _ (hYode k hk)
    filter_upwards [hsp k hk, hx, hy, ae_restrict_mem measurableSet_Ioo] with t hs hx hy ht
    have hloc := hlocal k hk t (Icc_subset_uIcc (Ioo_subset_Icc_self ht))
    exact ⟨fun i => (hloc i).1, fun i => (hloc i).2, hs, hx, hy⟩
end PaperFormalization.Manuscript
