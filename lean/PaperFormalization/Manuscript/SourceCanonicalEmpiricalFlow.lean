import PaperFormalization.Manuscript.SourceCanonicalODEFlow
import PaperFormalization.Manuscript.SourceParticlePermutation
import PaperFormalization.Manuscript.SourceActualFiniteConstruction

/-! # The actual empirical drift has a canonical measurable horizon flow
M13s verified unit; see CODEX_HANDOFF_M13S.md. The original all-moment-domain hypothesis implies C1 regularity.
No solution is claimed outside the closed-interval existence domain. On that
domain, coordinate ODEs and agreement with the manuscript's solutions follow.
Particle permutation equivariance is derived, not made a new model field.
-/
open MeasureTheory Set
open scoped Topology
namespace PaperFormalization.Manuscript
variable {N d : Nat}

noncomputable def sourceParticlePermuteIsometry (s : Equiv.Perm (Fin N)) :
    SourceFiniteConfiguration N d ≃ₗᵢ[Real] SourceFiniteConfiguration N d :=
  LinearIsometryEquiv.piLpCongrLeft 2 Real (EuclideanSpace Real (Fin d)) s.symm

@[simp] theorem sourceParticlePermuteIsometry_apply (s : Equiv.Perm (Fin N))
    (x : SourceFiniteConfiguration N d) : sourceParticlePermuteIsometry s x = sourceParticlePermute s x := rfl

/-- The source endpoint on a used branch; unused labels have zero length. -/
def sourceHorizonEndpoint (tau : Nat -> Real) (J : Nat) (T : Real) (n : Nat) : Real :=
  if n < J then tau (n+1) else if n = J then T else tau n

theorem sourceHorizonEndpoint_ordered (tau : Nat -> Real) (J : Nat) (T : Real)
    (htime : forall n, n < J -> tau n < tau (n+1)) (hT : tau J ≤ T) (n : Nat) :
    tau n ≤ sourceHorizonEndpoint tau J T n := by
  classical
  unfold sourceHorizonEndpoint
  split_ifs with hn he
  . exact (htime n hn).le
  . simpa [he] using hT
  . exact le_rfl

theorem sourceHorizonEndpoint_used (tau : Nat -> Real) (J : Nat) (T : Real)
    (n : Nat) (hn : n ≤ J) :
    sourceHorizonEndpoint tau J T n = if n < J then tau (n+1) else T := by
  unfold sourceHorizonEndpoint
  split_ifs <;> first | rfl | omega

variable {H : Nat -> Type*} [forall m, NormedAddCommGroup (H m)]
  [forall m, InnerProductSpace Real (H m)] [forall m, CompleteSpace (H m)]

noncomputable def sourceExactEmpiricalDrift
    (c p : Real) (phi : forall m, EuclideanSpace Real (Fin d) -> H m)
    (G : lp H 2 -> Real) : SourceFiniteConfiguration N d -> SourceFiniteConfiguration N d :=
  empiricalConfigurationField (sourceWeightedFeatureMap c p phi)
    (momentGradientField (fderiv Real (sourceWeightedFeatureMap c p phi)) (gradient G))

noncomputable def sourceCanonicalEmpiricalFlow
    (c p : Real) (phi : forall m, EuclideanSpace Real (Fin d) -> H m)
    (G : lp H 2 -> Real) (tau : Nat -> Real) (J : Nat) (T : Real)
    (htime : forall n, n < J -> tau n < tau (n+1)) (hT : tau J ≤ T)
    (n : Nat) (t : Real) (x : SourceFiniteConfiguration N d) : SourceFiniteConfiguration N d :=
  sourceCanonicalODEFlow (sourceExactEmpiricalDrift c p phi G) (tau n)
    (sourceHorizonEndpoint tau J T n) (sourceHorizonEndpoint_ordered tau J T htime hT n) x t

/-- Measurability and symmetry use the SAME selected solution map. -/
theorem sourceCanonicalEmpiricalFlow_properties
    (c C g p q alpha : Real) (phi : forall m, EuclideanSpace Real (Fin d) -> H m)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hphi : forall m, ContDiff Real 2 (phi m))
    (hgrowth : forall m z k, k ≤ 2 -> norm (iteratedFDeriv Real k (phi m) z) ≤
      featureGrowth C g q m * (1 + norm z ^ (m+1-k)))
    (G : lp H 2 -> Real) (U : Set (lp H 2)) (hU : IsOpen U)
    (hDomains : SourceAllMomentDomains (sourceWeightedFeatureMap c p phi) alpha U)
    (hG : ContDiffOn Real 3 G U) (hN : 0 < N)
    (tau : Nat -> Real) (J : Nat) (T : Real)
    (htime : forall n, n < J -> tau n < tau (n+1)) (hT : tau J ≤ T) :
    let flow := sourceCanonicalEmpiricalFlow c p phi G tau J T htime hT
    (forall n t, Measurable (flow n t)) ∧
    (forall n x, flow n (tau n) x = x) ∧
    (forall n x, Continuous (fun t => flow n t x)) ∧
    (forall (s : Equiv.Perm (Fin N)) n t x,
      flow n t (sourceParticlePermute s x) = sourceParticlePermute s (flow n t x)) := by
  have hf := source_empirical_drift_contDiff_all_domains c C g p q alpha phi
    hc hC hp hq hphi hgrowth G U hU hDomains hG hN
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  . intro n t
    exact (sourceCanonicalODEFlow_measurable _ hf _ _ _).comp (measurable_id.prodMk measurable_const)
  . intro n x
    exact sourceCanonicalODEFlow_initial _ hf _ _ _ x
  . intro n x
    exact sourceODEPathExtend_continuous _ _
  . intro s n t x
    exact sourceCanonicalODEFlow_symmetry _ hf _ _ _ (sourceParticlePermuteIsometry s)
      (fun x => source_empiricalConfigurationField_permute _ _ s x) x t

/-- On the actual source existence domain, this is the literal empirical ODE. -/
theorem sourceCanonicalEmpiricalFlow_ode
    (c p : Real) (phi : forall m, EuclideanSpace Real (Fin d) -> H m)
    (G : lp H 2 -> Real)
    (hf : ContDiff Real 1 (sourceExactEmpiricalDrift (N := N) c p phi G))
    (tau : Nat -> Real) (J : Nat) (T : Real)
    (htime : forall n, n < J -> tau n < tau (n+1)) (hT : tau J ≤ T)
    (n : Nat) (x : SourceFiniteConfiguration N d)
    (hx : x ∈ sourceODEExistenceDomain (sourceExactEmpiricalDrift c p phi G)
      (tau n) (sourceHorizonEndpoint tau J T n) (sourceHorizonEndpoint_ordered tau J T htime hT n))
    (t : Real) (ht : t ∈ Ioo (tau n) (sourceHorizonEndpoint tau J T n)) :
    HasDerivAt (fun s => sourceCanonicalEmpiricalFlow c p phi G tau J T htime hT n s x)
      (sourceExactEmpiricalDrift c p phi G
        (sourceCanonicalEmpiricalFlow c p phi G tau J T htime hT n t x)) t := by
  exact (sourceODESolutionSet_hasDerivWithinAt _ hf.continuous _ _ _ _
    (sourceCanonicalODEPath_mem _ hf _ _ _ x hx) t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)

/-- A source solution supplies membership in the canonical lifetime domain and
is exactly the selected path; this is not an extra assumption of nonexplosion. -/
theorem sourceCanonicalEmpiricalFlow_eq_source
    (c p : Real) (phi : forall m, EuclideanSpace Real (Fin d) -> H m) (G : lp H 2 -> Real)
    (hf : ContDiff Real 1 (sourceExactEmpiricalDrift (N := N) c p phi G))
    (tau : Nat -> Real) (J : Nat) (T : Real)
    (htime : forall n, n < J -> tau n < tau (n+1)) (hT : tau J ≤ T)
    (n : Nat) (x : Real -> SourceFiniteConfiguration N d)
    (hx : ContinuousOn x (Icc (tau n) (sourceHorizonEndpoint tau J T n)))
    (hode : ∀ t ∈ Ioo (tau n) (sourceHorizonEndpoint tau J T n),
      HasDerivAt x (sourceExactEmpiricalDrift c p phi G (x t)) t) :
    x (tau n) ∈ sourceODEExistenceDomain (sourceExactEmpiricalDrift c p phi G)
      (tau n) (sourceHorizonEndpoint tau J T n) (sourceHorizonEndpoint_ordered tau J T htime hT n) ∧
    EqOn (fun t => sourceCanonicalEmpiricalFlow c p phi G tau J T htime hT n t (x (tau n)))
      x (Icc (tau n) (sourceHorizonEndpoint tau J T n)) := by
  refine ⟨?_,sourceCanonicalODEFlow_eq_actual _ hf _ _ _ x hx hode⟩
  exact ⟨⟨⟨fun t => x t,hx.restrict⟩,sourceODESolutionSet_of_hasDerivAt _ hf.continuous _ _ _ x hx hode⟩,rfl⟩
end PaperFormalization.Manuscript
