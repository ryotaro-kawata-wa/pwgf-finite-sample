import PaperFormalization.Manuscript.SourceFiniteParticleRecursion
import PaperFormalization.Manuscript.SourceActualGramRegularity

/-! # Instantiate the finite recurrence with the literal source matrices

M13q verified unit (see CODEX_HANDOFF_M13Q.md). Neither a matrix factor nor a covariance
version nor a Gaussian coordinate is a free input to this source construction.
They are the actual empirical factor, the proved Borel population Gram version,
and the fixed spectral-whitening rule. The primitive inputs still include the
source branch solution maps and raw population field realization.
-/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ProbabilityTheory Matrix.Norms.Frobenius
namespace PaperFormalization.Manuscript
attribute [local instance] sourceGramMeasurableMatrix sourceGramBorelMatrix
variable {N d : Nat} {W : Type*} [MeasurableSpace W]
variable {H : Nat -> Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace Real (H n)] [∀ n, CompleteSpace (H n)]

/-- The actual population jump, not a newly sampled finite-coordinate update. -/
def sourcePopulationFieldJump
    (eta : Nat -> Real)
    (field : (n : Nat) -> (Fin n -> W) -> W -> EuclideanSpace Real (Fin d) -> EuclideanSpace Real (Fin d))
    (n : Nat) (past : Fin n -> W) (w : W) (x : EuclideanSpace Real (Fin d)) :=
  x + eta n • field n past w x

/-- The Borel covariance rule on prefix and evaluation configuration, computed
from the ORIGINAL seed pushforward and actual moment Hessian. -/
noncomputable def sourceActualCovarianceVersion
    (mu0 : Measure (EuclideanSpace Real (Fin d)))
    (c p : Real) (phi : ∀ n, EuclideanSpace Real (Fin d) -> H n)
    (G : lp H 2 -> Real) (U : Set (lp H 2))
    (tau eta : Nat -> Real)
    (flowY : (n : Nat) -> (Fin n -> W) -> Real -> EuclideanSpace Real (Fin d) -> EuclideanSpace Real (Fin d))
    (field : (n : Nat) -> (Fin n -> W) -> W -> EuclideanSpace Real (Fin d) -> EuclideanSpace Real (Fin d))
    (n : Nat) (past : Fin n -> W) (Y : SourceFiniteConfiguration N d) :=
  sourcePopulationGramVersion
    (characteristicKernel mu0 (fun h u =>
      sourceReferencePre tau flowY (sourcePopulationFieldJump eta field) n h.1 u))
    (sourceWeightedFeatureMap c p phi) G U (sourceWeightedFeatureMap c p phi 0)
    (fun h i => (h.2 : SourceFiniteConfiguration N d) i) (past,Y)

/-- Raw measurable branch/field maps and source derivatives make the actual
covariance RULE measurable. Its equality to a genuine Gram integral is supplied
by sourcePopulationGramVersion_eq_actual on the derived finite-scale set. -/
theorem sourceActualCovarianceVersion_measurable
    (mu0 : Measure (EuclideanSpace Real (Fin d))) [IsProbabilityMeasure mu0]
    (c C g p q alpha : Real) (phi : ∀ n, EuclideanSpace Real (Fin d) -> H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hphi : ∀ n, ContDiff Real 2 (phi n))
    (hgrowth : ∀ n z k, k ≤ 2 -> norm (iteratedFDeriv Real k (phi n) z) ≤
      featureGrowth C g q n * (1 + norm z ^ (n+1-k)))
    (G : lp H 2 -> Real) (U : Set (lp H 2)) (hU : IsOpen U)
    (hDomains : SourceAllMomentDomains (sourceWeightedFeatureMap c p phi) alpha U)
    (hG : ContDiffOn Real 2 G U) (tau eta : Nat -> Real) (flowY field)
    (hFY : ∀ n t, Measurable (fun z : (Fin n -> W) × EuclideanSpace Real (Fin d) => flowY n z.1 t z.2))
    (hField : ∀ n, Measurable (fun z : ((Fin n -> W) × W) × EuclideanSpace Real (Fin d) => field n z.1.1 z.1.2 z.2))
    (n : Nat) :
    Measurable (fun z : (Fin n -> W) × SourceFiniteConfiguration N d =>
      sourceActualCovarianceVersion mu0 c p phi G U tau eta flowY field n z.1 z.2) := by
  have hjump : ∀ n, Measurable (fun z : ((Fin n -> W) × W) × EuclideanSpace Real (Fin d) =>
      sourcePopulationFieldJump eta field n z.1.1 z.1.2 z.2) :=
    fun n => measurable_snd.add ((hField n).const_smul (eta n))
  have hpre := sourceReferenceBranch_measurable tau flowY (sourcePopulationFieldJump eta field)
    hFY hjump n (tau (n+1))
  let kappa := characteristicKernel mu0 (fun h : (Fin n -> W) × SourceFiniteConfiguration N d =>
    fun u => sourceReferencePre tau flowY (sourcePopulationFieldJump eta field) n h.1 u)
  have hpreFull : Measurable (fun z : ((Fin n -> W) × SourceFiniteConfiguration N d) ×
      EuclideanSpace Real (Fin d) => sourceReferencePre tau flowY (sourcePopulationFieldJump eta field) n z.1.1 z.2) :=
    hpre.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  letI : IsMarkovKernel kappa := (characteristicKernel_properties mu0 _ hpreFull).1
  have hj := contDiff_sourceWeightedFeatureMap c C g p q phi hc hC hp hq hphi hgrowth
  have hanchor : sourceWeightedFeatureMap c p phi 0 ∈ U :=
    hDomains 1 (by norm_num) 1 (by norm_num)
      (zero_anchor_mem_measureMomentRegion _ _ 1 (by norm_num))
  exact sourcePopulationGramVersion_measurable kappa _ hj.continuous
    (hj.continuous_fderiv (by norm_num)) G U hU hG _ hanchor (fun h i => h.2 i)
    (fun i => ((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 _)).comp measurable_snd)

/-- An explicit source finite particle construction. The branch maps are source
primitives; their literal ODE equations are not replaced by scalar estimates. -/
noncomputable def sourceActualFinitePost
    (mu0 : Measure (EuclideanSpace Real (Fin d)))
    (c p alpha : Real) (phi : ∀ n, EuclideanSpace Real (Fin d) -> H n)
    (G : lp H 2 -> Real) (U : Set (lp H 2)) (hU : IsOpen U)
    (hDomains : SourceAllMomentDomains (sourceWeightedFeatureMap c p phi) alpha U)
    (hG : ContDiffOn Real 2 G U) (hN : 0 < N)
    (tau eta : Nat -> Real) (flowX flowY field)
    (n : Nat) (h : Fin n -> W × EuclideanSpace Real (Fin N × Fin d))
    (u : SourceFiniteConfiguration N d) :=
  sourceCanonicalCoupledPost tau eta flowX flowY field (sourceEmpiricalKernelFactor c p phi G)
    (source_empirical_factor_hermitian_all_domains c p alpha phi G U hU hDomains hG hN)
    (sourceActualCovarianceVersion mu0 c p phi G U tau eta flowY field) n h u

/-- Both source states are measurable functions of the original sample and
strict finite innovation prefix. No output measurability is assumed. -/
theorem sourceActualFinitePost_measurable
    (mu0 : Measure (EuclideanSpace Real (Fin d))) [IsProbabilityMeasure mu0]
    (c C g p q alpha : Real) (phi : ∀ n, EuclideanSpace Real (Fin d) -> H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hphi : ∀ n, ContDiff Real 2 (phi n))
    (hgrowth : ∀ n z k, k ≤ 2 -> norm (iteratedFDeriv Real k (phi n) z) ≤
      featureGrowth C g q n * (1 + norm z ^ (n+1-k)))
    (G : lp H 2 -> Real) (U : Set (lp H 2)) (hU : IsOpen U)
    (hDomains : SourceAllMomentDomains (sourceWeightedFeatureMap c p phi) alpha U)
    (hG : ContDiffOn Real 2 G U) (hN : 0 < N)
    (tau eta : Nat -> Real) (flowX flowY field)
    (hFX : ∀ n t, Measurable (flowX n t))
    (hFY : ∀ n t, Measurable (fun z : (Fin n -> W) × EuclideanSpace Real (Fin d) => flowY n z.1 t z.2))
    (hField : ∀ n, Measurable (fun z : ((Fin n -> W) × W) × EuclideanSpace Real (Fin d) => field n z.1.1 z.1.2 z.2))
    (n : Nat) :
    Measurable (fun z : (Fin n -> W × EuclideanSpace Real (Fin N × Fin d)) × SourceFiniteConfiguration N d =>
      sourceActualFinitePost mu0 c p alpha phi G U hU hDomains hG hN tau eta flowX flowY field n z.1 z.2) := by
  exact sourceCanonicalCoupledPost_measurable tau eta flowX flowY field _ _ _ hFX hFY hField
    (source_empirical_factor_continuous_all_domains c C g p q alpha phi hc hC hp hq
      hphi hgrowth G U hU hDomains hG hN).measurable
    (sourceActualCovarianceVersion_measurable mu0 c C g p q alpha phi hc hC hp hq hphi hgrowth
      G U hU hDomains hG tau eta flowY field hFY hField) n

/-- Every source reference coordinate is the original causal characteristic,
independently of all whitening auxiliaries and the empirical state. -/
theorem sourceActualFinitePost_reference
    (mu0 : Measure (EuclideanSpace Real (Fin d)))
    (c p alpha : Real) (phi : ∀ n, EuclideanSpace Real (Fin d) -> H n)
    (G : lp H 2 -> Real) (U : Set (lp H 2)) (hU : IsOpen U)
    (hDomains : SourceAllMomentDomains (sourceWeightedFeatureMap c p phi) alpha U)
    (hG : ContDiffOn Real 2 G U) (hN : 0 < N)
    (tau eta : Nat -> Real) (flowX flowY field)
    (n : Nat) (h : Fin n -> W × EuclideanSpace Real (Fin N × Fin d))
    (u : SourceFiniteConfiguration N d) (i : Fin N) :
    (sourceActualFinitePost mu0 c p alpha phi G U hU hDomains hG hN tau eta flowX flowY field n h u).2 i =
      sourceReferencePost tau flowY (sourcePopulationFieldJump eta field) n (sourcePopulationPrefix h) (u i) :=
  sourceCanonicalCoupledPost_reference tau eta flowX flowY field _ _ _ n h u i
end PaperFormalization.Manuscript
