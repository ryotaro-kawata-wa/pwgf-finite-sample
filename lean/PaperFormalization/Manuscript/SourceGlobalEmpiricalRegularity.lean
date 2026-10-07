import PaperFormalization.Manuscript.SourceSegmentRegularity
import PaperFormalization.Manuscript.SourceEmpiricalFactor
import PaperFormalization.Manuscript.KernelNuclearResidual
import Mathlib.Analysis.ODE.ExistUnique

/-! # The original all-radius domain discharges global empirical regularity

M13q verified unit (see CODEX_HANDOFF_M13Q.md). The manuscript's ONE open U contains every
finite-K, finite-D moment region. This is stronger than fixing one localization
radius, but is already the source assumption (structured-moment-open-neighbourhood).
No global smoothness outside U and no bounded sample event is added. The local
ODE flow below is local: it is not a global-existence or nonexplosion theorem.
-/
open MeasureTheory Set
open scoped BigOperators Topology Matrix.Norms.Frobenius
namespace PaperFormalization.Manuscript

variable {N d : Nat}
variable {H : Nat -> Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace Real (H n)] [∀ n, CompleteSpace (H n)]

/-- The exact all-K/all-D inclusion in the original fixed open domain. -/
def SourceAllMomentDomains (J : EuclideanSpace Real (Fin d) -> lp H 2)
    (alpha : Real) (U : Set (lp H 2)) : Prop :=
  ∀ K : Real, 0 < K -> ∀ D : Real, 1 ≤ D ->
    measureMomentRegion J (sourceMomentClass alpha K) D ⊆ U

/-- Every finite empirical cloud is in U. The radius is a finite deterministic
function of the cloud, not a conditioning event or a new uniform radius premise. -/
theorem source_empirical_moment_mem_all_domains
    (J : EuclideanSpace Real (Fin d) -> lp H 2) (alpha : Real)
    (U : Set (lp H 2)) (hDomains : SourceAllMomentDomains J alpha U)
    (hN : 0 < N) (X : PiLp 2 fun _ : Fin N => EuclideanSpace Real (Fin d)) :
    empiricalMomentMap J X ∈ U := by
  classical
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let D : Real := 1 + ∑ i : Fin N, norm (X i)
  have hD : 1 ≤ D := by
    dsimp only [D]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => norm_nonneg _))
  apply hDomains 1 (by norm_num) D hD
  apply empiricalMomentMap_mem_measureMomentRegion
  intro i
  have hi : norm (X i) ≤ ∑ j : Fin N, norm (X j) :=
    Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  dsimp only [D]
  linarith

/-- C2 on U implies symmetry for every empirical configuration, without
localizing the particles or assuming the resulting matrix symmetry. -/
theorem source_empirical_factor_hermitian_all_domains
    (c p alpha : Real) (phi : ∀ n, EuclideanSpace Real (Fin d) -> H n)
    (G : lp H 2 -> Real) (U : Set (lp H 2)) (hU : IsOpen U)
    (hDomains : SourceAllMomentDomains (sourceWeightedFeatureMap c p phi) alpha U)
    (hG : ContDiffOn Real 2 G U) (hN : 0 < N)
    (X : PiLp 2 fun _ : Fin N => EuclideanSpace Real (Fin d)) :
    (sourceEmpiricalKernelFactor c p phi G X).IsHermitian := by
  apply actualMomentKernel_empiricalFactor_isHermitian
  exact hG.contDiffAt (hU.mem_nhds
    (source_empirical_moment_mem_all_domains _ alpha U hDomains hN X))

/-- Continuous feature moments retain the exact reciprocal-cardinality mean. -/
theorem source_continuous_empiricalMomentMap
    (J : EuclideanSpace Real (Fin d) -> lp H 2) (hJ : Continuous J) :
    Continuous (empiricalMomentMap J :
      (PiLp 2 fun _ : Fin N => EuclideanSpace Real (Fin d)) -> lp H 2) := by
  classical
  unfold empiricalMomentMap
  exact (continuous_finsetSum Finset.univ (fun i _ =>
    hJ.comp (PiLp.proj (𝕜 := Real) 2 (fun _ : Fin N => EuclideanSpace Real (Fin d)) i).continuous)).const_smul ((Fintype.card (Fin N) : Real)⁻¹)

/-- The ACTUAL normalized empirical Hessian factor is continuous everywhere on
the finite configuration space. Only local objective smoothness on U is used. -/
theorem source_empirical_factor_continuous_all_domains
    (c C g p q alpha : Real) (phi : ∀ n, EuclideanSpace Real (Fin d) -> H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hphi : ∀ n, ContDiff Real 2 (phi n))
    (hgrowth : ∀ n z k, k ≤ 2 -> norm (iteratedFDeriv Real k (phi n) z) ≤
      featureGrowth C g q n * (1 + norm z ^ (n+1-k)))
    (G : lp H 2 -> Real) (U : Set (lp H 2)) (hU : IsOpen U)
    (hDomains : SourceAllMomentDomains (sourceWeightedFeatureMap c p phi) alpha U)
    (hG : ContDiffOn Real 2 G U) (hN : 0 < N) :
    Continuous (sourceEmpiricalKernelFactor (N := N) c p phi G) := by
  classical
  let J := sourceWeightedFeatureMap c p phi
  have hj := contDiff_sourceWeightedFeatureMap c C g p q phi hc hC hp hq hphi hgrowth
  have hm := source_continuous_empiricalMomentMap (N := N) J hj.continuous
  have hh : Continuous (fun X : PiLp 2 fun _ : Fin N => EuclideanSpace Real (Fin d) =>
      momentObjectiveHessian G (empiricalMomentMap J X)) := by
    apply continuous_iff_continuousAt.mpr
    intro X
    exact ((continuousOn_momentObjectiveHessian G U hU hG).continuousAt
      (hU.mem_nhds (source_empirical_moment_mem_all_domains J alpha U hDomains hN X))).comp hm.continuousAt
  have hd (i : Fin N × Fin d) : Continuous
      (fun X : PiLp 2 fun _ : Fin N => EuclideanSpace Real (Fin d) =>
        actualFeatureDerivativeColumns J (X i.1) i.2) :=
    ((hj.continuous_fderiv (by norm_num)).comp
      (PiLp.proj (𝕜 := Real) 2 (fun _ : Fin N => EuclideanSpace Real (Fin d)) i.1).continuous).clm_apply continuous_const
  have hentry (i j : Fin N × Fin d) : Continuous
      (fun X : PiLp 2 fun _ : Fin N => EuclideanSpace Real (Fin d) =>
        sourceEmpiricalKernelFactor c p phi G X i j) := by
    have heq : (fun X : PiLp 2 fun _ : Fin N => EuclideanSpace Real (Fin d) =>
        sourceEmpiricalKernelFactor c p phi G X i j) =
        fun X => (Real.sqrt N)⁻¹ * inner Real
          (momentObjectiveHessian G (empiricalMomentMap J X)
            (actualFeatureDerivativeColumns J (X i.1) i.2))
          (actualFeatureDerivativeColumns J (X j.1) j.2) := by
      funext X
      change (Real.sqrt N)⁻¹ * actualMomentKernelMatrix J G
        (empiricalMomentMap J X) (X i.1) (X j.1) i.2 j.2 = _
      rw [actualMomentKernelMatrix_eq_column_inner J G _ _ _
        (hG.contDiffAt (hU.mem_nhds
          (source_empirical_moment_mem_all_domains J alpha U hDomains hN X)))]
    rw [heq]
    exact continuous_const.mul ((hh.clm_apply (hd i)).inner (hd j))

  let assemble : ((Fin N × Fin d) -> (Fin N × Fin d) -> Real) ->
      Matrix (Fin N × Fin d) (Fin N × Fin d) Real :=
    fun v => ∑ i, ∑ j, v i j • Matrix.single i j (1 : Real)
  have ha : Continuous assemble := by unfold assemble; fun_prop
  have he := continuous_pi (fun i => continuous_pi (fun j => hentry i j))
  convert ha.comp he using 1
  funext X
  simpa only [Function.comp_def, assemble, Matrix.smul_single, smul_eq_mul, mul_one] using
    Matrix.matrix_eq_sum_single (sourceEmpiricalKernelFactor c p phi G X)

/-- The exact empirical ODE vector field is C1 on the whole finite
configuration space, derived from the original source domain and features. -/
theorem source_empirical_drift_contDiff_all_domains
    (c C g p q alpha : Real) (phi : ∀ n, EuclideanSpace Real (Fin d) -> H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hphi : ∀ n, ContDiff Real 2 (phi n))
    (hgrowth : ∀ n z k, k ≤ 2 -> norm (iteratedFDeriv Real k (phi n) z) ≤
      featureGrowth C g q n * (1 + norm z ^ (n+1-k)))
    (G : lp H 2 -> Real) (U : Set (lp H 2)) (hU : IsOpen U)
    (hDomains : SourceAllMomentDomains (sourceWeightedFeatureMap c p phi) alpha U)
    (hG : ContDiffOn Real 3 G U) (hN : 0 < N) :
    let J := sourceWeightedFeatureMap c p phi
    ContDiff Real 1 (empiricalConfigurationField (ι := Fin N) J
      (momentGradientField (fderiv Real J) (gradient G))) := by
  apply contDiff_iff_contDiffAt.mpr
  intro X
  exact contDiffAt_sourceEmpiricalMomentGradientField c C g p q phi hc hC hp hq
    hphi hgrowth G U hU hG X
    (source_empirical_moment_mem_all_domains _ alpha U hDomains hN X)

/-- A C1 field gives a jointly continuous LOCAL flow. No global extension or
uniform lifespan over unbounded initial states is asserted. -/
theorem source_local_continuous_flow_of_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    (f : E -> E) (hf : ContDiff Real 1 f) (x0 : E) (t0 : Real) :
    ∃ r : Real, 0 < r ∧ ∃ eps : Real, 0 < eps ∧
      ∃ flow : E × Real -> E,
        (∀ x, x ∈ Metric.closedBall x0 r -> flow (x,t0) = x ∧
          ∀ t, t ∈ Ioo (t0-eps) (t0+eps) ->
            HasDerivAt (fun s => flow (x,s)) (f (flow (x,t))) t) ∧
        ContinuousOn flow (Metric.closedBall x0 r ×ˢ Icc (t0-eps) (t0+eps)) := by
  obtain ⟨eps, heps, a, r, L, K, hr, hpl⟩ :=
    IsPicardLindelof.of_contDiffAt_one (hf.contDiffAt (x := x0))
  obtain ⟨flow, hflow, hcont⟩ :=
    (hpl t0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  refine ⟨r, hr, eps, heps, flow, ?_, hcont⟩
  intro x hx
  refine ⟨(hflow x hx).1, ?_⟩
  intro t ht
  exact ((hflow x hx).2 t (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

end PaperFormalization.Manuscript
