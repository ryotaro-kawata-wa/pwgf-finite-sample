import PaperFormalization.Manuscript.SourceOriginalFreshJump
import PaperFormalization.Manuscript.SourceCanonicalWhitening

/-! # The fixed finite-recursion whitening rule under the original law

M13q verified unit (see CODEX_HANDOFF_M13Q.md). All covariance regularity/version identities and
raw conditional Gaussian laws below are DERIVED from source features, original
reference moments and the primitive fresh innovation. The exact fixed formula
used in finite iteration has the correct standard law and reproduces the raw
population vector, not merely some existentially chosen substitute coordinate.
-/
open Matrix MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory Matrix.Norms.Frobenius
namespace PaperFormalization.Manuscript
attribute [local instance] sourceGramMeasurableMatrix sourceGramBorelMatrix
variable {O S Env W : Type*} [MeasurableSpace O] [MeasurableSpace S]
  [MeasurableSpace Env] [MeasurableSpace W] {N d : Nat}
variable {H : Nat -> Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace Real (H n)] [∀ n, CompleteSpace (H n)]

set_option maxHeartbeats 4000000 in
/-- Source-specific validation of the deterministic canonical seed. In
particular, hGaussian, hCovarianceVersion and matrix measurability are not
premises. The per-innovation field law is the original Gaussian-field model. -/
theorem source_original_canonical_seed_law
    (c C g p q alpha K0 : Real) (phi : ∀ n, EuclideanSpace Real (Fin d) -> H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (halpha : 0 < alpha) (hK0 : 0 < K0)
    (hphi : ∀ n, ContDiff Real 2 (phi n))
    (hgrowth : ∀ n z k, k ≤ 2 -> norm (iteratedFDeriv Real k (phi n) z) ≤
      featureGrowth C g q n * (1 + norm z ^ (n+1-k)))
    (G : lp H 2 -> Real) (U : Set (lp H 2)) (hU : IsOpen U)
    (hDomains : SourceAllMomentDomains (sourceWeightedFeatureMap c p phi) alpha U)
    (hG : ContDiffOn Real 2 G U) (hN : 0 < N)
    (nu : Measure O) [IsProbabilityMeasure nu]
    (mu0 : Measure (EuclideanSpace Real (Fin d))) [IsProbabilityMeasure mu0]
    (lambda : Measure W) [IsProbabilityMeasure lambda]
    (history : O -> S) (past : S -> Env)
    (initial : O -> EuclideanSpace Real (Fin d)) (innovation : O -> W)
    (hH : Measurable history) (hpast : Measurable past)
    (hinit : Measurable initial) (hInnovation : Measurable innovation)
    (hPopIndependent : IndepFun (past ∘ history) initial nu)
    (hInitialLaw : nu.map initial = mu0)
    (hFresh : IndepFun history innovation nu) (hInnovationLaw : nu.map innovation = lambda)
    (Phi : Env -> EuclideanSpace Real (Fin d) -> EuclideanSpace Real (Fin d))
    (hPhi : Measurable (fun z : Env × EuclideanSpace Real (Fin d) => Phi z.1 z.2))
    (hMoment : nu.map (fun o => Phi (past (history o)) (initial o)) ∈ sourceMomentClass alpha K0)
    (Y : S -> PiLp 2 (fun _ : Fin N => EuclideanSpace Real (Fin d))) (hY : Measurable Y)
    (evaluate : S -> W -> EuclideanSpace Real (Fin N × Fin d))
    (hEvaluate : Measurable (fun z : S × W => evaluate z.1 z.2))
    (hField : let popLaw := characteristicKernel mu0 (fun h u => Phi (past h) u)
      ∀ᵐ h ∂ nu.map history, lambda.map (evaluate h) = multivariateGaussian 0
        (populationGramCovariance (popLaw h)
          (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix
            (sourceWeightedFeatureMap c p phi) G
            (∫ x, sourceWeightedFeatureMap c p phi x ∂ popLaw h) (Y h i) z)))) :
    let J := sourceWeightedFeatureMap c p phi
    let popLaw := characteristicKernel mu0 (fun h u => Phi (past h) u)
    let normal := stdGaussian (EuclideanSpace Real (Fin N × Fin d))
    let M := fun h => sourceEmpiricalKernelFactor c p phi G (Y h)
    let hM := fun h => source_empirical_factor_hermitian_all_domains c p alpha phi G U hU hDomains hG hN (Y h)
    let Cov := fun h => populationGramCovariance (popLaw h)
      (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix J G
        (∫ x, J x ∂ popLaw h) (Y h i) z))
    let version := sourcePopulationGramVersion popLaw J G U (J 0) (fun h i => Y h i)
    let seed := fun h (z : EuclideanSpace Real (Fin N × Fin d) × EuclideanSpace Real (Fin N × Fin d)) =>
      sourceCanonicalWhiteningSeed (M h) (hM h) (version h) z.1 z.2
    Measurable (fun z : S × (EuclideanSpace Real (Fin N × Fin d) ×
      EuclideanSpace Real (Fin N × Fin d)) => seed z.1 z.2) ∧
    (nu.prod normal).map (fun z => (history z.1,
      seed (history z.1) (evaluate (history z.1) (innovation z.1),z.2))) =
        (nu.map history).prod normal ∧
    (∀ᵐ z ∂ nu.prod normal,
      matrixEuclideanOperator (alignedCovarianceFactor (hM (history z.1)) (Cov (history z.1)))
        (seed (history z.1) (evaluate (history z.1) (innovation z.1),z.2)) =
          evaluate (history z.1) (innovation z.1)) := by
  let J := sourceWeightedFeatureMap c p phi
  let popLaw := characteristicKernel mu0 (fun h u => Phi (past h) u)
  have hPhiFull : Measurable (fun z : S × EuclideanSpace Real (Fin d) => Phi (past z.1) z.2) :=
    hPhi.comp ((hpast.comp measurable_fst).prodMk measurable_snd)
  letI : IsMarkovKernel popLaw := (characteristicKernel_properties mu0 _ hPhiFull).1
  let rho := nu.map history
  letI : IsProbabilityMeasure rho := Measure.isProbabilityMeasure_map hH.aemeasurable
  let normal := stdGaussian (EuclideanSpace Real (Fin N × Fin d))
  let raw := fun o => evaluate (history o) (innovation o)
  have hraw : Measurable raw := hEvaluate.comp (hH.prodMk hInnovation)
  let k := condDistrib raw history nu
  let M := fun h => sourceEmpiricalKernelFactor c p phi G (Y h)
  let hM := fun h => source_empirical_factor_hermitian_all_domains c p alpha phi G U hU hDomains hG hN (Y h)
  let Cov := fun h => populationGramCovariance (popLaw h)
    (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix J G
      (∫ x, J x ∂ popLaw h) (Y h i) z))
  let version := sourcePopulationGramVersion popLaw J G U (J 0) (fun h i => Y h i)
  have hfinite := source_full_history_finite_scales_of_reference_moments nu mu0 history past initial
    hH hpast hinit hPopIndependent hInitialLaw Phi hPhi alpha K0 halpha hK0 hMoment
  have hYcoord : ∀ i, Measurable (fun h => Y h i) := fun i =>
    ((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 _)).comp hY
  have hVersion := source_actual_gram_version_ae c C g p q alpha phi hc hC hp hq halpha
    hphi hgrowth G U hU hDomains hG rho popLaw hfinite (fun h i => Y h i) hYcoord
  have hJ := contDiff_sourceWeightedFeatureMap c C g p q phi hc hC hp hq hphi hgrowth
  have hanchor : J 0 ∈ U := hDomains 1 (by norm_num) 1 (by norm_num)
    (zero_anchor_mem_measureMomentRegion J _ 1 (by norm_num))
  have hCm := sourcePopulationGramVersion_measurable popLaw J hJ.continuous
    (hJ.continuous_fderiv (by norm_num)) G U hU hG (J 0) hanchor (fun h i => Y h i) hYcoord
  have hMm : Measurable M :=
    (source_empirical_factor_continuous_all_domains c C g p q alpha phi hc hC hp hq
      hphi hgrowth G U hU hDomains hG hN).measurable.comp hY
  have hGaussian := source_fresh_evaluation_gaussian nu lambda history innovation hH hInnovation
    hFresh hInnovationLaw evaluate hEvaluate Cov hField
  have hRaw : ∀ᵐ h ∂ rho, (k h).map (fun v => v) = multivariateGaussian 0 (Cov h) := by
    simpa only [Measure.map_id'] using hGaussian
  have hprops := sourceCanonicalWhiteningSeed_original_law rho k (fun _ v => v) measurable_snd
    M version Cov hM hMm hCm (hVersion.mono (fun _ h => h.2.1))
    (hVersion.mono (fun _ h => h.2.2)) hRaw
  rcases hprops with ⟨hseed,_,hjoint,hreproduce⟩
  let seed := fun h (z : EuclideanSpace Real (Fin N × Fin d) ×
      EuclideanSpace Real (Fin N × Fin d)) =>
    sourceCanonicalWhiteningSeed (M h) (hM h) (version h) z.1 z.2
  change Measurable (fun z : S × (EuclideanSpace Real (Fin N × Fin d) ×
    EuclideanSpace Real (Fin N × Fin d)) => seed z.1 z.2) at hseed
  let obs := fun z : O × EuclideanSpace Real (Fin N × Fin d) =>
    (history z.1,(raw z.1,z.2))
  have hobs : Measurable obs :=
    (hH.comp measurable_fst).prodMk ((hraw.comp measurable_fst).prodMk measurable_snd)
  have hobsLaw : (nu.prod normal).map obs = rho ⊗ₘ (k.prod (Kernel.const S normal)) :=
    source_original_auxiliary_observation_law nu history raw hH hraw normal
  refine ⟨hseed, ?_, ?_⟩
  . calc
      _ = ((nu.prod normal).map obs).map (fun z : S ×
          (EuclideanSpace Real (Fin N × Fin d) × EuclideanSpace Real (Fin N × Fin d)) =>
            (z.1, seed z.1 z.2)) := by
        rw [Measure.map_map (measurable_fst.prodMk hseed) hobs]
        rfl
      _ = _ := by rw [hobsLaw]; exact hjoint
  . have hMP : MeasurePreserving obs (nu.prod normal) (rho ⊗ₘ (k.prod (Kernel.const S normal))) :=
      ⟨hobs,hobsLaw⟩
    simpa only [source_matrixEuclideanOperator_eq_toEuclideanCLM] using
      hMP.quasiMeasurePreserving.ae hreproduce
end PaperFormalization.Manuscript
