import PaperFormalization.Manuscript.SourceAEJumpConstruction
import PaperFormalization.Manuscript.SourceActualGramRegularity

/-! # Original jumps with all matrix-side obligations discharged from source data

M13q verified unit (see CODEX_HANDOFF_M13Q.md). The five old inputs hMX, hMY, hCov, hSym, hPos
are conclusions here. The original unconditional reference marginal controls
AE random population scales, not an almost-sure deterministic conditional scale.
The raw GP finite-evaluation law is still a primitive stochastic-model input;
it can be obtained at augmented histories by SourceFreshInnovationLaw.
-/
open Matrix MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory MatrixOrder Matrix.Norms.Frobenius
namespace PaperFormalization.Manuscript
attribute [local instance] sourceGramMeasurableMatrix sourceGramBorelMatrix
variable {O S : Type*} [MeasurableSpace O] [MeasurableSpace S] {N d : Nat}
variable {H : Nat -> Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace Real (H n)] [∀ n, CompleteSpace (H n)]
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 3000000 in
/-- Construct the original jump using source analytic hypotheses, genuine
unconditional moments and the raw population Gaussian law. There is no input
matrix regularity/PSD/symmetry, whitened-seed law or observation-law estimate. -/
theorem exists_source_analytic_original_jump_view
    (c C g p q K D alpha K0 : ℝ) (phi : ∀ n, EuclideanSpace ℝ (Fin d) -> H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hK : 0 < K) (hD : 1 ≤ D) (halpha : 0 < alpha) (hK0 : 0 < K0)
    (hphi : ∀ n, ContDiff Real 2 (phi n))
    (hgrowth : ∀ n z k, k ≤ 2 -> norm (iteratedFDeriv Real k (phi n) z) ≤
      featureGrowth C g q n * (1 + norm z ^ (n+1-k)))
    (G : lp H 2 -> ℝ) (U : Set (lp H 2)) (hU : IsOpen U)
    (hDomains : SourceAllMomentDomains (sourceWeightedFeatureMap c p phi) alpha U)
    (hG : ContDiffOn ℝ 2 G U) (hN : 0 < N)
    (nu : Measure O) [IsProbabilityMeasure nu]
    (history : O -> S) (population : O -> EuclideanSpace ℝ (Fin N × Fin d))
    (hhistory : Measurable history) (hpopulation : Measurable population)
    (popLaw : Kernel S (EuclideanSpace ℝ (Fin d))) [IsMarkovKernel popLaw]
    (PopGood : Set S) (hPopGood : MeasurableSet PopGood)
    (hclass : ∀ᵐ h ∂nu.map history, h ∈ PopGood -> popLaw h ∈ sourceMomentClass alpha K)
    (X Y : S -> PiLp 2 (fun _ : Fin N => EuclideanSpace ℝ (Fin d)))
    (hX : Measurable X) (hY : Measurable Y) (eta : ℝ) (heta : 0 ≤ eta)
    (hUnconditional : ((nu.map history) ⊗ₘ popLaw).map Prod.snd ∈
      sourceMomentClass alpha K0)
    (hGaussian : ∀ᵐ h ∂nu.map history,
      condDistrib population history nu h = multivariateGaussian 0
        (populationGramCovariance (popLaw h)
          (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix
            (sourceWeightedFeatureMap c p phi) G
            (∫ x, sourceWeightedFeatureMap c p phi x ∂popLaw h) (Y h i) z)))) :
    let normal := stdGaussian (EuclideanSpace ℝ (Fin N × Fin d))
    ∃ view : SourceObservedJumpView c p K D alpha phi G U hU (hDomains K hK D hD) hG hN
      (nu.prod normal) S
      (EuclideanSpace ℝ (Fin N × Fin d) × EuclideanSpace ℝ (Fin N × Fin d)),
      view.κ = popLaw ∧ view.PopGood = PopGood ∧
      view.X = X ∧ view.Y = Y ∧ view.eta = eta ∧
      view.observation = (fun z => (history z.1, (population z.1, z.2))) ∧
      Measurable (fun z : S × (EuclideanSpace ℝ (Fin N × Fin d) × EuclideanSpace ℝ (Fin N × Fin d)) => view.seed z.1 z.2) ∧
      (∀ᵐ h ∂nu.map history, (view.k h).map (view.seed h) = normal) ∧
      (∀ h z, particleFlatten (view.Ypost h z) = particleFlatten (Y h) + eta • z.1) ∧
      (∀ h z, particleFlatten (view.Xpost h z) = particleFlatten (X h) +
        eta • matrixEuclideanOperator (sourceEmpiricalKernelFactor c p phi G (X h)) (view.seed h z)) ∧
      (nu.prod normal).map (fun z => (history z.1, view.seed (view.observation z).1 (view.observation z).2)) =
        (nu.map history).prod normal := by
  let rho := nu.map history
  letI : IsProbabilityMeasure rho := Measure.isProbabilityMeasure_map hhistory.aemeasurable
  have hfinite := source_ae_finite_scale_of_mixture_class rho popLaw alpha K0 halpha hK0 hUnconditional
  have hregular := source_actual_gram_regular_of_finite_scales c C g p q alpha phi
    hc hC hp hq halpha hphi hgrowth G U hU hDomains hG rho popLaw hfinite
    (fun h i => Y h i) (fun i =>
      (PiLp.proj (𝕜 := Real) 2 (fun _ : Fin N => EuclideanSpace Real (Fin d)) i).continuous.measurable.comp hY)
  have hM := source_empirical_factor_continuous_all_domains c C g p q alpha phi
    hc hC hp hq hphi hgrowth G U hU hDomains hG hN
  exact exists_source_original_jump_view_ae_covariance c p K D alpha phi G U hU
    (hDomains K hK D hD) hG hN nu history population hhistory hpopulation popLaw
    PopGood hPopGood hclass X Y hX hY eta heta (hM.measurable.comp hX)
    (hM.measurable.comp hY) hregular.1
    (Filter.Eventually.of_forall (fun h => source_empirical_factor_hermitian_all_domains
      c p alpha phi G U hU hDomains hG hN (Y h)))
    (hregular.2.mono (fun _ h => h.2.1)) hGaussian

end PaperFormalization.Manuscript
