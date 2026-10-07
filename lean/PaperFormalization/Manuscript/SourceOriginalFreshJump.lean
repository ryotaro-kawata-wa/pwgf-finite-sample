import PaperFormalization.Manuscript.SourceAnalyticJumpConstruction
import PaperFormalization.Manuscript.SourceFreshInnovationLaw
import PaperFormalization.Manuscript.SourceOriginalCoefficientMixture
import PaperFormalization.Manuscript.PrehistoryPopulationEligibility

/-! # One original jump from source analytic data, initial seeds and a fresh field

M13q verified unit (see CODEX_HANDOFF_M13Q.md). The history may contain the observed initial
sample and all past auxiliary coordinates. It excludes the current innovation.
The population coefficient is constructed from its actual characteristic map;
its mixture is identified with the original reference marginal. The raw
conditional Gaussian law, all five matrix-side inputs, and eligibility-to-class
implication are derived internally. No future event is used for conditioning.
-/
open Matrix MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory MatrixOrder Matrix.Norms.Frobenius
namespace PaperFormalization.Manuscript
variable {O S Env W : Type*} [MeasurableSpace O] [MeasurableSpace S]
  [MeasurableSpace Env] [MeasurableSpace W] {N d : Nat}
variable {H : Nat -> Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace Real (H n)] [∀ n, CompleteSpace (H n)]
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 4000000 in
/-- The source raw Gaussian FIELD law is under the primitive fresh innovation,
not supplied as an already conditioned vector law or a whitened-seed law.
The all-real unconditional moment belongs to the original reference observable.
The exact coefficient law is returned pointwise for every history. -/
theorem exists_source_original_fresh_jump
    (c C g p q K D alpha K0 scale : Real)
    (phi : ∀ n, EuclideanSpace Real (Fin d) -> H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hK : 0 < K) (hD : 1 ≤ D) (halpha : 0 < alpha) (hK0 : 0 < K0)
    (hscale : 0 < scale) (hKscale : K = sourceExponentialMomentCoefficient alpha * scale)
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
    (X Y : S -> PiLp 2 (fun _ : Fin N => EuclideanSpace Real (Fin d)))
    (hX : Measurable X) (hY : Measurable Y) (eta : Real) (heta : 0 ≤ eta)
    (evaluate : S -> W -> EuclideanSpace Real (Fin N × Fin d))
    (hEvaluate : Measurable (fun z : S × W => evaluate z.1 z.2))
    (hField : let popLaw := characteristicKernel mu0 (fun h u => Phi (past h) u)
      ∀ᵐ h ∂ nu.map history,
        lambda.map (evaluate h) = multivariateGaussian 0
          (populationGramCovariance (popLaw h)
            (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix
              (sourceWeightedFeatureMap c p phi) G
              (∫ x, sourceWeightedFeatureMap c p phi x ∂ popLaw h) (Y h i) z)))) :
    let popLaw := characteristicKernel mu0 (fun h u => Phi (past h) u)
    let normal := stdGaussian (EuclideanSpace Real (Fin N × Fin d))
    ∃ view : SourceObservedJumpView c p K D alpha phi G U hU (hDomains K hK D hD) hG hN
        (nu.prod normal) S
        (EuclideanSpace Real (Fin N × Fin d) × EuclideanSpace Real (Fin N × Fin d)),
      (view.κ = popLaw ∧
       view.PopGood = populationExponentialEligibility popLaw alpha scale ∧
       view.X = X ∧ view.Y = Y ∧ view.eta = eta ∧
       view.observation = (fun z => (history z.1, (evaluate (history z.1) (innovation z.1), z.2))) ∧
       Measurable (fun z : S × (EuclideanSpace Real (Fin N × Fin d) ×
         EuclideanSpace Real (Fin N × Fin d)) => view.seed z.1 z.2) ∧
       (∀ᵐ h ∂ nu.map history, (view.k h).map (view.seed h) = normal) ∧
       (∀ h z, particleFlatten (view.Ypost h z) = particleFlatten (Y h) + eta • z.1) ∧
       (∀ h z, particleFlatten (view.Xpost h z) = particleFlatten (X h) +
         eta • matrixEuclideanOperator (sourceEmpiricalKernelFactor c p phi G (X h)) (view.seed h z)) ∧
       (nu.prod normal).map (fun z => (history z.1,
         view.seed (view.observation z).1 (view.observation z).2)) =
         (nu.map history).prod normal) ∧
      (∀ h, view.κ h = mu0.map (Phi (past h))) := by
  let popLaw := characteristicKernel mu0 (fun h u => Phi (past h) u)
  have hPhiFull : Measurable (fun z : S × EuclideanSpace Real (Fin d) => Phi (past z.1) z.2) :=
    hPhi.comp ((hpast.comp measurable_fst).prodMk measurable_snd)
  letI : IsMarkovKernel popLaw := (characteristicKernel_properties mu0 _ hPhiFull).1
  have hMix : ((nu.map history) ⊗ₘ popLaw).map Prod.snd ∈ sourceMomentClass alpha K0 := by
    rw [source_full_history_coefficient_mixture nu mu0 history past initial hH hpast hinit
      hPopIndependent hInitialLaw Phi hPhi]
    exact hMoment
  let PopGood := populationExponentialEligibility popLaw alpha scale
  have hclass : ∀ᵐ h ∂ nu.map history, h ∈ PopGood -> popLaw h ∈ sourceMomentClass alpha K := by
    filter_upwards with h
    intro hh
    rw [hKscale]
    exact sourceMomentClass_of_populationExponentialEligibility popLaw alpha scale halpha hscale h hh
  have hGaussian := source_fresh_evaluation_gaussian nu lambda history innovation hH hInnovation
    hFresh hInnovationLaw evaluate hEvaluate
    (fun h => populationGramCovariance (popLaw h)
      (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix
        (sourceWeightedFeatureMap c p phi) G
        (∫ x, sourceWeightedFeatureMap c p phi x ∂popLaw h) (Y h i) z))) hField
  obtain ⟨view, hview⟩ := exists_source_analytic_original_jump_view
    c C g p q K D alpha K0 phi hc hC hp hq hK hD halpha hK0 hphi hgrowth
    G U hU hDomains hG hN nu history
    (fun o => evaluate (history o) (innovation o)) hH (hEvaluate.comp (hH.prodMk hInnovation))
    popLaw PopGood (measurableSet_populationExponentialEligibility popLaw alpha scale)
    hclass X Y hX hY eta heta hMix hGaussian
  refine ⟨view, hview, ?_⟩
  intro h
  rw [hview.1]
  exact (characteristicKernel_properties mu0 _ hPhiFull).2 h
end PaperFormalization.Manuscript
