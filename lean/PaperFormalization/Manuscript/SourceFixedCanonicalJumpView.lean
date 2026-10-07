import PaperFormalization.Manuscript.SourceOriginalCanonicalJump

/-! # The observed jump uses the fixed recursive coordinate
M13r verified unit (see CODEX_HANDOFF_M13R.md). This is the actual fixed whitening formula, not an unrelated
existential seed. Original vector values and reference updates are unchanged.
-/
open Matrix MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory Matrix.Norms.Frobenius
namespace PaperFormalization.Manuscript
attribute [local instance] sourceGramMeasurableMatrix sourceGramBorelMatrix
variable {O S Env W : Type*} [MeasurableSpace O] [MeasurableSpace S]
  [MeasurableSpace Env] [MeasurableSpace W] {N d : Nat}
variable {H : Nat -> Type*} [forall n, NormedAddCommGroup (H n)]
  [forall n, InnerProductSpace Real (H n)] [forall n, CompleteSpace (H n)]

/-- The version is pointwise natural in its kernel and sample; this equality
alone makes no assertion about integrability of either displayed integral. -/
theorem sourcePopulationGramVersion_congr_at
    {S' : Type*} [MeasurableSpace S']
    (k : Kernel S (EuclideanSpace Real (Fin d)))
    (k' : Kernel S' (EuclideanSpace Real (Fin d)))
    (J : EuclideanSpace Real (Fin d) -> lp H 2) (G : lp H 2 -> Real)
    (U : Set (lp H 2)) (anchor : lp H 2)
    (Y : S -> Fin N -> EuclideanSpace Real (Fin d))
    (Y' : S' -> Fin N -> EuclideanSpace Real (Fin d))
    (s : S) (s' : S') (hk : k s = k' s') (hY : Y s = Y' s') :
    sourcePopulationGramVersion k J G U anchor Y s =
      sourcePopulationGramVersion k' J G U anchor Y' s' := by
  simp only [sourcePopulationGramVersion, hk, hY]

set_option maxSynthPendingDepth 8 in
set_option maxHeartbeats 5000000 in
/-- Original fresh-field data construct an observed view with exactly the fixed
canonical seed. No observation-law or canonical-seed-law premise is added. -/
theorem exists_source_fixed_canonical_jump_view
    (c C g p q alpha K0 K D scale : Real)
    (phi : forall n, EuclideanSpace Real (Fin d) -> H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (halpha : 0 < alpha) (hK0 : 0 < K0) (hK : 0 < K) (hD : 1 ≤ D)
    (hscale : 0 < scale) (hKscale : K = sourceExponentialMomentCoefficient alpha * scale)
    (hphi : forall n, ContDiff Real 2 (phi n))
    (hgrowth : forall n z k, k ≤ 2 -> norm (iteratedFDeriv Real k (phi n) z) ≤
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
    let version := sourcePopulationGramVersion popLaw J G U (J 0) (fun h i => Y h i)
    let seed := fun h (z : EuclideanSpace Real (Fin N × Fin d) × EuclideanSpace Real (Fin N × Fin d)) =>
      sourceCanonicalWhiteningSeed (M h) (hM h) (version h) z.1 z.2
    ∃ view : SourceObservedJumpView c p K D alpha phi G U hU (hDomains K hK D hD) hG hN
        (nu.prod normal) S
        (EuclideanSpace Real (Fin N × Fin d) × EuclideanSpace Real (Fin N × Fin d)),
      view.κ = popLaw ∧
      view.PopGood = populationExponentialEligibility popLaw alpha scale ∧
      view.X = X ∧ view.Y = Y ∧ view.eta = eta ∧
      view.observation = (fun z => (history z.1, (evaluate (history z.1) (innovation z.1), z.2))) ∧
      view.seed = seed ∧
      Measurable (fun z : S × (EuclideanSpace Real (Fin N × Fin d) × EuclideanSpace Real (Fin N × Fin d)) => seed z.1 z.2) ∧
      (forall h z, particleFlatten (view.Xpost h z) = particleFlatten (X h) +
        eta • matrixEuclideanOperator (sourceEmpiricalKernelFactor c p phi G (X h)) (seed h z)) ∧
      (forall h z, particleFlatten (view.Ypost h z) = particleFlatten (Y h) + eta • z.1) := by
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
  let kext := k.prod (Kernel.const S normal)
  let M := fun h => sourceEmpiricalKernelFactor c p phi G (Y h)
  let hM := fun h => source_empirical_factor_hermitian_all_domains c p alpha phi G U hU hDomains hG hN (Y h)
  let Cov := fun h => populationGramCovariance (popLaw h)
    (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix J G
      (∫ x, J x ∂ popLaw h) (Y h i) z))
  let version := sourcePopulationGramVersion popLaw J G U (J 0) (fun h i => Y h i)
  let seed := fun h (z : EuclideanSpace Real (Fin N × Fin d) × EuclideanSpace Real (Fin N × Fin d)) =>
    sourceCanonicalWhiteningSeed (M h) (hM h) (version h) z.1 z.2
  have hfinite := source_full_history_finite_scales_of_reference_moments nu mu0 history past initial
    hH hpast hinit hPopIndependent hInitialLaw Phi hPhi alpha K0 halpha hK0 hMoment
  have hYcoord : forall i, Measurable (fun h => Y h i) := fun i =>
    ((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 _)).comp hY
  have hVersion := source_actual_gram_version_ae c C g p q alpha phi hc hC hp hq halpha
    hphi hgrowth G U hU hDomains hG rho popLaw hfinite (fun h i => Y h i) hYcoord
  have hJ := contDiff_sourceWeightedFeatureMap c C g p q phi hc hC hp hq hphi hgrowth
  have hanchor : J 0 ∈ U := hDomains 1 (by norm_num) 1 (by norm_num)
    (zero_anchor_mem_measureMomentRegion J _ 1 (by norm_num))
  have hCm := sourcePopulationGramVersion_measurable popLaw J hJ.continuous
    (hJ.continuous_fderiv (by norm_num)) G U hU hG (J 0) hanchor (fun h i => Y h i) hYcoord
  have hfactor := (source_empirical_factor_continuous_all_domains c C g p q alpha phi hc hC hp hq
    hphi hgrowth G U hU hDomains hG hN).measurable
  have hGaussian := source_fresh_evaluation_gaussian nu lambda history innovation hH hInnovation
    hFresh hInnovationLaw evaluate hEvaluate Cov hField
  have hRaw : ∀ᵐ h ∂ rho, (k h).map (fun v => v) = multivariateGaussian 0 (Cov h) := by
    simpa only [Measure.map_id'] using hGaussian
  rcases sourceCanonicalWhiteningSeed_original_law rho k (fun _ v => v) measurable_snd
    M version Cov hM (hfactor.comp hY) hCm
    (hVersion.mono (fun _ h => h.2.1)) (hVersion.mono (fun _ h => h.2.2)) hRaw with
    ⟨hseed, hseedLaw, _, hreproduce⟩
  let Xpost := fun h z => sourceParticleUnflatten (particleFlatten (X h) +
    eta • matrixEuclideanOperator (sourceEmpiricalKernelFactor c p phi G (X h)) (seed h z))
  let Ypost := fun h (z : EuclideanSpace Real (Fin N × Fin d) × EuclideanSpace Real (Fin N × Fin d)) =>
    sourceParticleUnflatten (particleFlatten (Y h) + eta • z.1)
  have hXpost : Measurable (fun z : S × (EuclideanSpace Real (Fin N × Fin d) × EuclideanSpace Real (Fin N × Fin d)) => Xpost z.1 z.2) := by
    apply sourceParticleUnflatten_measurable.comp
    apply ((sourceParticleFlatten_measurable.comp hX).comp measurable_fst).add
    have happ := measurable_matrix_euclidean_apply
      (fun z : S × (EuclideanSpace Real (Fin N × Fin d) × EuclideanSpace Real (Fin N × Fin d)) =>
        sourceEmpiricalKernelFactor c p phi G (X z.1)) (fun z => seed z.1 z.2)
      ((hfactor.comp hX).comp measurable_fst) hseed
    simpa only [source_matrixEuclideanOperator_eq_toEuclideanCLM, Function.comp_def, Pi.smul_apply] using (measurable_const_smul eta).comp happ
  have hYpost : Measurable (fun z : S × (EuclideanSpace Real (Fin N × Fin d) × EuclideanSpace Real (Fin N × Fin d)) => Ypost z.1 z.2) :=
    sourceParticleUnflatten_measurable.comp
      (((sourceParticleFlatten_measurable.comp hY).comp measurable_fst).add
        ((measurable_fst.comp measurable_snd).const_smul eta))
  let PopGood := populationExponentialEligibility popLaw alpha scale
  have hclass (h : S) (hh : h ∈ PopGood) : popLaw h ∈ sourceMomentClass alpha K := by
    rw [hKscale]
    exact sourceMomentClass_of_populationExponentialEligibility popLaw alpha scale halpha hscale h hh
  have hRep := Measure.ae_ae_of_ae_compProd hreproduce
  have hmodel : ∀ᵐ h ∂ rho, h ∈ PopGood ->
      popLaw h ∈ sourceMomentClass alpha K ∧ (kext h).map (seed h) = normal ∧
      forall hloc : (forall i, norm (X h i) ≤ D) ∧ (forall i, norm (Y h i) ≤ D),
        let hMYloc := sourceEmpiricalKernelFactor_isHermitian c p K D alpha phi G U hU
          (hDomains K hK D hD) hG (Y h) hN hloc.2
        ∀ᵐ z ∂ kext h,
          particleFlatten (Xpost h z) = particleFlatten (X h) +
            eta • matrixEuclideanOperator (sourceEmpiricalKernelFactor c p phi G (X h)) (seed h z) ∧
          particleFlatten (Ypost h z) = particleFlatten (Y h) +
            eta • matrixEuclideanOperator (alignedCovarianceFactor hMYloc (Cov h)) (seed h z) := by
    filter_upwards [hseedLaw, hRep] with h hs hr
    intro helig
    refine ⟨hclass h helig, hs, ?_⟩
    intro hloc
    filter_upwards [hr] with z hz
    refine ⟨particleFlatten_sourceParticleUnflatten _, ?_⟩
    have hactual : matrixEuclideanOperator
        (alignedCovarianceFactor (sourceEmpiricalKernelFactor_isHermitian c p K D alpha phi G U hU
          (hDomains K hK D hD) hG (Y h) hN hloc.2) (Cov h)) (seed h z) = z.1 := by
      simpa only [source_matrixEuclideanOperator_eq_toEuclideanCLM] using hz
    simp only [Ypost, particleFlatten_sourceParticleUnflatten, hactual]
  let observation := fun z : O × EuclideanSpace Real (Fin N × Fin d) =>
    (history z.1, (raw z.1, z.2))
  have hobs : Measurable observation :=
    (hH.comp measurable_fst).prodMk ((hraw.comp measurable_fst).prodMk measurable_snd)
  have hobsLaw : (nu.prod normal).map observation = rho ⊗ₘ kext :=
    source_original_auxiliary_observation_law nu history raw hH hraw normal
  have hParticleSpace :
      (inferInstance : MeasurableSpace (PiLp 2 fun _ : Fin N => EuclideanSpace Real (Fin d))) =
        instMeasurableSpaceObservedJumpParticles := BorelSpace.measurable_eq
  let view : SourceObservedJumpView c p K D alpha phi G U hU (hDomains K hK D hD) hG hN
      (nu.prod normal) S
      (EuclideanSpace Real (Fin N × Fin d) × EuclideanSpace Real (Fin N × Fin d)) := {
    ρ := rho, probability := inferInstance, k := kext, markov := inferInstance
    κ := popLaw, PopGood := PopGood
    measurable_popGood := measurableSet_populationExponentialEligibility popLaw alpha scale
    X := X, Y := Y, Xpost := Xpost, Ypost := Ypost
    measurable_X := by rw [← hParticleSpace]; exact hX
    measurable_Y := by rw [← hParticleSpace]; exact hY
    measurable_Xpost := by rw [← hParticleSpace]; exact hXpost
    measurable_Ypost := by rw [← hParticleSpace]; exact hYpost
    seed := seed, eta := eta, eta_nonneg := heta, source_model := hmodel
    observation := observation, measurable_observation := hobs, observation_law := hobsLaw }
  exact ⟨view, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hseed,
    (fun h z => particleFlatten_sourceParticleUnflatten _),
    (fun h z => particleFlatten_sourceParticleUnflatten _)⟩
end PaperFormalization.Manuscript
