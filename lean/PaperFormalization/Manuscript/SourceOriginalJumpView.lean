import PaperFormalization.Manuscript.SourceOriginalObservationExtension
import PaperFormalization.Manuscript.SourceParticleUnflatten
import PaperFormalization.Manuscript.SourceObservedJumpSchedule

/-! # Construct the source jump view from the original population Gaussian vector

M13p verified unit (see CODEX_HANDOFF_M13P.md). The primitive Gaussian input is the population
FIELD EVALUATION conditional on the prehistory, as in the manuscript, not a
standard finite seed independent of the reference particles. A fresh auxiliary
normal is added to the original experiment. Whitening, its Gaussian law, both
updates, and the view observation law are derived. Matrix structure is only AE;
measurable representatives do not alter the original states or population vector.
-/
open Matrix MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory MatrixOrder Matrix.Norms.Frobenius
set_option maxSynthPendingDepth 8
namespace PaperFormalization.Manuscript

/-- The two existing finite-matrix operator interfaces have the same action. -/
theorem source_matrixEuclideanOperator_eq_toEuclideanCLM
    {I : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I ℝ) :
    matrixEuclideanOperator M = Matrix.toEuclideanCLM (𝕜 := ℝ) M := by
  ext x i
  rfl

/-- Transport the actual aligned factor across matrix equalities, including
its dependent Hermitian proof argument. -/
theorem source_alignedCovarianceFactor_congr
    {I : Type*} [Fintype I] [DecidableEq I] {M M' C C' : Matrix I I ℝ}
    (hM : M.IsHermitian) (hM' : M'.IsHermitian) (hm : M = M') (hc : C = C') :
    alignedCovarianceFactor hM C = alignedCovarianceFactor hM' C' := by
  subst M'
  subst C'
  rfl

variable {O S : Type*} [MeasurableSpace O] [MeasurableSpace S] {N d : ℕ}
variable {H : ℕ -> Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

local instance sourceJumpViewMatrixMeasurable :
    MeasurableSpace (Matrix (Fin N × Fin d) (Fin N × Fin d) ℝ) := borel _
local instance sourceJumpViewMatrixBorel :
    BorelSpace (Matrix (Fin N × Fin d) (Fin N × Fin d) ℝ) := ⟨rfl⟩

set_option maxHeartbeats 2400000 in
/-- Build an actual observed jump view. `hGaussian` is the original population
GP finite-evaluation law. No observation-law, finite-seed-law, aligned-update,
conditional-iid or scalar comparison premise is supplied. The raw matrix
measurability and AE symmetry/positivity are the model-level obligations named
explicitly by the population-first finite coupling lemma. -/
theorem exists_source_original_jump_view
    (c p K D alpha : ℝ) (phi : ∀ n, EuclideanSpace ℝ (Fin d) -> H n)
    (G : lp H 2 -> ℝ) (U : Set (lp H 2)) (hU : IsOpen U)
    (hSU : measureMomentRegion (sourceWeightedFeatureMap c p phi)
      (sourceMomentClass alpha K) D ⊆ U)
    (hG : ContDiffOn ℝ 2 G U) (hN : 0 < N)
    (nu : Measure O) [IsProbabilityMeasure nu]
    (history : O -> S) (population : O -> EuclideanSpace ℝ (Fin N × Fin d))
    (hhistory : Measurable history) (hpopulation : Measurable population)
    (popLaw : Kernel S (EuclideanSpace ℝ (Fin d))) [IsMarkovKernel popLaw]
    (PopGood : Set S) (hPopGood : MeasurableSet PopGood)
    (hclass : ∀ᵐ h ∂nu.map history, h ∈ PopGood -> popLaw h ∈ sourceMomentClass alpha K)
    (X Y : S -> PiLp 2 (fun _ : Fin N => EuclideanSpace ℝ (Fin d)))
    (hX : Measurable X) (hY : Measurable Y) (eta : ℝ) (heta : 0 ≤ eta)
    (hMX : Measurable (fun h => sourceEmpiricalKernelFactor c p phi G (X h)))
    (hMY : Measurable (fun h => sourceEmpiricalKernelFactor c p phi G (Y h)))
    (hCov : Measurable (fun h => populationGramCovariance (popLaw h)
      (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix
        (sourceWeightedFeatureMap c p phi) G
        (∫ x, sourceWeightedFeatureMap c p phi x ∂popLaw h) (Y h i) z))))
    (hSym : ∀ᵐ h ∂nu.map history, (sourceEmpiricalKernelFactor c p phi G (Y h)).IsHermitian)
    (hPos : ∀ᵐ h ∂nu.map history, (populationGramCovariance (popLaw h)
      (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix
        (sourceWeightedFeatureMap c p phi) G
        (∫ x, sourceWeightedFeatureMap c p phi x ∂popLaw h) (Y h i) z))).PosSemidef)
    (hGaussian : ∀ᵐ h ∂nu.map history,
      condDistrib population history nu h = multivariateGaussian 0
        (populationGramCovariance (popLaw h)
          (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix
            (sourceWeightedFeatureMap c p phi) G
            (∫ x, sourceWeightedFeatureMap c p phi x ∂popLaw h) (Y h i) z)))) :
    let normal := stdGaussian (EuclideanSpace ℝ (Fin N × Fin d))
    ∃ view : SourceObservedJumpView c p K D alpha phi G U hU hSU hG hN
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
  let ρ := nu.map history
  letI : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_map hhistory.aemeasurable
  let normal := stdGaussian (EuclideanSpace ℝ (Fin N × Fin d))
  let k := condDistrib population history nu
  let MY := fun h => sourceEmpiricalKernelFactor c p phi G (Y h)
  let Cov := fun h => populationGramCovariance (popLaw h)
    (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix
      (sourceWeightedFeatureMap c p phi) G
      (∫ x, sourceWeightedFeatureMap c p phi x ∂popLaw h) (Y h i) z))
  have hRaw : ∀ᵐ h ∂ρ, (k h).map (fun v => v) = multivariateGaussian 0 (Cov h) := by
    simpa only [Measure.map_id'] using hGaussian
  obtain ⟨M', C', hsym', hm', hc', hpos', hMeq, hCeq, hprops⟩ :=
    conditional_aligned_seed_joint_properties_of_ae ρ k (fun _ v => v) MY Cov
      measurable_snd hMY hCov hSym hPos hRaw
  let kext := k.prod (Kernel.const S normal)
  let B := fun h => Matrix.toEuclideanCLM (𝕜 := ℝ) (alignedCovarianceFactor (hsym' h) (C' h))
  let Q := fun h => Matrix.toEuclideanCLM (𝕜 := ℝ) (alignedCovariancePseudoInverse (hsym' h) (C' h))
  let seed := fun h (z : EuclideanSpace ℝ (Fin N × Fin d) × EuclideanSpace ℝ (Fin N × Fin d)) =>
    Q h z.1 + (1-Q h*B h) z.2
  rcases hprops with ⟨hseed, _, hseedLaw, hseedJoint, _, _, hreproduce⟩
  have hRep := Measure.ae_ae_of_ae_compProd hreproduce
  let Xpost := fun h z => sourceParticleUnflatten (particleFlatten (X h) +
    eta • matrixEuclideanOperator (sourceEmpiricalKernelFactor c p phi G (X h)) (seed h z))
  let Ypost := fun h (z : EuclideanSpace ℝ (Fin N × Fin d) × EuclideanSpace ℝ (Fin N × Fin d)) =>
    sourceParticleUnflatten (particleFlatten (Y h) + eta • z.1)
  have hXpost : Measurable (fun z : S × (EuclideanSpace ℝ (Fin N × Fin d) × EuclideanSpace ℝ (Fin N × Fin d)) => Xpost z.1 z.2) := by
    apply sourceParticleUnflatten_measurable.comp
    apply ((sourceParticleFlatten_measurable.comp hX).comp measurable_fst).add
    have happ := measurable_matrix_euclidean_apply
      (fun z : S × (EuclideanSpace ℝ (Fin N × Fin d) × EuclideanSpace ℝ (Fin N × Fin d)) =>
        sourceEmpiricalKernelFactor c p phi G (X z.1))
      (fun z => seed z.1 z.2) (hMX.comp measurable_fst) hseed
    simpa only [source_matrixEuclideanOperator_eq_toEuclideanCLM, Function.comp_def] using
      (measurable_const_smul eta).comp happ
  have hYpost : Measurable (fun z : S × (EuclideanSpace ℝ (Fin N × Fin d) × EuclideanSpace ℝ (Fin N × Fin d)) => Ypost z.1 z.2) :=
    sourceParticleUnflatten_measurable.comp
      (((sourceParticleFlatten_measurable.comp hY).comp measurable_fst).add
        ((measurable_fst.comp measurable_snd).const_smul eta))
  have hmodel : ∀ᵐ h ∂ρ, h ∈ PopGood ->
      popLaw h ∈ sourceMomentClass alpha K ∧
      (kext h).map (seed h) = normal ∧
      ∀ hloc : (∀ i, ‖X h i‖ ≤ D) ∧ (∀ i, ‖Y h i‖ ≤ D),
        let hMYloc := sourceEmpiricalKernelFactor_isHermitian c p K D alpha phi G U hU hSU hG (Y h) hN hloc.2
        ∀ᵐ z ∂kext h,
          particleFlatten (Xpost h z) = particleFlatten (X h) +
            eta • matrixEuclideanOperator (sourceEmpiricalKernelFactor c p phi G (X h)) (seed h z) ∧
          particleFlatten (Ypost h z) = particleFlatten (Y h) +
            eta • matrixEuclideanOperator (alignedCovarianceFactor hMYloc (Cov h)) (seed h z) := by
    filter_upwards [hclass, hMeq, hCeq, hseedLaw, hRep] with h hh hm hc hg hr
    intro helig
    refine ⟨hh helig, hg, ?_⟩
    intro hloc
    let hMYloc := sourceEmpiricalKernelFactor_isHermitian c p K D alpha phi G U hU hSU hG (Y h) hN hloc.2
    have hB := source_alignedCovarianceFactor_congr (hsym' h) hMYloc hm hc
    filter_upwards [hr] with z hz
    refine ⟨particleFlatten_sourceParticleUnflatten _, ?_⟩
    have hactual : matrixEuclideanOperator (alignedCovarianceFactor hMYloc (Cov h)) (seed h z) = z.1 := by
      rw [source_matrixEuclideanOperator_eq_toEuclideanCLM, <- hB]
      exact hz
    simp only [Ypost, particleFlatten_sourceParticleUnflatten, hactual]
  let observation := fun z : O × EuclideanSpace ℝ (Fin N × Fin d) =>
    (history z.1, (population z.1, z.2))
  have hobs : Measurable observation :=
    (hhistory.comp measurable_fst).prodMk ((hpopulation.comp measurable_fst).prodMk measurable_snd)
  have hobsLaw : (nu.prod normal).map observation = ρ ⊗ₘ kext :=
    source_original_auxiliary_observation_law nu history population hhistory hpopulation normal
  have hParticleSpace :
      (inferInstance : MeasurableSpace (PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d))) =
        instMeasurableSpaceObservedJumpParticles := BorelSpace.measurable_eq
  let view : SourceObservedJumpView c p K D alpha phi G U hU hSU hG hN (nu.prod normal) S
      (EuclideanSpace ℝ (Fin N × Fin d) × EuclideanSpace ℝ (Fin N × Fin d)) := {
    ρ := ρ
    probability := inferInstance
    k := kext
    markov := inferInstance
    κ := popLaw
    PopGood := PopGood
    measurable_popGood := hPopGood
    X := X
    Y := Y
    Xpost := Xpost
    Ypost := Ypost
    measurable_X := by rw [← hParticleSpace]; exact hX
    measurable_Y := by rw [← hParticleSpace]; exact hY
    measurable_Xpost := by rw [← hParticleSpace]; exact hXpost
    measurable_Ypost := by rw [← hParticleSpace]; exact hYpost
    seed := seed
    eta := eta
    eta_nonneg := heta
    source_model := hmodel
    observation := observation
    measurable_observation := hobs
    observation_law := hobsLaw }
  refine ⟨view, rfl, rfl, rfl, rfl, rfl, rfl, hseed, hseedLaw,
    (fun h z => particleFlatten_sourceParticleUnflatten _),
    (fun h z => particleFlatten_sourceParticleUnflatten _), ?_⟩
  calc
    _ = ((nu.prod normal).map observation).map (fun z => (z.1, seed z.1 z.2)) := by
      rw [Measure.map_map (measurable_fst.prodMk hseed) hobs]
      rfl
    _ = (ρ ⊗ₘ kext).map (fun z => (z.1, seed z.1 z.2)) := by rw [hobsLaw]
    _ = _ := hseedJoint

end PaperFormalization.Manuscript
