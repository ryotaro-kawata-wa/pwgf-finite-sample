import PaperFormalization.Manuscript.SourceOriginalJumpView
import PaperFormalization.Manuscript.ConditionalAlignedSeedAE

/-! # The original jump construction with AE-measurable raw covariance

M13q verified unit (see CODEX_HANDOFF_M13Q.md). Measurable versions are chosen internally and
proved AE equal. Neither the original population evaluation nor the raw update
is changed. A totalized objective outside U need not have a Borel Hessian.
-/
open Matrix MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory MatrixOrder Matrix.Norms.Frobenius
namespace PaperFormalization.Manuscript
section General
variable {ι H Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace H] [MeasurableSpace Ω]
local instance sourceAEWhiteningMatrixSpace : MeasurableSpace (Matrix ι ι Real) := borel _
local instance sourceAEWhiteningMatrixBorel : BorelSpace (Matrix ι ι Real) := ⟨rfl⟩

/-- The original conditional Gaussian vector is whitened from AE-measurable
matrices, with no unproved measurability outside their original domain. -/
theorem source_conditional_aligned_seed_of_aemeasurable
    (ν : Measure H) [IsProbabilityMeasure ν] (k : Kernel H Ω) [IsMarkovKernel k]
    (v : H → Ω → EuclideanSpace ℝ ι) (M C : H → Matrix ι ι ℝ)
    (hv : Measurable (fun z : H × Ω => v z.1 z.2))
    (hM : AEMeasurable M ν) (hC : AEMeasurable C ν)
    (hsym : ∀ᵐ h ∂ν, (M h).IsHermitian) (hpos : ∀ᵐ h ∂ν, (C h).PosSemidef)
    (hLaw : ∀ᵐ h ∂ν, (k h).map (v h) = multivariateGaussian 0 (C h)) :
    ∃ (M' C' : H → Matrix ι ι ℝ) (hsym' : ∀ h, (M' h).IsHermitian),
      Measurable M' ∧ Measurable C' ∧ (∀ h, (C' h).PosSemidef) ∧
      M' =ᵐ[ν] M ∧ C' =ᵐ[ν] C ∧
      let kext := k.prod (Kernel.const H (stdGaussian (EuclideanSpace ℝ ι)))
      let B := fun h => toEuclideanCLM (𝕜 := ℝ) (alignedCovarianceFactor (hsym' h) (C' h))
      let D := fun h => toEuclideanCLM (𝕜 := ℝ) (alignedCovariancePseudoInverse (hsym' h) (C' h))
      let g := fun h (z : Ω × EuclideanSpace ℝ ι) => D h (v h z.1) + (1 - D h * B h) z.2
      Measurable (fun z : H × (Ω × EuclideanSpace ℝ ι) => g z.1 z.2) ∧
        (ν ⊗ₘ kext).map (fun z : H × (Ω × EuclideanSpace ℝ ι) => (z.1, z.2.1)) = ν ⊗ₘ k ∧
        (∀ᵐ h ∂ν, (kext h).map (g h) = stdGaussian (EuclideanSpace ℝ ι)) ∧
        (ν ⊗ₘ kext).map (fun z : H × (Ω × EuclideanSpace ℝ ι) => (z.1, g z.1 z.2)) =
          ν.prod (stdGaussian (EuclideanSpace ℝ ι)) ∧
        (ν ⊗ₘ kext).map (fun z : H × (Ω × EuclideanSpace ℝ ι) => g z.1 z.2) =
          stdGaussian (EuclideanSpace ℝ ι) ∧
        IndepFun Prod.fst (fun z : H × (Ω × EuclideanSpace ℝ ι) => g z.1 z.2) (ν ⊗ₘ kext) ∧
        ∀ᵐ z ∂ν ⊗ₘ kext, B z.1 (g z.1 z.2) = v z.1 z.2.1 := by
  let M0 := hM.mk M
  let C0 := hC.mk C
  have hsym0 : ∀ᵐ h ∂ν, (M0 h).IsHermitian := by
    filter_upwards [hsym, hM.ae_eq_mk] with h hh he
    change M h = M0 h at he
    rwa [← he]
  have hpos0 : ∀ᵐ h ∂ν, (C0 h).PosSemidef := by
    filter_upwards [hpos, hC.ae_eq_mk] with h hh he
    change C h = C0 h at he
    rwa [← he]
  have hlaw0 : ∀ᵐ h ∂ν, (k h).map (v h) = multivariateGaussian 0 (C0 h) := by
    filter_upwards [hLaw, hC.ae_eq_mk] with h hh he
    change C h = C0 h at he
    rwa [← he]
  obtain ⟨M', C', hsym', hm', hc', hpos', hMeq, hCeq, hprops⟩ :=
    conditional_aligned_seed_joint_properties_of_ae ν k v M0 C0 hv
      hM.measurable_mk hC.measurable_mk hsym0 hpos0 hlaw0
  exact ⟨M', C', hsym', hm', hc', hpos', hMeq.trans hM.ae_eq_mk.symm,
    hCeq.trans hC.ae_eq_mk.symm, hprops⟩

end General

variable {O S : Type*} [MeasurableSpace O] [MeasurableSpace S] {N d : ℕ}
variable {H : ℕ -> Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

local instance sourceAEJumpMatrixMeasurable :
    MeasurableSpace (Matrix (Fin N × Fin d) (Fin N × Fin d) ℝ) := borel _
local instance sourceAEJumpMatrixBorel :
    BorelSpace (Matrix (Fin N × Fin d) (Fin N × Fin d) ℝ) := ⟨rfl⟩

set_option maxHeartbeats 2400000 in
/-- Build an actual observed jump view. `hGaussian` is the original population
GP finite-evaluation law. No observation-law, finite-seed-law, aligned-update,
conditional-iid or scalar comparison premise is supplied. The raw matrix
measurability and AE symmetry/positivity are the model-level obligations named
explicitly by the population-first finite coupling lemma. -/
theorem exists_source_original_jump_view_ae_covariance
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
    (hCov : AEMeasurable (fun h => populationGramCovariance (popLaw h)
      (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix
        (sourceWeightedFeatureMap c p phi) G
        (∫ x, sourceWeightedFeatureMap c p phi x ∂popLaw h) (Y h i) z))) (nu.map history))
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
    source_conditional_aligned_seed_of_aemeasurable ρ k (fun _ v => v) MY Cov
      measurable_snd hMY.aemeasurable hCov hSym hPos hRaw
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
      (fun z : S × (EuclideanSpace ℝ (Fin N × Fin d) × EuclideanSpace ℝ (Fin N × Fin d)) => sourceEmpiricalKernelFactor c p phi G (X z.1))
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
      (inferInstance : MeasurableSpace (PiLp 2 fun _ : Fin N => EuclideanSpace Real (Fin d))) =
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
