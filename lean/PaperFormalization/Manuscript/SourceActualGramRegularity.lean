import PaperFormalization.Manuscript.SourceGlobalEmpiricalRegularity
import PaperFormalization.Manuscript.SourceFiniteConditionalScale
import PaperFormalization.Manuscript.SourcePopulationGram
import PaperFormalization.Manuscript.SourceTensorCovarianceIntegrability

/-! # The actual population Gram covariance: measurable version and true integrals

M13q verified unit (see CODEX_HANDOFF_M13Q.md). The version uses the original U anchor only
outside U. On the original ∀ᵐ finite-scale set it equals the actual covariance.
No sample localization, separability of the feature Hilbert spaces, covariance
measurability premise, or assumption of Gram integrability is introduced.
-/
open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius ProbabilityTheory
namespace PaperFormalization.Manuscript
variable {S : Type*} [MeasurableSpace S] {N d : Nat}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
noncomputable local instance sourceGramContinuousENormMatrix :
    ContinuousENorm (Matrix (Fin N × Fin d) (Fin N × Fin d) Real) :=
  SeminormedAddGroup.toContinuousENorm
local instance sourceGramMeasurableMatrix :
    MeasurableSpace (Matrix (Fin N × Fin d) (Fin N × Fin d) Real) := borel _
local instance sourceGramBorelMatrix :
    BorelSpace (Matrix (Fin N × Fin d) (Fin N × Fin d) Real) := ⟨rfl⟩

/-- Genuine tensor integration identifies the actual population covariance,
not merely the population-minus-empirical residual. -/
theorem source_actual_gram_eq_tensor
    (J : EuclideanSpace Real (Fin d) -> H) (G : H -> Real) (theta : H)
    (mu : Measure (EuclideanSpace Real (Fin d))) (Y : Fin N -> EuclideanSpace Real (Fin d))
    (hG : ContDiffAt Real 2 G theta)
    (hW : Integrable (fun x => finiteOperatorCovariance (fderiv Real J x)) mu) :
    populationGramCovariance mu
      (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix J G theta (Y i) z)) =
      hilbertTensorCompression (actualMomentTensorColumns J G theta Y)
        (∫ x, finiteOperatorCovariance (fderiv Real J x) ∂mu) := by
  rw [hilbertTensorCompression_integral mu _ _ hW]
  unfold populationGramCovariance
  apply integral_congr_ae
  filter_upwards with z
  rw [stacked_actualMomentKernelMatrix_eq_column_inner J G theta Y z hG]
  exact (hilbertTensorCompression_finiteColumnCovariance
    (actualMomentTensorColumns J G theta Y) (actualFeatureDerivativeColumns J z)).symm

/-- A Borel version; its values outside the actual domain are not used as
population covariance or as evidence for integrability. -/
noncomputable def sourcePopulationGramVersion
    (kappa : Kernel S (EuclideanSpace Real (Fin d)))
    (J : EuclideanSpace Real (Fin d) -> H) (G : H -> Real) (U : Set H) (anchor : H)
    (Y : S -> Fin N -> EuclideanSpace Real (Fin d)) (h : S) :
    Matrix (Fin N × Fin d) (Fin N × Fin d) Real :=
  hilbertTensorCompression
    (actualMomentTensorColumns J G (openMomentParameter U anchor (∫ x, J x ∂kappa h)) (Y h))
    (∫ x, finiteOperatorCovariance (fderiv Real J x) ∂kappa h)

/-- Strong measurability precedes finite scalar matrix assembly. The moment
and tensor targets need not be separable. -/
theorem sourcePopulationGramVersion_measurable
    (kappa : Kernel S (EuclideanSpace Real (Fin d))) [IsMarkovKernel kappa]
    (J : EuclideanSpace Real (Fin d) -> H) (hJ : Continuous J)
    (hDJ : Continuous (fderiv Real J)) (G : H -> Real) (U : Set H)
    (hU : IsOpen U) (hG : ContDiffOn Real 2 G U) (anchor : H) (hanchor : anchor ∈ U)
    (Y : S -> Fin N -> EuclideanSpace Real (Fin d)) (hY : ∀ i, Measurable (fun h => Y h i)) :
    Measurable (sourcePopulationGramVersion kappa J G U anchor Y) := by
  have htheta : StronglyMeasurable (fun h : S => ∫ x, J x ∂kappa h) :=
    hJ.stronglyMeasurable.integral_kernel
  have hh := stronglyMeasurable_openMomentHessian G U hU hG anchor hanchor _ htheta
  have hcol (i : Fin N × Fin d) : StronglyMeasurable
      (fun h : S => actualFeatureDerivativeColumns J (Y h i.1) i.2) :=
    (hDJ.clm_apply continuous_const).comp_stronglyMeasurable (hY i.1).stronglyMeasurable
  have hrow (i : Fin N × Fin d) : StronglyMeasurable
      (fun h : S => actualMomentTensorColumns J G
        (openMomentParameter U anchor (∫ x, J x ∂kappa h)) (Y h) i) :=
    (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable (hh.prodMk (hcol i))
  have hpop : StronglyMeasurable (fun h : S =>
      ∫ x, finiteOperatorCovariance (fderiv Real J x) ∂kappa h) :=
    (continuous_finiteOperatorCovariance.comp hDJ).stronglyMeasurable.integral_kernel
  have hentry (i j : Fin N × Fin d) : StronglyMeasurable
      (fun h => sourcePopulationGramVersion kappa J G U anchor Y h i j) := by
    have hpure := ((hilbertPureTensor.continuous.comp continuous_fst).clm_apply continuous_snd).comp_stronglyMeasurable ((hrow i).prodMk (hrow j))
    exact (continuous_fst.inner continuous_snd).comp_stronglyMeasurable (hpure.prodMk hpop)
  let assemble : ((Fin N × Fin d) -> (Fin N × Fin d) -> Real) ->
      Matrix (Fin N × Fin d) (Fin N × Fin d) Real :=
    fun v => ∑ i, ∑ j, v i j • Matrix.single i j (1 : Real)
  have ha : Continuous assemble := by unfold assemble; fun_prop
  have he := measurable_pi_lambda _ (fun i =>
    measurable_pi_lambda _ (fun j => (hentry i j).measurable))
  convert ha.measurable.comp he using 1
  funext h
  simpa only [Function.comp_def, assemble, Matrix.smul_single, smul_eq_mul, mul_one] using
    Matrix.matrix_eq_sum_single (sourcePopulationGramVersion kappa J G U anchor Y h)

/-- The version equals the actual Gram integral on its genuine domain. -/
theorem sourcePopulationGramVersion_eq_actual
    (kappa : Kernel S (EuclideanSpace Real (Fin d)))
    (J : EuclideanSpace Real (Fin d) -> H) (G : H -> Real) (U : Set H)
    (hU : IsOpen U) (hG : ContDiffOn Real 2 G U) (anchor : H)
    (Y : S -> Fin N -> EuclideanSpace Real (Fin d)) (h : S)
    (htheta : (∫ x, J x ∂kappa h) ∈ U)
    (hW : Integrable (fun x => finiteOperatorCovariance (fderiv Real J x)) (kappa h)) :
    sourcePopulationGramVersion kappa J G U anchor Y h = populationGramCovariance (kappa h)
      (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix J G
        (∫ x, J x ∂kappa h) (Y h i) z)) := by
  unfold sourcePopulationGramVersion
  rw [openMomentParameter_eq U anchor _ htheta]
  exact (source_actual_gram_eq_tensor J G _ (kappa h) (Y h)
    (hG.contDiffAt (hU.mem_nhds htheta)) hW).symm

section Source
variable {V : Nat -> Type*} [∀ n, NormedAddCommGroup (V n)]
  [∀ n, InnerProductSpace Real (V n)] [∀ n, CompleteSpace (V n)]

/-- The actual source moment is genuinely Bochner integrable before its
value is used as an objective parameter. No conditional uniform scale is needed. -/
theorem source_feature_integrable_of_source_class
    (c C g p q alpha K : Real) (phi : ∀ n, EuclideanSpace Real (Fin d) -> V n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K)
    (hphi : ∀ n, ContDiff Real 2 (phi n))
    (hgrowth : ∀ n z k, k ≤ 2 -> norm (iteratedFDeriv Real k (phi n) z) ≤
      featureGrowth C g q n * (1 + norm z ^ (n+1-k)))
    (mu : Measure (EuclideanSpace Real (Fin d))) (hmu : mu ∈ sourceMomentClass alpha K) :
    Integrable (sourceWeightedFeatureMap c p phi) mu := by
  letI : IsProbabilityMeasure mu := sourceMomentClass_isProbabilityMeasure alpha K mu hmu
  have hvalue : ∀ n z, norm (phi n z) ≤ featureGrowth C g q n * (1 + norm z ^ (n+1)) := by
    intro n z
    simpa only [norm_iteratedFDeriv_zero, Nat.sub_zero] using hgrowth n z 0 (by omega)
  exact (source_population_measure_moment_bounds mu c C g p q K alpha phi
    hc hC hp hq hK (fun n => (hphi n).continuous)
    (fun n => (sourceMomentClass_succ_moment alpha K hK mu hmu n).1)
    (fun n => (sourceMomentClass_succ_moment alpha K hK mu hmu n).2) hvalue).1

/-- Source features and an ∀ᵐ finite (not uniformly bounded) population scale
derive the actual covariance's ∀ᵐ measurability, integrability and positivity.
Finite scales can be supplied by source_ae_finite_scale_of_mixture_class. -/
theorem source_actual_gram_regular_of_finite_scales
    (c C g p q alpha : Real) (phi : ∀ n, EuclideanSpace Real (Fin d) -> V n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (halpha : 0 < alpha)
    (hphi : ∀ n, ContDiff Real 2 (phi n))
    (hgrowth : ∀ n z k, k ≤ 2 -> norm (iteratedFDeriv Real k (phi n) z) ≤
      featureGrowth C g q n * (1 + norm z ^ (n+1-k)))
    (G : lp V 2 -> Real) (U : Set (lp V 2)) (hU : IsOpen U)
    (hDomains : SourceAllMomentDomains (sourceWeightedFeatureMap c p phi) alpha U)
    (hG : ContDiffOn Real 2 G U) (rho : Measure S)
    (kappa : Kernel S (EuclideanSpace Real (Fin d))) [IsMarkovKernel kappa]
    (hfinite : ∀ᵐ h ∂rho, ∃ K : Real, 0 < K ∧ kappa h ∈ sourceMomentClass alpha K)
    (Y : S -> Fin N -> EuclideanSpace Real (Fin d)) (hY : ∀ i, Measurable (fun h => Y h i)) :
    let J := sourceWeightedFeatureMap c p phi
    let Cov := fun h => populationGramCovariance (kappa h)
      (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix J G
        (∫ x, J x ∂kappa h) (Y h i) z))
    AEMeasurable Cov rho ∧ ( ∀ᵐ h ∂rho,
      (∫ x, J x ∂kappa h) ∈ U ∧ (Cov h).PosSemidef ∧
      Integrable (fun z =>
        let A := stackedKernelMatrix (fun i => actualMomentKernelMatrix J G
          (∫ x, J x ∂kappa h) (Y h i) z)
        A * Aᵀ) (kappa h)) := by
  let J := sourceWeightedFeatureMap c p phi
  let Cov := fun h => populationGramCovariance (kappa h)
    (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix J G
      (∫ x, J x ∂kappa h) (Y h i) z))
  have hj := contDiff_sourceWeightedFeatureMap c C g p q phi hc hC hp hq hphi hgrowth
  have hanchor : J 0 ∈ U := hDomains 1 (by norm_num) 1 (by norm_num)
    (zero_anchor_mem_measureMomentRegion J _ 1 (by norm_num))
  have hm := sourcePopulationGramVersion_measurable kappa J hj.continuous
    (hj.continuous_fderiv (by norm_num)) G U hU hG (J 0) hanchor Y hY
  have hfacts : ∀ᵐ h ∂rho,
      sourcePopulationGramVersion kappa J G U (J 0) Y h = Cov h ∧
      (∫ x, J x ∂kappa h) ∈ U ∧ (Cov h).PosSemidef ∧
      Integrable (fun z =>
        let A := stackedKernelMatrix (fun i => actualMomentKernelMatrix J G
          (∫ x, J x ∂kappa h) (Y h i) z)
        A * Aᵀ) (kappa h) := by
    filter_upwards [hfinite] with h hh
    obtain ⟨K, hK, hk⟩ := hh
    have hJint := source_feature_integrable_of_source_class c C g p q alpha K phi
      hc hC hp hq hK hphi hgrowth (kappa h) hk
    have htheta : (∫ x, J x ∂kappa h) ∈ U :=
      hDomains K hK 1 (by norm_num) (population_integral_mem_measureMomentRegion J _ 1 _ hk)
    have hW := (sourceMomentClass_integrable_tensorCovariance_and_norm_sq c C g p q alpha K
      phi hc hC hp hq halpha hK hphi hgrowth (kappa h) hk).1
    have hGram := sourceMomentClass_integrable_actualMomentKernelMatrix_gram c C g p q alpha K
      phi hc hC hp hq halpha hK hphi hgrowth (kappa h) hk G (∫ x, J x ∂kappa h) (Y h)
    exact ⟨sourcePopulationGramVersion_eq_actual kappa J G U hU hG (J 0) Y h htheta hW,
      htheta, populationGramCovariance_posSemidef (kappa h) _ hGram, hGram⟩
  exact ⟨hm.aemeasurable.congr (hfacts.mono (fun _ h => h.1)),
    hfacts.mono (fun _ h => h.2)⟩
/-- One original-law AE set identifies the fixed covariance version used by
finite iteration, with actual integrability and positivity, before any clipping. -/
theorem source_actual_gram_version_ae
    (c C g p q alpha : Real) (phi : ∀ n, EuclideanSpace Real (Fin d) -> V n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (halpha : 0 < alpha)
    (hphi : ∀ n, ContDiff Real 2 (phi n))
    (hgrowth : ∀ n z k, k ≤ 2 -> norm (iteratedFDeriv Real k (phi n) z) ≤
      featureGrowth C g q n * (1 + norm z ^ (n+1-k)))
    (G : lp V 2 -> Real) (U : Set (lp V 2)) (hU : IsOpen U)
    (hDomains : SourceAllMomentDomains (sourceWeightedFeatureMap c p phi) alpha U)
    (hG : ContDiffOn Real 2 G U) (rho : Measure S)
    (kappa : Kernel S (EuclideanSpace Real (Fin d))) [IsMarkovKernel kappa]
    (hfinite : ∀ᵐ h ∂rho, ∃ K : Real, 0 < K ∧ kappa h ∈ sourceMomentClass alpha K)
    (Y : S -> Fin N -> EuclideanSpace Real (Fin d)) (hY : ∀ i, Measurable (fun h => Y h i)) :
    let J := sourceWeightedFeatureMap c p phi
    ∀ᵐ h ∂ rho, Integrable J (kappa h) ∧
      sourcePopulationGramVersion kappa J G U (J 0) Y h =
        populationGramCovariance (kappa h)
          (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix J G
            (∫ x, J x ∂ kappa h) (Y h i) z)) ∧
      (populationGramCovariance (kappa h)
        (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix J G
          (∫ x, J x ∂ kappa h) (Y h i) z))).PosSemidef := by
  let J := sourceWeightedFeatureMap c p phi
  have hr := source_actual_gram_regular_of_finite_scales c C g p q alpha phi hc hC hp hq
    halpha hphi hgrowth G U hU hDomains hG rho kappa hfinite Y hY
  filter_upwards [hfinite,hr.2] with h hh hreg
  obtain ⟨K,hK,hk⟩ := hh
  have hJint := source_feature_integrable_of_source_class c C g p q alpha K phi
    hc hC hp hq hK hphi hgrowth (kappa h) hk
  have hW := (sourceMomentClass_integrable_tensorCovariance_and_norm_sq c C g p q alpha K
    phi hc hC hp hq halpha hK hphi hgrowth (kappa h) hk).1
  exact ⟨hJint, sourcePopulationGramVersion_eq_actual kappa J G U hU hG (J 0) Y h
    hreg.1 hW, hreg.2.1⟩

end Source
end PaperFormalization.Manuscript
