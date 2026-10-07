import PaperFormalization.Manuscript.ActualNuclearResidualMeasurability
import Mathlib.Probability.Kernel.MeasurableIntegral

/-! # A measurable version of the actual history-dependent nuclear residual

The original objective is smooth only on its original open set U. The moment
parameter uses a fixed anchor in U outside that domain, solely to define a
measurable version on ineligible histories. Whenever the genuine population
moment lies in U and its tensor covariance is integrable, this version equals
the literal original kernel covariance residual. No target separability or
global extension of the objective's smoothness is assumed.
-/

open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius

namespace PaperFormalization.Manuscript

variable {H S Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace S] [MeasurableSpace Ω] {N d : ℕ}

noncomputable local instance instMeasurableSpaceKernelNuclearHilbert : MeasurableSpace H := borel _
noncomputable local instance instBorelSpaceKernelNuclearHilbert : BorelSpace H := ⟨rfl⟩
local instance instMeasurableSpaceKernelNuclearMatrix :
    MeasurableSpace (Matrix (Fin N × Fin d) (Fin N × Fin d) ℝ) := borel _
local instance instBorelSpaceKernelNuclearMatrix :
    BorelSpace (Matrix (Fin N × Fin d) (Fin N × Fin d) ℝ) := ⟨rfl⟩
noncomputable local instance instContinuousENormKernelNuclearMatrix :
    ContinuousENorm (Matrix (Fin N × Fin d) (Fin N × Fin d) ℝ) :=
  SeminormedAddGroup.toContinuousENorm

/-- Retain the actual parameter on U, and use a fixed valid anchor elsewhere. -/
noncomputable def openMomentParameter (U : Set H) (anchor theta : H) : H := by
  classical
  exact if theta ∈ U then theta else anchor

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- The fallback never changes a parameter already in the original domain. -/
theorem openMomentParameter_eq (U : Set H) (anchor theta : H) (htheta : theta ∈ U) :
    openMomentParameter U anchor theta = theta := by
  classical
  simp only [openMomentParameter, if_pos htheta]

/-- Local C2 on the original open domain makes the actual Riesz Hessian
continuous on that domain, with no global smoothness premise. -/
theorem continuousOn_momentObjectiveHessian (G : H → ℝ) (U : Set H)
    (hU : IsOpen U) (hG : ContDiffOn ℝ 2 G U) :
    ContinuousOn (momentObjectiveHessian G) U := by
  have hd : ContDiffOn ℝ 1 (fderiv ℝ G) U := hG.fderiv_of_isOpen hU (by norm_num)
  exact continuous_const.continuousOn.clm_comp (hd.continuousOn_fderiv_of_isOpen hU (by norm_num))

/-- The local Hessian along a strongly measurable actual parameter has a
strongly measurable version using the anchor only outside its open domain. -/
theorem stronglyMeasurable_openMomentHessian (G : H → ℝ) (U : Set H)
    (hU : IsOpen U) (hG : ContDiffOn ℝ 2 G U) (anchor : H) (hanchor : anchor ∈ U)
    (theta : S → H) (htheta : StronglyMeasurable theta) :
    StronglyMeasurable (fun h => momentObjectiveHessian G (openMomentParameter U anchor (theta h))) := by
  classical
  let psi : S → U := fun h => ⟨openMomentParameter U anchor (theta h), by
    by_cases hh : theta h ∈ U
    · simpa only [openMomentParameter_eq U anchor (theta h) hh] using hh
    · simpa only [openMomentParameter, if_neg hh] using hanchor⟩
  have hs : StronglyMeasurable (fun h => (psi h : H)) :=
    htheta.piecewise (hU.measurableSet.preimage htheta.measurable) stronglyMeasurable_const
  have hpsi : StronglyMeasurable psi :=
    (Embedding.comp_stronglyMeasurable_iff Topology.IsEmbedding.subtypeVal).mp hs
  exact (continuousOn_iff_continuous_restrict.mp
    (continuousOn_momentObjectiveHessian G U hU hG)).comp_stronglyMeasurable hpsi

/-- An actual tensor-compression version with the original population kernel
means. This is a version outside the local domain, not a new population law. -/
noncomputable def kernelNuclearResidualVersion
    (κ : Kernel S (EuclideanSpace ℝ (Fin d)))
    (X : S × Ω → Fin N → EuclideanSpace ℝ (Fin d))
    (J : EuclideanSpace ℝ (Fin d) → H) (G : H → ℝ) (U : Set H) (anchor : H)
    (z : S × Ω) : ℝ :=
  let theta := openMomentParameter U anchor (∫ x, J x ∂κ z.1)
  let rows := actualMomentTensorColumns J G theta (X z)
  let tensor := (∫ x, finiteOperatorCovariance (fderiv ℝ J x) ∂κ z.1) -
    (N : ℝ)⁻¹ • ∑ i, finiteOperatorCovariance (fderiv ℝ J (X z i))
  matrixNuclearValue (hilbertTensorCompression rows tensor) / N

set_option maxHeartbeats 1000000 in
/-- The version is jointly measurable for genuinely measurable samples and an
actual population kernel. Strong measurability handles the nonseparable
Hilbert/tensor targets before taking finite scalar matrix entries. -/
theorem measurable_kernelNuclearResidualVersion
    (κ : Kernel S (EuclideanSpace ℝ (Fin d)))
    (X : S × Ω → Fin N → EuclideanSpace ℝ (Fin d))
    (hX : ∀ i, Measurable (fun z => X z i))
    (J : EuclideanSpace ℝ (Fin d) → H) (hJ : Continuous J)
    (hDJ : Continuous (fderiv ℝ J)) (G : H → ℝ) (U : Set H)
    (hU : IsOpen U) (hG : ContDiffOn ℝ 2 G U) (anchor : H) (hanchor : anchor ∈ U) :
    Measurable (kernelNuclearResidualVersion κ X J G U anchor) := by
  have htheta : StronglyMeasurable (fun h : S => ∫ x, J x ∂κ h) :=
    hJ.stronglyMeasurable.integral_kernel
  have hHess := (stronglyMeasurable_openMomentHessian G U hU hG anchor hanchor _ htheta).comp_measurable
    (measurable_fst : Measurable (Prod.fst : S × Ω → S))
  have hcol (i : Fin N × Fin d) : StronglyMeasurable (fun z : S × Ω =>
      actualFeatureDerivativeColumns J (X z i.1) i.2) := by
    exact (hDJ.clm_apply continuous_const).comp_stronglyMeasurable (hX i.1).stronglyMeasurable
  have hrow (i : Fin N × Fin d) : StronglyMeasurable (fun z : S × Ω =>
      actualMomentTensorColumns J G (openMomentParameter U anchor (∫ x, J x ∂κ z.1)) (X z) i) := by
    exact (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable (hHess.prodMk (hcol i))
  have hW : Continuous (fun x => finiteOperatorCovariance (fderiv ℝ J x)) :=
    continuous_finiteOperatorCovariance.comp hDJ
  have hpop : StronglyMeasurable (fun z : S × Ω =>
      ∫ x, finiteOperatorCovariance (fderiv ℝ J x) ∂κ z.1) :=
    hW.stronglyMeasurable.integral_kernel.comp_measurable measurable_fst
  have hemp : StronglyMeasurable (fun z : S × Ω =>
      (N : ℝ)⁻¹ • ∑ i, finiteOperatorCovariance (fderiv ℝ J (X z i))) :=
    (Finset.stronglyMeasurable_fun_sum Finset.univ (fun i _ =>
      hW.comp_stronglyMeasurable (hX i).stronglyMeasurable)).const_smul ((N : ℝ)⁻¹)
  let M := fun z : S × Ω => hilbertTensorCompression
    (actualMomentTensorColumns J G (openMomentParameter U anchor (∫ x, J x ∂κ z.1)) (X z))
    ((∫ x, finiteOperatorCovariance (fderiv ℝ J x) ∂κ z.1) -
      (N : ℝ)⁻¹ • ∑ i, finiteOperatorCovariance (fderiv ℝ J (X z i)))
  have hentry (i j : Fin N × Fin d) : StronglyMeasurable (fun z => M z i j) := by
    have hpure := ((hilbertPureTensor.continuous.comp continuous_fst).clm_apply continuous_snd).comp_stronglyMeasurable
      ((hrow i).prodMk (hrow j))
    exact (continuous_fst.inner continuous_snd).comp_stronglyMeasurable (hpure.prodMk (hpop.sub hemp))
  let assemble : ((Fin N × Fin d) → (Fin N × Fin d) → ℝ) →
      Matrix (Fin N × Fin d) (Fin N × Fin d) ℝ :=
    fun v => ∑ i, ∑ j, v i j • Matrix.single i j (1 : ℝ)
  have ha : Continuous assemble := by
    unfold assemble
    fun_prop
  have he : Measurable (fun z i j => M z i j) := measurable_pi_lambda _ (fun i =>
    measurable_pi_lambda _ (fun j => (hentry i j).measurable))
  have hmat : Measurable M := by
    convert ha.measurable.comp he using 1
    funext z
    simpa only [Function.comp_def, assemble, Matrix.smul_single, smul_eq_mul, mul_one] using
      Matrix.matrix_eq_sum_single (M z)
  exact (measurable_matrixNuclearValue M hmat).div_const _

omit [MeasurableSpace Ω] in
/-- On every eligible population parameter, the measurable version equals the
literal actual nuclear residual under the same kernel measure. -/
theorem kernelNuclearResidualVersion_eq_actual
    (κ : Kernel S (EuclideanSpace ℝ (Fin d)))
    (X : S × Ω → Fin N → EuclideanSpace ℝ (Fin d))
    (J : EuclideanSpace ℝ (Fin d) → H) (G : H → ℝ) (U : Set H)
    (hU : IsOpen U) (hG : ContDiffOn ℝ 2 G U) (anchor : H) (z : S × Ω)
    (htheta : (∫ x, J x ∂κ z.1) ∈ U)
    (hW : Integrable (fun x => finiteOperatorCovariance (fderiv ℝ J x)) (κ z.1)) :
    kernelNuclearResidualVersion κ X J G U anchor z =
      matrixNuclearValue (populationCovarianceResidual (κ z.1) (X z)
        (fun x => stackedKernelMatrix (fun i =>
          actualMomentKernelMatrix J G (∫ y, J y ∂κ z.1) (X z i) x))) / N := by
  rw [actual_populationCovarianceResidual_eq_tensor_compression J G _ _ _
    (hG.contDiffAt (hU.mem_nhds htheta)) hW,
    integral_finiteEmpiricalMeasure]
  simp only [kernelNuclearResidualVersion, openMomentParameter_eq U anchor _ htheta,
    finiteFeatureMean, Fintype.card_fin]

end PaperFormalization.Manuscript
