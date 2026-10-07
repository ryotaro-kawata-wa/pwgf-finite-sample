import PaperFormalization.Manuscript.SourceTensorCovarianceResidual
import PaperFormalization.Manuscript.MeasurableAlignedFactors

/-! # Measurability of the literal nuclear covariance residual

Continuity of the actual matrix residual follows from its proved tensor
compression identity. Thus no unjustified interchange of sample-parameter
limits with the unbounded population integral is needed. Nuclear-value
measurability uses the actual positive square root of XᵀX.
-/

open Matrix MeasureTheory
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

namespace PaperFormalization.Manuscript

local instance instMeasurableSpaceActualNuclearMatrix {n : Type*} [Fintype n] : MeasurableSpace (Matrix n n ℝ) := borel _
local instance instBorelSpaceActualNuclearMatrix {n : Type*} [Fintype n] : BorelSpace (Matrix n n ℝ) := ⟨rfl⟩

section Nuclear
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual nuclear value is nonnegative for every finite real matrix. -/
theorem matrixNuclearValue_nonneg (M : Matrix n n ℝ) : 0 ≤ matrixNuclearValue M := by
  exact (CFC.sqrt_nonneg (M.transpose * M)).posSemidef.trace_nonneg

/-- Borel nuclear values follow from PSD square roots, including singular
matrices; no choice of measurable eigenvectors or nuclear Norm is assumed. -/
theorem measurable_matrixNuclearValue {Ω : Type*} [MeasurableSpace Ω]
    (M : Ω → Matrix n n ℝ) (hM : Measurable M) :
    Measurable (fun x => matrixNuclearValue (M x)) := by
  have hgram : Continuous (fun X : Matrix n n ℝ => X.transpose * X) :=
    continuous_id.matrix_transpose.matrix_mul continuous_id
  have hs := measurable_psd_sqrt (fun x => (M x).transpose * M x) (hgram.measurable.comp hM)
    (fun x => by simpa only [conjTranspose_eq_transpose_of_trivial] using
      posSemidef_conjTranspose_mul_self (M x))
  exact (continuous_id.matrix_trace : Continuous (fun X : Matrix n n ℝ => Matrix.trace X)).measurable.comp hs

end Nuclear

section Residual

variable {N d : ℕ} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

noncomputable local instance instContinuousENormActualNuclearMatrix : ContinuousENorm (Matrix (Fin N × Fin d) (Fin N × Fin d) ℝ) :=
  SeminormedAddGroup.toContinuousENorm

set_option maxHeartbeats 800000 in
/-- Actual population covariance residuals vary continuously with the finite
sample cloud, by their exact tensor identity and genuine tensor integrability. -/
theorem continuous_actual_populationCovarianceResidual
    (J : EuclideanSpace ℝ (Fin d) → H) (G : H → ℝ) (theta : H)
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (hJ : Continuous (fderiv ℝ J)) (hG : ContDiffAt ℝ 2 G theta)
    (hW : Integrable (fun z => finiteOperatorCovariance (fderiv ℝ J z)) μ) :
    Continuous (fun Y : Fin N → EuclideanSpace ℝ (Fin d) => populationCovarianceResidual μ Y
      (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix J G theta (Y i) z))) := by
  have heq : (fun Y : Fin N → EuclideanSpace ℝ (Fin d) => populationCovarianceResidual μ Y
      (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix J G theta (Y i) z))) =
      fun Y => hilbertTensorCompression (actualMomentTensorColumns J G theta Y)
        ((∫ z, finiteOperatorCovariance (fderiv ℝ J z) ∂μ) -
          (N : ℝ)⁻¹ • ∑ j, finiteOperatorCovariance (fderiv ℝ J (Y j))) := by
    funext Y
    rw [actual_populationCovarianceResidual_eq_tensor_compression J G theta μ Y hG hW,
      integral_finiteEmpiricalMeasure]
    simp only [finiteFeatureMean, Fintype.card_fin]
  rw [heq]
  have hv (i : Fin N × Fin d) : Continuous (fun Y : Fin N → EuclideanSpace ℝ (Fin d) =>
      actualMomentTensorColumns J G theta Y i) := by
    exact (momentObjectiveHessian G theta).continuous.comp
      ((hJ.comp (continuous_apply i.1)).clm_apply continuous_const)
  have hS : Continuous (fun Y : Fin N → EuclideanSpace ℝ (Fin d) =>
      (∫ z, finiteOperatorCovariance (fderiv ℝ J z) ∂μ) -
        (N : ℝ)⁻¹ • ∑ j, finiteOperatorCovariance (fderiv ℝ J (Y j))) := by
    exact continuous_const.sub
      ((continuous_finsetSum Finset.univ (fun j _ =>
        continuous_finiteOperatorCovariance.comp (hJ.comp (continuous_apply j)))).const_smul ((N : ℝ)⁻¹))
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun Y => inner ℝ
    (hilbertPureTensor (actualMomentTensorColumns J G theta Y i)
      (actualMomentTensorColumns J G theta Y j)) _)
  exact ((hilbertPureTensor.continuous.comp (hv i)).clm_apply (hv j)).inner hS

/-- The literal normalized covariance residual is measurable and nonnegative.
No residual-measurability premise is left to a probabilistic application. -/
theorem measurable_nonneg_actual_nuclear_populationCovarianceResidual
    (J : EuclideanSpace ℝ (Fin d) → H) (G : H → ℝ) (theta : H)
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (hJ : Continuous (fderiv ℝ J)) (hG : ContDiffAt ℝ 2 G theta)
    (hW : Integrable (fun z => finiteOperatorCovariance (fderiv ℝ J z)) μ) :
    Measurable (fun Y : Fin N → EuclideanSpace ℝ (Fin d) =>
      matrixNuclearValue (populationCovarianceResidual μ Y
        (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix J G theta (Y i) z))) / N) ∧
    ∀ Y : Fin N → EuclideanSpace ℝ (Fin d), 0 ≤
      matrixNuclearValue (populationCovarianceResidual μ Y
        (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix J G theta (Y i) z))) / N := by
  refine ⟨(measurable_matrixNuclearValue (n := Fin N × Fin d) _
    (continuous_actual_populationCovarianceResidual (N := N) J G theta μ hJ hG hW).measurable).div_const _, ?_⟩
  intro Y
  exact div_nonneg (matrixNuclearValue_nonneg _) (Nat.cast_nonneg N)

end Residual

end PaperFormalization.Manuscript
