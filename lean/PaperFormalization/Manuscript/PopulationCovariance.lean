import PaperFormalization.Manuscript.CovarianceMismatch
import PaperFormalization.Manuscript.EmpiricalMeasureMoment
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Genuine population covariance integrals and empirical residuals

This is a generic Bochner covariance adapter. Integrability of the actual Gram
matrix is an explicit premise, not claimed from the source feature conditions
here. The population law is unrestricted by localization. The signed residual
is the difference of two actual integrals, never truncated measure subtraction.
-/

open Matrix MeasureTheory
open scoped MatrixOrder Matrix.Norms.Frobenius BigOperators

namespace PaperFormalization.Manuscript

variable {n k : Type*} [Fintype n] [Fintype k]

-- Matrix's abbreviation requires making this inherited Frobenius instance
-- explicit for the current extended-norm Bochner API.
noncomputable local instance : ContinuousENorm (Matrix n k ℝ) :=
  SeminormedAddGroup.toContinuousENorm

/-- Continuous evaluation of a finite matrix entry in its actual normed space. -/
noncomputable def matrixEntryFunctional (i : n) (j : k) : Matrix n k ℝ →L[ℝ] ℝ :=
  ({ toFun := fun A => A i j
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Matrix n k ℝ →ₗ[ℝ] ℝ).toContinuousLinearMap

@[simp] theorem matrixEntryFunctional_apply (i : n) (j : k) (A : Matrix n k ℝ) :
    matrixEntryFunctional i j A = A i j := rfl

/-- A fixed quadratic form is linear and continuous in the matrix argument. -/
noncomputable def matrixQuadraticFunctional (x : n → ℝ) : Matrix n n ℝ →L[ℝ] ℝ :=
  ∑ i, ∑ j, (x i * x j) • matrixEntryFunctional i j

/-- The linear functional is exactly the Euclidean quadratic form. -/
theorem matrixQuadraticFunctional_apply (x : n → ℝ) (A : Matrix n n ℝ) :
    matrixQuadraticFunctional x A = x ⬝ᵥ (A *ᵥ x) := by
  simp only [matrixQuadraticFunctional, _root_.sum_apply,
    _root_.smul_apply, matrixEntryFunctional_apply, smul_eq_mul,
    dotProduct, mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

variable {E : Type*} [MeasurableSpace E]

/-- Genuine matrix integrability permits entrywise evaluation of the integral. -/
theorem matrix_integral_entry (μ : Measure E) (F : E → Matrix n k ℝ)
    (hF : Integrable F μ) (i : n) (j : k) :
    (∫ z, F z ∂μ) i j = ∫ z, F z i j ∂μ :=
  ((matrixEntryFunctional i j).integral_comp_comm hF).symm

/-- The Bochner integral of genuinely integrable, almost-everywhere PSD
matrices is PSD. Positivity is checked through actual finite quadratic forms. -/
theorem matrix_integral_posSemidef (μ : Measure E) (F : E → Matrix n n ℝ)
    (hF : Integrable F μ) (hPSD : ∀ᵐ z ∂μ, (F z).PosSemidef) :
    (∫ z, F z ∂μ).PosSemidef := by
  have hsym : (∫ z, F z ∂μ).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial]
    rw [matrix_integral_entry μ F hF, matrix_integral_entry μ F hF]
    apply integral_congr_ae
    filter_upwards [hPSD] with z hz
    simpa only [star_trivial] using hz.isHermitian.apply i j
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hsym
  intro x
  simp only [star_trivial]
  have hint : (∫ z, matrixQuadraticFunctional x (F z) ∂μ) =
      matrixQuadraticFunctional x (∫ z, F z ∂μ) :=
    (matrixQuadraticFunctional x).integral_comp_comm hF
  have hnonneg : 0 ≤ ∫ z, matrixQuadraticFunctional x (F z) ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hPSD] with z hz
    simpa only [matrixQuadraticFunctional_apply, star_trivial, Pi.zero_apply] using hz.dotProduct_mulVec_nonneg x
  simpa only [matrixQuadraticFunctional_apply] using hnonneg.trans_eq hint

/-- Actual population covariance built from the rectangular factor U(z). -/
noncomputable def populationGramCovariance (μ : Measure E) (U : E → Matrix n k ℝ) :
    Matrix n n ℝ := ∫ z, U z * (U z)ᵀ ∂μ

/-- Population covariance is PSD once its genuine Gram integrability is supplied. -/
theorem populationGramCovariance_posSemidef (μ : Measure E) (U : E → Matrix n k ℝ)
    (hU : Integrable (fun z => U z * (U z)ᵀ) μ) :
    (populationGramCovariance μ U).PosSemidef := by
  apply matrix_integral_posSemidef μ _ hU
  filter_upwards [] with z
  simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose (U z)

/-- Exact population entry: the integral of the finite row-inner-product sum. -/
theorem populationGramCovariance_entry (μ : Measure E) (U : E → Matrix n k ℝ)
    (hU : Integrable (fun z => U z * (U z)ᵀ) μ) (i j : n) :
    populationGramCovariance μ U i j = ∫ z, ∑ a, U z i a * U z j a ∂μ := by
  rw [populationGramCovariance, matrix_integral_entry μ _ hU]
  rfl

/-- Under the actual finite empirical measure, the covariance integral is
exactly the previously checked reciprocal-count Gram average. -/
theorem populationGramCovariance_empirical [MeasurableSingletonClass E]
    {N : ℕ} (Y : Fin N → E) (U : E → Matrix n k ℝ) :
    populationGramCovariance (finiteEmpiricalMeasure Y) U =
      empiricalGramMatrix (fun j => U (Y j)) := by
  rw [populationGramCovariance, integral_finiteEmpiricalMeasure]
  simp only [finiteFeatureMean, Fintype.card_fin, empiricalGramMatrix]

/-- The actual covariance fluctuation residual, interpreted as a difference
of two integrals under the same fixed population law and empirical cloud. -/
noncomputable def populationCovarianceResidual {N : ℕ}
    (μ : Measure E) (Y : Fin N → E) (U : E → Matrix n k ℝ) : Matrix n n ℝ :=
  populationGramCovariance μ U - populationGramCovariance (finiteEmpiricalMeasure Y) U

/-- Exact empirical-sum form of the population residual; no localization of
population integration points is used. -/
theorem populationCovarianceResidual_eq_empirical [MeasurableSingletonClass E]
    {N : ℕ} (μ : Measure E) (Y : Fin N → E) (U : E → Matrix n k ℝ) :
    populationCovarianceResidual μ Y U =
      populationGramCovariance μ U - empiricalGramMatrix (fun j => U (Y j)) := by
  rw [populationCovarianceResidual, populationGramCovariance_empirical]

/-- The residual is genuinely symmetric, for the actual unbounded population
integral and exact finite empirical average. -/
theorem populationCovarianceResidual_isHermitian [MeasurableSingletonClass E]
    {N : ℕ} (μ : Measure E) (Y : Fin N → E) (U : E → Matrix n k ℝ)
    (hU : Integrable (fun z => U z * (U z)ᵀ) μ) :
    (populationCovarianceResidual μ Y U).IsHermitian := by
  rw [populationCovarianceResidual_eq_empirical]
  exact (populationGramCovariance_posSemidef μ U hU).isHermitian.sub
    (empiricalGramMatrix_isHermitian _)

/-- The empirical Gram integrand is genuinely integrable on finite support,
including the empty empirical measure. No population support claim is made. -/
theorem integrable_gram_finiteEmpiricalMeasure [MeasurableSingletonClass E]
    {N : ℕ} (Y : Fin N → E) (U : E → Matrix n k ℝ) :
    Integrable (fun z => U z * (U z)ᵀ) (finiteEmpiricalMeasure Y) := by
  cases N with
  | zero => simp [finiteEmpiricalMeasure]
  | succ N => exact integrable_finiteEmpiricalMeasure Y _

/-- Each actual population covariance block is the integral of its two
kernel factors, with transpose and multiplication order preserved. -/
theorem populationGramCovariance_stacked_entry {N d : ℕ}
    (μ : Measure E) (H : Fin N → E → Matrix (Fin d) (Fin d) ℝ)
    (hH : Integrable (fun z => stackedKernelMatrix (fun i => H i z) *
      (stackedKernelMatrix (fun i => H i z))ᵀ) μ)
    (i j : Fin N) (a b : Fin d) :
    populationGramCovariance μ (fun z => stackedKernelMatrix (fun i => H i z)) (i, a) (j, b) =
      ∫ z, (H i z * (H j z)ᵀ) a b ∂μ := by
  rw [populationGramCovariance_entry μ _ hH]
  rfl

/-- Source-shaped mismatch with an actual unbounded population Bochner
covariance and the literal two-integral residual. This remains conditional on
genuine population Gram integrability and the sample-local block bounds. -/
theorem population_covariance_mismatch_normalized_le [MeasurableSingletonClass E]
    {N d : ℕ} (μ : Measure E) (Y : Fin N → E)
    (H : Fin N → E → Matrix (Fin d) (Fin d) ℝ)
    (G : Fin N → Fin N → Matrix (Fin d) (Fin d) ℝ) (L gamma : ℝ)
    (hN : 0 < N) (hL : 0 ≤ L) (hgamma : 0 ≤ gamma)
    (hGram : Integrable (fun z => stackedKernelMatrix (fun i => H i z) *
      (stackedKernelMatrix (fun i => H i z))ᵀ) μ)
    (hH : ∀ i j, ‖matrixEuclideanOperator (H i (Y j))‖ ≤ L)
    (hG : ∀ i j, ‖matrixEuclideanOperator (G i j)‖ ≤ L)
    (hHG : ∀ i j, ‖matrixEuclideanOperator (H i (Y j) - G i j)‖ ≤ gamma)
    (hGsym : ∀ i j, (G i j)ᵀ = G j i) :
    matrixNuclearValue (populationGramCovariance μ (fun z => stackedKernelMatrix (fun i => H i z)) -
      empiricalKernelFactor G * empiricalKernelFactor G) / N ≤
      2 * d * L * gamma +
        matrixNuclearValue (populationCovarianceResidual μ Y
          (fun z => stackedKernelMatrix (fun i => H i z))) / N := by
  rw [populationCovarianceResidual_eq_empirical]
  exact source_covariance_mismatch_factor_square_le _
    (populationGramCovariance_posSemidef μ _ hGram).isHermitian
    (fun i j => H i (Y j)) G L gamma hN hL hgamma hH hG hHG hGsym

end PaperFormalization.Manuscript
