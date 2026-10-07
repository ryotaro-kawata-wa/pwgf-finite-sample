import PaperFormalization.Manuscript.HilbertTensorCovariance
import PaperFormalization.Manuscript.OrthogonalHilbertColumns
import PaperFormalization.Manuscript.PopulationCovariance

/-! # Actual finite matrix compression of Hilbert covariance tensors

The compression tests a tensor against v_i ⊗ v_j. It is an actual continuous
linear map, so it commutes with genuine Bochner integrals and finite empirical
means. Its symmetric nuclear bound uses the constructed spectral sign and exact
orthogonal Hilbert-column energy preservation, with no dimension loss.
-/

open Matrix MeasureTheory
open scoped BigOperators InnerProductSpace Matrix.Norms.Frobenius

namespace PaperFormalization.Manuscript

variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

noncomputable local instance instContinuousENormTensorCompressionMatrix :
    ContinuousENorm (Matrix ι ι ℝ) := SeminormedAddGroup.toContinuousENorm

/-- Testing an actual Hilbert tensor against a finite family of pure tensors. -/
noncomputable def hilbertTensorCompression (v : ι → H) :
    realHilbertTensor H →L[ℝ] Matrix ι ι ℝ where
  toFun S i j := inner ℝ (hilbertPureTensor (v i) (v j)) S
  map_add' S T := by ext i j; exact inner_add_right _ _ _
  map_smul' a S := by
    ext i j
    change inner ℝ (hilbertPureTensor (v i) (v j)) (a • S) =
      a * inner ℝ (hilbertPureTensor (v i) (v j)) S
    exact real_inner_smul_right _ _ _
  cont := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact continuous_const.inner continuous_id

omit [Fintype ι] [DecidableEq ι] in
/-- Compression uses the literal tested entries. -/
@[simp] theorem hilbertTensorCompression_apply (v : ι → H) (S : realHilbertTensor H) (i j : ι) :
    hilbertTensorCompression v S i j = inner ℝ (hilbertPureTensor (v i) (v j)) S := rfl

omit [Fintype ι] [DecidableEq ι] in
/-- A compressed pure tensor is the exact rank-one entry product. -/
theorem hilbertTensorCompression_pureTensor (v : ι → H) (x y : H) (i j : ι) :
    hilbertTensorCompression v (hilbertPureTensor x y) i j =
      inner ℝ (v i) x * inner ℝ (v j) y := inner_hilbertPureTensor _ _ _ _

omit [Fintype ι] [DecidableEq ι] in
/-- The compression of a finite column covariance is its actual Gram matrix. -/
theorem hilbertTensorCompression_finiteColumnCovariance {κ : Type*} [Fintype κ]
    (v : ι → H) (w : κ → H) :
    hilbertTensorCompression v (finiteColumnCovariance w) =
      (Matrix.of (fun (i : ι) (j : κ) => inner ℝ (v i) (w j))) * (fun i j => inner ℝ (v i) (w j))ᵀ := by
  ext i j
  simp only [hilbertTensorCompression_apply, inner_finiteColumnCovariance,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]

omit [DecidableEq ι] in
/-- Genuine tensor integrability implies genuine matrix integrability. -/
theorem integrable_hilbertTensorCompression {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (v : ι → H) (S : Ω → realHilbertTensor H) (hS : Integrable S μ) :
    Integrable (fun z => hilbertTensorCompression v (S z)) μ :=
  (hilbertTensorCompression v).integrable_comp hS

/-- Bochner compression commutes with the original, unchanged measure. -/
theorem hilbertTensorCompression_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (v : ι → H) (S : Ω → realHilbertTensor H) (hS : Integrable S μ) :
    hilbertTensorCompression v (∫ z, S z ∂μ) = ∫ z, hilbertTensorCompression v (S z) ∂μ :=
  ((hilbertTensorCompression v).integral_comp_comm hS).symm

omit [Fintype ι] [DecidableEq ι] in
/-- The literal finite empirical covariance mean has the same compression. -/
theorem hilbertTensorCompression_empirical {N : ℕ} (v : ι → H)
    (S : Fin N → realHilbertTensor H) :
    hilbertTensorCompression v ((N : ℝ)⁻¹ • ∑ j, S j) =
      (N : ℝ)⁻¹ • ∑ j, hilbertTensorCompression v (S j) := by
  simp only [map_smul, map_sum]

/-- Orthogonal column mixing bounds the actual finite tensor test vector
by the original squared column norms, including an empty family. -/
theorem norm_sum_hilbertPureTensor_orthogonal_le (Q : Matrix ι ι ℝ)
    (hQ : Q * Q.transpose = 1) (v : ι → H) :
    ‖∑ i, hilbertPureTensor (v i) (orthogonalHilbertColumns Q v i)‖ ≤ ∑ i, ‖v i‖ ^ 2 := by
  exact (norm_sum_le _ _).trans ((by
    simpa only [norm_hilbertPureTensor] using orthogonalHilbertColumns_sum_norm_mul_le Q hQ v))

omit [DecidableEq ι] in
/-- The trace pairing is the actual tensor inner product, with the correct
right-mixing orientation. No symmetry of Q or S is used in this identity. -/
theorem trace_mul_hilbertTensorCompression (Q : Matrix ι ι ℝ) (v : ι → H)
    (S : realHilbertTensor H) :
    Matrix.trace (Q * hilbertTensorCompression v S) =
      inner ℝ (∑ i, hilbertPureTensor (v i) (orthogonalHilbertColumns Q v i)) S := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hilbertTensorCompression_apply,
    orthogonalHilbertColumns, map_sum, map_smul, sum_inner, real_inner_smul_left]
  exact Finset.sum_comm

/-- Actual symmetric nuclear compression has the exact source coefficient.
Symmetry is the structural condition on this arbitrary tested tensor, not a
norm or concentration premise. -/
theorem matrixNuclearValue_hilbertTensorCompression_le (v : ι → H)
    (S : realHilbertTensor H) (hS : (hilbertTensorCompression v S).IsHermitian) :
    matrixNuclearValue (hilbertTensorCompression v S) ≤ (∑ i, ‖v i‖ ^ 2) * ‖S‖ := by
  rw [matrixNuclearValue_eq_trace_alignedSignMatrix hS, trace_mul_hilbertTensorCompression]
  exact (real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right
      (norm_sum_hilbertPureTensor_orthogonal_le _ (alignedSignMatrix_orthogonal hS).1 v)
      (norm_nonneg S))

/-- The full tensor population-minus-empirical difference is exactly the
existing matrix covariance residual, under the unchanged population measure. -/
theorem hilbertTensorCompression_populationCovarianceResidual
    {Ω κ : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype κ]
    {N : ℕ} (μ : Measure Ω) (Y : Fin N → Ω) (v : ι → H) (w : Ω → κ → H)
    (hw : Integrable (fun z => finiteColumnCovariance (w z)) μ) :
    hilbertTensorCompression v
      ((∫ z, finiteColumnCovariance (w z) ∂μ) -
        ∫ z, finiteColumnCovariance (w z) ∂finiteEmpiricalMeasure Y) =
      populationCovarianceResidual μ Y (fun z i j => inner ℝ (v i) (w z j)) := by
  rw [map_sub, hilbertTensorCompression_integral μ v _ hw,
    integral_finiteEmpiricalMeasure, populationCovarianceResidual_eq_empirical]
  simp only [finiteFeatureMean, Fintype.card_fin, map_smul, map_sum,
    hilbertTensorCompression_finiteColumnCovariance, populationGramCovariance, empiricalGramMatrix]
  rfl

/-- The concrete covariance residual has the exact dimension-free nuclear
reduction; matrix symmetry and matrix Gram integrability are both derived. -/
theorem populationCovarianceResidual_nuclear_le_tensor
    {Ω κ : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype κ]
    {N : ℕ} (μ : Measure Ω) (Y : Fin N → Ω) (v : ι → H) (w : Ω → κ → H)
    (hw : Integrable (fun z => finiteColumnCovariance (w z)) μ) :
    matrixNuclearValue
      (populationCovarianceResidual μ Y (fun z i j => inner ℝ (v i) (w z j))) ≤
      (∑ i, ‖v i‖ ^ 2) *
        ‖(∫ z, finiteColumnCovariance (w z) ∂μ) -
          ∫ z, finiteColumnCovariance (w z) ∂finiteEmpiricalMeasure Y‖ := by
  have hGram : Integrable (fun z =>
      (Matrix.of (fun (i : ι) (j : κ) => inner ℝ (v i) (w z j))) * (fun i j => inner ℝ (v i) (w z j))ᵀ) μ := by
    simpa only [hilbertTensorCompression_finiteColumnCovariance] using
      integrable_hilbertTensorCompression μ v (fun z => finiteColumnCovariance (w z)) hw
  rw [← hilbertTensorCompression_populationCovarianceResidual μ Y v w hw]
  apply matrixNuclearValue_hilbertTensorCompression_le
  rw [hilbertTensorCompression_populationCovarianceResidual μ Y v w hw]
  exact populationCovarianceResidual_isHermitian μ Y _ hGram

end PaperFormalization.Manuscript
