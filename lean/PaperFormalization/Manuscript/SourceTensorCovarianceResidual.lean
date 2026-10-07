import PaperFormalization.Manuscript.HilbertTensorCompression
import PaperFormalization.Manuscript.MomentKernelMatrix
import PaperFormalization.Manuscript.SourceKernelCovarianceBounds

/-! # Actual source kernels as Hilbert tensor compressions

The row vectors are A(DJ0(Y_i)e_a), and the population columns are DJ0(z)e_b.
Local C2 of the actual objective supplies self-adjointness of A. Thus the
existing kernel matrices and their full population covariance residual are
identified without a kernel-factorization or a nuclear-bound premise.
-/

open Matrix MeasureTheory Set
open scoped BigOperators InnerProductSpace Matrix.Norms.Frobenius

namespace PaperFormalization.Manuscript

variable {N d : ℕ} {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

noncomputable local instance instContinuousENormSourceTensorResidualMatrix :
    ContinuousENorm (Matrix (Fin N × Fin d) (Fin N × Fin d) ℝ) :=
  SeminormedAddGroup.toContinuousENorm

/-- The actual derivative's standard Euclidean columns, in encoded Hilbert coordinates. -/
noncomputable def actualFeatureDerivativeColumns
    (J : EuclideanSpace ℝ (Fin d) → H) (z : EuclideanSpace ℝ (Fin d)) (b : Fin d) : H :=
  fderiv ℝ J z (PiLp.single 2 b (1 : ℝ))

/-- The source Hessian applied to the actual sample derivative columns. -/
noncomputable def actualMomentTensorColumns (J : EuclideanSpace ℝ (Fin d) → H)
    (G : H → ℝ) (theta : H) (Y : Fin N → EuclideanSpace ℝ (Fin d)) (i : Fin N × Fin d) : H :=
  momentObjectiveHessian G theta (actualFeatureDerivativeColumns J (Y i.1) i.2)

/-- The actual kernel entry is the inner product of these concrete columns.
Local objective C2 supplies the required self-adjointness. -/
theorem actualMomentKernelMatrix_eq_column_inner
    (J : EuclideanSpace ℝ (Fin d) → H) (G : H → ℝ) (theta : H)
    (x z : EuclideanSpace ℝ (Fin d)) (hG : ContDiffAt ℝ 2 G theta) (a b : Fin d) :
    actualMomentKernelMatrix J G theta x z a b =
      inner ℝ (momentObjectiveHessian G theta (actualFeatureDerivativeColumns J x a))
        (actualFeatureDerivativeColumns J z b) := by
  rw [actualMomentKernelMatrix, euclideanOperatorMatrix_entry]
  have hp := inner_momentIntegralHessian (fderiv ℝ J x) (fderiv ℝ J z)
    (momentObjectiveHessian G theta) (PiLp.single 2 a (1 : ℝ)) (PiLp.single 2 b (1 : ℝ))
  simp only [EuclideanSpace.inner_single_left, map_one, one_mul] at hp
  rw [hp]
  change inner ℝ (actualFeatureDerivativeColumns J x a)
    (momentObjectiveHessian G theta (actualFeatureDerivativeColumns J z b)) = _
  rw [← ContinuousLinearMap.adjoint_inner_left, momentObjectiveHessian_adjoint G theta hG]

/-- The existing stacked source kernel has precisely the tensor-compression
row/column factorization, with no normalization introduced. -/
theorem stacked_actualMomentKernelMatrix_eq_column_inner
    (J : EuclideanSpace ℝ (Fin d) → H) (G : H → ℝ) (theta : H)
    (Y : Fin N → EuclideanSpace ℝ (Fin d)) (z : EuclideanSpace ℝ (Fin d))
    (hG : ContDiffAt ℝ 2 G theta) :
    stackedKernelMatrix (fun i => actualMomentKernelMatrix J G theta (Y i) z) =
      Matrix.of (fun i b => inner ℝ (actualMomentTensorColumns J G theta Y i)
        (actualFeatureDerivativeColumns J z b)) := by
  ext i b
  exact actualMomentKernelMatrix_eq_column_inner J G theta (Y i.1) z hG i.2 b

/-- Compression of the actual derivative-covariance tensor difference equals
the existing full population kernel covariance residual, under the same μ. -/
theorem actual_populationCovarianceResidual_eq_tensor_compression
    (J : EuclideanSpace ℝ (Fin d) → H) (G : H → ℝ) (theta : H)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (Y : Fin N → EuclideanSpace ℝ (Fin d))
    (hG : ContDiffAt ℝ 2 G theta)
    (hW : Integrable (fun z => finiteOperatorCovariance (fderiv ℝ J z)) μ) :
    populationCovarianceResidual μ Y
      (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix J G theta (Y i) z)) =
      hilbertTensorCompression (actualMomentTensorColumns J G theta Y)
        ((∫ z, finiteOperatorCovariance (fderiv ℝ J z) ∂μ) -
          ∫ z, finiteOperatorCovariance (fderiv ℝ J z) ∂finiteEmpiricalMeasure Y) := by
  simp_rw [stacked_actualMomentKernelMatrix_eq_column_inner J G theta Y _ hG]
  exact (hilbertTensorCompression_populationCovarianceResidual μ Y
    (actualMomentTensorColumns J G theta Y) (actualFeatureDerivativeColumns J) hW).symm

/-- The exact row energy is controlled by the actual Hessian operator norm
and the sample's actual derivative Hilbert--Schmidt energies. -/
theorem actualMomentTensorColumns_energy_le (J : EuclideanSpace ℝ (Fin d) → H)
    (G : H → ℝ) (theta : H) (Y : Fin N → EuclideanSpace ℝ (Fin d)) :
    (∑ i, ‖actualMomentTensorColumns J G theta Y i‖ ^ 2) ≤
      ‖momentObjectiveHessian G theta‖ ^ 2 *
        ∑ i, finiteHilbertSchmidtNorm (fderiv ℝ J (Y i)) ^ 2 := by
  simp only [Fintype.sum_prod_type, finiteHilbertSchmidtNorm_sq, Finset.mul_sum,
    actualMomentTensorColumns, actualFeatureDerivativeColumns]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro a _
  exact (pow_le_pow_left₀ (norm_nonneg _)
    ((momentObjectiveHessian G theta).le_opNorm _) 2).trans_eq (mul_pow _ _ 2)

/-- The normalized actual source residual has the exact deterministic
Hilbert--Schmidt reduction. The remaining operator norm is the actual
objective Hessian, and no particle or spatial dimension factor is hidden. -/
theorem actual_populationCovarianceResidual_nuclear_normalized_le
    (J : EuclideanSpace ℝ (Fin d) → H) (G : H → ℝ) (theta : H)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (Y : Fin N → EuclideanSpace ℝ (Fin d))
    (hG : ContDiffAt ℝ 2 G theta)
    (hW : Integrable (fun z => finiteOperatorCovariance (fderiv ℝ J z)) μ) :
    matrixNuclearValue (populationCovarianceResidual μ Y
      (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix J G theta (Y i) z))) / N ≤
      ‖momentObjectiveHessian G theta‖ ^ 2 *
        ((∑ i, finiteHilbertSchmidtNorm (fderiv ℝ J (Y i)) ^ 2) / N) *
        ‖(∫ z, finiteOperatorCovariance (fderiv ℝ J z) ∂μ) -
          ∫ z, finiteOperatorCovariance (fderiv ℝ J z) ∂finiteEmpiricalMeasure Y‖ := by
  have hb := populationCovarianceResidual_nuclear_le_tensor μ Y
    (actualMomentTensorColumns J G theta Y) (actualFeatureDerivativeColumns J) hW
  have he : (∑ i, ‖actualMomentTensorColumns J G theta Y i‖ ^ 2) ≤
      ‖momentObjectiveHessian G theta‖ ^ 2 *
        ∑ i, finiteHilbertSchmidtNorm (fderiv ℝ J (Y i)) ^ 2 :=
    actualMomentTensorColumns_energy_le J G theta Y
  have hd := div_le_div_of_nonneg_right
    (hb.trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))) (Nat.cast_nonneg N)
  have hstack : (fun z => stackedKernelMatrix (fun i =>
      actualMomentKernelMatrix J G theta (Y i) z)) =
      (fun z i b => inner ℝ (actualMomentTensorColumns J G theta Y i)
        (actualFeatureDerivativeColumns J z b)) := by
    funext z
    exact stacked_actualMomentKernelMatrix_eq_column_inner J G theta Y z hG
  rw [hstack]
  change matrixNuclearValue (populationCovarianceResidual μ Y
    (fun z i b => inner ℝ (actualMomentTensorColumns J G theta Y i)
      (actualFeatureDerivativeColumns J z b))) / N ≤
    (‖momentObjectiveHessian G theta‖ ^ 2 *
      ∑ i, finiteHilbertSchmidtNorm (fderiv ℝ J (Y i)) ^ 2) *
      ‖(∫ z, finiteOperatorCovariance (fderiv ℝ J z) ∂μ) -
        ∫ z, finiteOperatorCovariance (fderiv ℝ J z) ∂finiteEmpiricalMeasure Y‖ / N at hd
  exact hd.trans_eq (by ring)

end PaperFormalization.Manuscript
