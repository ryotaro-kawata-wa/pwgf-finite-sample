import PaperFormalization.Manuscript.CovarianceMismatch
import PaperFormalization.Manuscript.MomentGradientField

/-! # Actual moment-kernel operators and their finite real matrices

The matrix conversion is inverse to the actual Euclidean continuous linear
operator construction. Thus its operator norm is preserved exactly. Local C2
regularity of G supplies Hessian self-adjointness, hence transpose symmetry of
the two spatial kernel slots. No invertibility or extra feature regularity is
used for these algebraic/symmetry facts. Population integrability is not claimed.
-/

open Matrix

namespace PaperFormalization.Manuscript

variable {d : ℕ}

/-- The actual matrix of a Euclidean continuous linear operator. -/
noncomputable def euclideanOperatorMatrix
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin d) (Fin d) ℝ := (Matrix.toEuclideanCLM (𝕜 := ℝ)).symm A

/-- Converting an operator to a matrix and back is exactly the same operator. -/
theorem matrixEuclideanOperator_euclideanOperatorMatrix
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    matrixEuclideanOperator (euclideanOperatorMatrix A) = A := by
  change (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)) ((Matrix.toEuclideanCLM (𝕜 := ℝ)).symm A) = A
  exact (Matrix.toEuclideanCLM (𝕜 := ℝ)).apply_symm_apply A

/-- Conversely the conversion recovers every real d-by-d matrix. -/
theorem euclideanOperatorMatrix_matrixEuclideanOperator (M : Matrix (Fin d) (Fin d) ℝ) :
    euclideanOperatorMatrix (matrixEuclideanOperator M) = M := by
  exact (Matrix.toEuclideanCLM (𝕜 := ℝ)).symm_apply_apply M

/-- The source operator norm has no factor introduced by the matrix conversion. -/
theorem euclideanOperatorMatrix_operator_norm
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    ‖matrixEuclideanOperator (euclideanOperatorMatrix A)‖ = ‖A‖ := by
  rw [matrixEuclideanOperator_euclideanOperatorMatrix]

/-- Exact matrix entries are standard-basis operator evaluations. -/
theorem euclideanOperatorMatrix_entry
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (i j : Fin d) :
    euclideanOperatorMatrix A i j = A (PiLp.single 2 j (1 : ℝ)) i := by
  have h := matrixEuclideanOperator_single (euclideanOperatorMatrix A) j i
  rw [matrixEuclideanOperator_euclideanOperatorMatrix] at h
  exact h.symm

/-- The conversion preserves differences, which are used by the local bounds. -/
theorem euclideanOperatorMatrix_sub
    (A B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    euclideanOperatorMatrix (A - B) = euclideanOperatorMatrix A - euclideanOperatorMatrix B :=
  map_sub (Matrix.toEuclideanCLM (𝕜 := ℝ)).symm A B

/-- Actual composition becomes matrix multiplication in the same order. -/
theorem euclideanOperatorMatrix_comp
    (A B : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    euclideanOperatorMatrix (A.comp B) = euclideanOperatorMatrix A * euclideanOperatorMatrix B :=
  map_mul (Matrix.toEuclideanCLM (𝕜 := ℝ)).symm A B

/-- The actual Hilbert adjoint becomes the real matrix transpose. -/
theorem euclideanOperatorMatrix_adjoint
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    euclideanOperatorMatrix A.adjoint = (euclideanOperatorMatrix A)ᵀ := by
  change (Matrix.toEuclideanCLM (𝕜 := ℝ)).symm (star A) = _
  rw [map_star, Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  rfl

section Moment

variable {H E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual Riesz Hessian has the exact second-derivative pairing. -/
theorem inner_momentObjectiveHessian (G : H → ℝ) (theta u v : H) :
    inner ℝ u (momentObjectiveHessian G theta v) =
      fderiv ℝ (fderiv ℝ G) theta v u := by
  change inner ℝ u ((InnerProductSpace.toDual ℝ H).symm
    (fderiv ℝ (fderiv ℝ G) theta v)) = _
  rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]

/-- Local C2 of the actual objective derives self-adjointness; it is not an
extra Hessian-symmetry assumption. -/
theorem momentObjectiveHessian_adjoint (G : H → ℝ) (theta : H)
    (hG : ContDiffAt ℝ 2 G theta) :
    (momentObjectiveHessian G theta).adjoint = momentObjectiveHessian G theta := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_left ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right,
    real_inner_comm u (momentObjectiveHessian G theta v),
    inner_momentObjectiveHessian, inner_momentObjectiveHessian]
  exact (hG.isSymmSndFDerivAt (by norm_num)) v u

/-- Adjoint reverses the two point slots of the actual integral Hessian. -/
theorem momentIntegralHessian_adjoint_swap
    (A B : E →L[ℝ] H) (T : H →L[ℝ] H) (hT : T.adjoint = T) :
    (momentIntegralHessian A B T).adjoint = momentIntegralHessian B A T := by
  simp only [momentIntegralHessian, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, hT, ContinuousLinearMap.comp_assoc]

/-- The original local objective regularity supplies the actual kernel's
slot-adjoint symmetry, without assumptions on nonexistent global derivatives. -/
theorem actualMomentIntegralHessian_adjoint_swap (φ : E → H) (G : H → ℝ)
    (theta : H) (x y : E) (hG : ContDiffAt ℝ 2 G theta) :
    (momentIntegralHessian (fderiv ℝ φ x) (fderiv ℝ φ y) (momentObjectiveHessian G theta)).adjoint =
      momentIntegralHessian (fderiv ℝ φ y) (fderiv ℝ φ x) (momentObjectiveHessian G theta) :=
  momentIntegralHessian_adjoint_swap _ _ _ (momentObjectiveHessian_adjoint G theta hG)

end Moment

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The actual finite matrix of the moment-mediated source Hessian kernel. -/
noncomputable def actualMomentKernelMatrix (φ : EuclideanSpace ℝ (Fin d) → H)
    (G : H → ℝ) (theta : H) (x y : EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin d) (Fin d) ℝ :=
  euclideanOperatorMatrix (momentIntegralHessian (fderiv ℝ φ x) (fderiv ℝ φ y)
    (momentObjectiveHessian G theta))

/-- The finite actual kernel matrix obeys the source transpose-swap identity. -/
theorem actualMomentKernelMatrix_transpose (φ : EuclideanSpace ℝ (Fin d) → H)
    (G : H → ℝ) (theta : H) (x y : EuclideanSpace ℝ (Fin d)) (hG : ContDiffAt ℝ 2 G theta) :
    (actualMomentKernelMatrix φ G theta x y)ᵀ = actualMomentKernelMatrix φ G theta y x := by
  unfold actualMomentKernelMatrix
  rw [← euclideanOperatorMatrix_adjoint, actualMomentIntegralHessian_adjoint_swap φ G theta x y hG]

/-- Applying the actual kernel at a finite cloud gives a symmetric normalized
empirical factor; the source block-symmetry premise is now derived. -/
theorem actualMomentKernel_empiricalFactor_isHermitian {N : ℕ}
    (φ : EuclideanSpace ℝ (Fin d) → H) (G : H → ℝ) (theta : H)
    (Y : Fin N → EuclideanSpace ℝ (Fin d)) (hG : ContDiffAt ℝ 2 G theta) :
    (empiricalKernelFactor (fun i j => actualMomentKernelMatrix φ G theta (Y i) (Y j))).IsHermitian :=
  empiricalKernelFactor_isHermitian _ (fun i j => actualMomentKernelMatrix_transpose φ G theta (Y i) (Y j) hG)

end PaperFormalization.Manuscript
