import PaperFormalization.Manuscript.SourceKernelIntegrability
import PaperFormalization.Manuscript.MomentKernelMatrix
import PaperFormalization.Manuscript.PopulationCovariance
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-! # Actual population kernel stacks have genuine Gram integrals

The finite matrix adapters preserve the actual kernel and Frobenius norm.
The population variable is unrestricted by any support localization.
-/

open Matrix MeasureTheory Set
open scoped MatrixOrder Matrix.Norms.Frobenius BigOperators

set_option maxSynthPendingDepth 8

namespace PaperFormalization.Manuscript

variable {n k : Type*} [Fintype n] [Fintype k]

noncomputable local instance : ContinuousENorm (Matrix n k ℝ) :=
  SeminormedAddGroup.toContinuousENorm

/-- An actual rectangular L2 matrix factor has a genuinely integrable Gram
matrix. The estimate uses the Frobenius norm, including all matrix entries. -/
theorem integrable_matrix_gram_of_memLp_two {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (U : Ω → Matrix n k ℝ) (hU : MemLp U 2 μ) :
    Integrable (fun z => U z * (U z)ᵀ) μ := by
  have hcont : Continuous (fun A : Matrix n k ℝ => A * Aᵀ) :=
    continuous_id.matrix_mul continuous_id.matrix_transpose
  apply (hU.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).mono'
    (hcont.comp_aestronglyMeasurable hU.aestronglyMeasurable)
  filter_upwards with z
  calc
    ‖U z * (U z)ᵀ‖ ≤ ‖U z‖ * ‖(U z)ᵀ‖ := Matrix.frobenius_norm_mul _ _
    _ = ‖U z‖ ^ 2 := by rw [Matrix.frobenius_norm_transpose]; ring

variable {d N : ℕ}

/-- The actual Euclidean operator-to-matrix map is bounded linear when the
matrix carries its genuine Frobenius norm. -/
noncomputable def euclideanOperatorMatrixLinear :
    (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) →L[ℝ]
      Matrix (Fin d) (Fin d) ℝ :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ)).symm.toAlgEquiv.toLinearEquiv.toLinearMap.toContinuousLinearMap

@[simp] theorem euclideanOperatorMatrixLinear_apply
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    euclideanOperatorMatrixLinear A = euclideanOperatorMatrix A := rfl

/-- Stacking a finite family of matrix blocks is an actual bounded linear map. -/
noncomputable def stackedKernelLinear :
    (Fin N → Matrix (Fin d) (Fin d) ℝ) →L[ℝ]
      Matrix (Fin N × Fin d) (Fin d) ℝ :=
  ({ toFun := stackedKernelMatrix
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } :
    (Fin N → Matrix (Fin d) (Fin d) ℝ) →ₗ[ℝ]
      Matrix (Fin N × Fin d) (Fin d) ℝ).toContinuousLinearMap

@[simp] theorem stackedKernelLinear_apply (H : Fin N → Matrix (Fin d) (Fin d) ℝ) :
    stackedKernelLinear H = stackedKernelMatrix H := rfl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- A fixed left derivative and objective Hessian preserve L2 of the varying
right feature derivative, for the actual moment-mediated kernel matrix. -/
theorem memLp_kernel_matrix_of_memLp_derivative (μ : Measure Ω)
    (B : Ω → (EuclideanSpace ℝ (Fin d) →L[ℝ] H)) (hB : MemLp B 2 μ)
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] H) (T : H →L[ℝ] H) :
    MemLp (fun z => euclideanOperatorMatrix (momentIntegralHessian A (B z) T)) 2 μ := by
  let L := ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin d)) H
    (EuclideanSpace ℝ (Fin d)) (A.adjoint.comp T)
  have h : MemLp (fun z => euclideanOperatorMatrixLinear (L (B z))) 2 μ :=
    (euclideanOperatorMatrixLinear.comp L).comp_memLp' hB
  change MemLp (fun z => euclideanOperatorMatrix ((A.adjoint.comp T).comp (B z))) 2 μ at h
  simpa only [momentIntegralHessian, ContinuousLinearMap.comp_assoc] using h

/-- Finite stacking preserves genuine L2, for any finite dimensions including
zero particle or spatial dimension. -/
theorem memLp_stacked_kernel_of_memLp (μ : Measure Ω)
    (F : Fin N → Ω → Matrix (Fin d) (Fin d) ℝ) (hF : ∀ i, MemLp (F i) 2 μ) :
    MemLp (fun z => stackedKernelMatrix (fun i => F i z)) 2 μ := by
  have hpi : MemLp (fun z i => F i z) 2 μ := MemLp.of_eval hF
  exact stackedKernelLinear.comp_memLp' hpi

/-- The finite stack of actual moment-mediated kernels has an integrable
Gram matrix whenever the actual feature derivative is operator-valued L2.
The fixed points need not localize the population variable. -/
theorem integrable_actualMomentKernelMatrix_gram_of_memLp_fderiv
    [MeasurableSpace (EuclideanSpace ℝ (Fin d))]
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (J : EuclideanSpace ℝ (Fin d) → H) (G : H → ℝ) (theta : H)
    (Y : Fin N → EuclideanSpace ℝ (Fin d))
    (hJ : MemLp (fderiv ℝ J) 2 μ) :
    Integrable (fun z =>
      stackedKernelMatrix (fun i => actualMomentKernelMatrix J G theta (Y i) z) *
      (stackedKernelMatrix (fun i => actualMomentKernelMatrix J G theta (Y i) z))ᵀ) μ := by
  apply integrable_matrix_gram_of_memLp_two
  apply memLp_stacked_kernel_of_memLp
  intro i
  exact memLp_kernel_matrix_of_memLp_derivative μ _ hJ (fderiv ℝ J (Y i))
    (momentObjectiveHessian G theta)

section Source

variable {V : ℕ → Type*} [∀ n, NormedAddCommGroup (V n)]
  [∀ n, InnerProductSpace ℝ (V n)] [∀ n, CompleteSpace (V n)]

/-- The original all-real-order source class and feature hypotheses derive
the actual untruncated population Gram integrability. There is no assumed
Gram integrability, bounded population support, or conditional-law change.
The objective argument is any fixed theta, including the population moment. -/
theorem sourceMomentClass_integrable_actualMomentKernelMatrix_gram
    (c C g p q alpha K : ℝ) (φ : ∀ n, EuclideanSpace ℝ (Fin d) → V n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (halpha : 0 < alpha) (hK : 0 < K)
    (hφ : ∀ n, ContDiff ℝ 2 (φ n))
    (hgrowth : ∀ n x k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) x‖ ≤
      featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1 - k)))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (hμ : μ ∈ sourceMomentClass alpha K)
    (G : lp V 2 → ℝ) (theta : lp V 2)
    (Y : Fin N → EuclideanSpace ℝ (Fin d)) :
    let J := sourceWeightedFeatureMap c p φ
    Integrable (fun z =>
      stackedKernelMatrix (fun i => actualMomentKernelMatrix J G theta (Y i) z) *
      (stackedKernelMatrix (fun i => actualMomentKernelMatrix J G theta (Y i) z))ᵀ) μ := by
  apply integrable_actualMomentKernelMatrix_gram_of_memLp_fderiv
  exact sourceMomentClass_memLp_fderiv_sourceWeightedFeatureMap
    c C g p q alpha K φ hc hC hp hq halpha hK hφ hgrowth μ hμ

end Source

end PaperFormalization.Manuscript
