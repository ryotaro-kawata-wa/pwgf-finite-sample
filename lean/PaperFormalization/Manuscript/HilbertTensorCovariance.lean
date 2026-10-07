import PaperFormalization.Manuscript.FiniteHilbertSchmidt
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Completion

/-! # Real Hilbert tensor covariance from actual finite derivative columns

The covariance tensor lives in the completion of the real Hilbert tensor
product. Its finite-column definition is actual, not an assumed covariance
operator. No separability or finite-dimensionality of the feature Hilbert
space is imposed, and no population law is introduced or changed here.
-/

open scoped BigOperators TensorProduct

namespace PaperFormalization.Manuscript

/-- The complete real Hilbert space used to encode covariance tensors. -/
abbrev realHilbertTensor (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] :=
  UniformSpace.Completion (H ⊗[ℝ] H)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Pure tensor as an actual continuous bilinear map into Hilbert completion. -/
noncomputable def hilbertPureTensor : H →L[ℝ] H →L[ℝ] realHilbertTensor H :=
  ((TensorProduct.mk ℝ H H).compr₂
    (UniformSpace.Completion.toComplL : (H ⊗[ℝ] H) →L[ℝ] realHilbertTensor H).toLinearMap).mkContinuous₂
      1 (fun x y => by simp [TensorProduct.norm_tmul])

/-- The bounded bilinear construction has exactly the ordinary pure tensor. -/
@[simp] theorem hilbertPureTensor_apply (x y : H) :
    hilbertPureTensor x y = (↑(x ⊗ₜ[ℝ] y) : realHilbertTensor H) := rfl

/-- Hilbert tensor norm is exactly the product of the two vector norms. -/
@[simp] theorem norm_hilbertPureTensor (x y : H) :
    ‖hilbertPureTensor x y‖ = ‖x‖ * ‖y‖ := by
  simp only [hilbertPureTensor_apply, UniformSpace.Completion.norm_coe, TensorProduct.norm_tmul]

/-- The real Hilbert tensor inner product retains the exact argument order. -/
@[simp] theorem inner_hilbertPureTensor (x y u v : H) :
    inner ℝ (hilbertPureTensor x y) (hilbertPureTensor u v) =
      inner ℝ x u * inner ℝ y v := by
  simp only [hilbertPureTensor_apply, UniformSpace.Completion.inner_coe, TensorProduct.inner_tmul]

/-- The pure tensor is jointly continuous, without assuming a separable H. -/
theorem continuous_hilbertPureTensor :
    Continuous (fun z : H × H => hilbertPureTensor z.1 z.2) := by
  exact (hilbertPureTensor.continuous.comp continuous_fst).clm_apply continuous_snd

variable {ι : Type*} [Fintype ι]

/-- The covariance tensor of an actual finite family of columns. -/
noncomputable def finiteColumnCovariance (v : ι → H) : realHilbertTensor H :=
  ∑ j, hilbertPureTensor (v j) (v j)

/-- The covariance tensor norm is at most the sum of squared column norms,
with no coefficient depending on the number of columns or the feature space. -/
theorem norm_finiteColumnCovariance_le (v : ι → H) :
    ‖finiteColumnCovariance v‖ ≤ ∑ j, ‖v j‖ ^ 2 := by
  exact (norm_sum_le _ _).trans_eq (by simp only [norm_hilbertPureTensor, ← pow_two])

/-- Testing the actual covariance tensor gives the finite Gram bilinear form. -/
theorem inner_finiteColumnCovariance (x y : H) (v : ι → H) :
    inner ℝ (hilbertPureTensor x y) (finiteColumnCovariance v) =
      ∑ j, inner ℝ x (v j) * inner ℝ y (v j) := by
  simp only [finiteColumnCovariance, inner_sum, inner_hilbertPureTensor]

/-- The covariance tensor's tested bilinear form is symmetric. -/
theorem inner_finiteColumnCovariance_swap (x y : H) (v : ι → H) :
    inner ℝ (hilbertPureTensor x y) (finiteColumnCovariance v) =
      inner ℝ (hilbertPureTensor y x) (finiteColumnCovariance v) := by
  rw [inner_finiteColumnCovariance, inner_finiteColumnCovariance]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- A continuous finite column family has a continuous actual covariance
tensor, so AE strong measurability can be inherited from its input law. -/
theorem continuous_finiteColumnCovariance {Ω : Type*} [TopologicalSpace Ω]
    (v : Ω → ι → H) (hv : ∀ j, Continuous (fun x => v x j)) :
    Continuous (fun x => finiteColumnCovariance (v x)) := by
  change Continuous (fun x => ∑ j, hilbertPureTensor (v x j) (v x j))
  exact continuous_finsetSum Finset.univ (fun j _ =>
    ((hilbertPureTensor (H := H)).continuous.comp (hv j)).clm_apply (hv j))

variable [DecidableEq ι]

/-- The covariance tensor of an actual finite-input operator, using the same
standard Euclidean columns as finiteHilbertSchmidtNorm. -/
noncomputable def finiteOperatorCovariance (A : EuclideanSpace ℝ ι →L[ℝ] H) :
    realHilbertTensor H :=
  finiteColumnCovariance (fun j => A (PiLp.single 2 j (1 : ℝ)))

/-- The actual covariance tensor has the required Hilbert--Schmidt square
bound, without a false equality between its norm and the trace. -/
theorem norm_finiteOperatorCovariance_le (A : EuclideanSpace ℝ ι →L[ℝ] H) :
    ‖finiteOperatorCovariance A‖ ≤ finiteHilbertSchmidtNorm A ^ 2 := by
  rw [finiteHilbertSchmidtNorm_sq]
  exact norm_finiteColumnCovariance_le _

/-- Actual operator-norm continuity of the derivative suffices for continuity
of its finite-column covariance in the completed tensor norm. -/
theorem continuous_finiteOperatorCovariance :
    Continuous (finiteOperatorCovariance : (EuclideanSpace ℝ ι →L[ℝ] H) → realHilbertTensor H) := by
  apply continuous_finiteColumnCovariance
  intro j
  exact continuous_id.clm_apply continuous_const

/-- The tensor covariance is exactly the bilinear form of A A*, including
singular A and zero input dimension. -/
theorem inner_finiteOperatorCovariance [CompleteSpace H]
    (A : EuclideanSpace ℝ ι →L[ℝ] H) (x y : H) :
    inner ℝ (hilbertPureTensor x y) (finiteOperatorCovariance A) =
      inner ℝ (A.adjoint x) (A.adjoint y) := by
  rw [finiteOperatorCovariance, inner_finiteColumnCovariance]
  simp_rw [← A.adjoint_inner_left]
  simp only [EuclideanSpace.inner_single_right, one_mul, starRingEnd_apply, star_trivial]
  simp [PiLp.inner_apply, mul_comm]

end PaperFormalization.Manuscript
