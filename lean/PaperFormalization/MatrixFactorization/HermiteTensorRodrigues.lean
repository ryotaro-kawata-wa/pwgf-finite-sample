import PaperFormalization.MatrixFactorization.GaussianDirectionalRodrigues
import PaperFormalization.MatrixFactorization.SymmetricMultilinearTensor

/-! # MF45: the all-order actual tensor Rodrigues identity

Gaussian derivatives are genuine iterated Frechet derivatives in the
original ambient space. Symmetry and diagonal values identify the whole
multilinear form, and evaluation on coordinate vectors gives the displayed
tensor formula. No Rodrigues identity is assumed.
-/
open scoped ContDiff
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

/-- The full multilinear form represented by the actual normalized Hermite tensor. -/
noncomputable def hermiteTensorMultilinear (d n : Nat) (z : Weight d) :
    ContinuousMultilinearMap Real (fun _ : Fin n => Weight d) Real :=
  (innerSL Real (normalizedHermiteTensor d n z).val).compContinuousMultilinearMap
    (mixedTensorMap d n)

/-- All mixed Gaussian derivatives, with the exact sign and factorial. -/
theorem gaussianTensorKernel_iteratedFDeriv {d : Nat} (n : Nat) (z : Weight d) :
    iteratedFDeriv Real n (gaussianTensorKernel d) z =
      ((-1 : Real) ^ n * Real.sqrt (n.factorial : Real) * gaussianTensorKernel d z) •
        hermiteTensorMultilinear d n z := by
  apply symmetricMultilinear_ext_of_diagonal
  · intro v e
    exact (gaussianTensorKernel_contDiff d).contDiffAt.iteratedFDeriv_comp_perm v e
  · intro v e
    change _ * inner Real (normalizedHermiteTensor d n z).val (mixedTensorMap d n (v ∘ e)) =
      _ * inner Real (normalizedHermiteTensor d n z).val (mixedTensorMap d n v)
    rw [symmetricTensor_inner_mixed_perm]
  · intro u
    exact gaussianTensorKernel_iteratedFDeriv_diagonal n z u

/-- The raw coordinate tensor of the actual nth Gaussian derivative. -/
noncomputable def gaussianDerivativeTensor (d n : Nat) (z : Weight d) : MomentTensor d n :=
  WithLp.toLp 2 (fun I => iteratedFDeriv Real n (gaussianTensorKernel d) z
    (fun j => EuclideanSpace.single (I j) (1 : Real)))

/-- Full tensor identity before dividing by the positive Gaussian and
factorial factors. This includes order zero and dimension zero. -/
theorem gaussianDerivativeTensor_eq {d : Nat} (n : Nat) (z : Weight d) :
    gaussianDerivativeTensor d n z =
      ((-1 : Real) ^ n * Real.sqrt (n.factorial : Real) * gaussianTensorKernel d z) •
        (normalizedHermiteTensor d n z).val := by
  apply PiLp.ext
  intro I
  change iteratedFDeriv Real n (gaussianTensorKernel d) z
    (fun j => EuclideanSpace.single (I j) (1 : Real)) = _
  rw [gaussianTensorKernel_iteratedFDeriv]
  simp [hermiteTensorMultilinear, mixedTensorMap_standardBasis,
    EuclideanSpace.inner_single_right]

/-- The exact all-order source Rodrigues formula in tensor coordinates. -/
theorem normalizedHermiteTensor_rodrigues {d : Nat} (n : Nat) (z : Weight d) :
    (normalizedHermiteTensor d n z).val =
      (((-1 : Real) ^ n / Real.sqrt (n.factorial : Real)) / gaussianTensorKernel d z) •
        gaussianDerivativeTensor d n z := by
  rw [gaussianDerivativeTensor_eq, smul_smul]
  have hn : Real.sqrt (n.factorial : Real) ≠ 0 := (hermite_normalizer_pos n).ne'
  have hg : gaussianTensorKernel d z ≠ 0 := Real.exp_ne_zero _
  have hs : ((-1 : Real) ^ n) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  have he : ((-1 : Real) ^ n / Real.sqrt (n.factorial : Real) / gaussianTensorKernel d z) *
      ((-1 : Real) ^ n * Real.sqrt (n.factorial : Real) * gaussianTensorKernel d z) = 1 := by
    field_simp
    nlinarith [hs]
  rw [he, one_smul]

/-- The manuscript's equivalent exponential version, with no Gaussian
normalizing constant left to interpret. -/
theorem normalizedHermiteTensor_rodrigues_exp {d : Nat} (n : Nat) (z : Weight d) :
    (normalizedHermiteTensor d n z).val =
      ((Real.sqrt (n.factorial : Real))⁻¹ * Real.exp (‖z‖ ^ 2 / 2) * (-1 : Real) ^ n) •
        gaussianDerivativeTensor d n z := by
  rw [normalizedHermiteTensor_rodrigues]
  congr 1
  simp only [gaussianTensorKernel, Real.exp_neg, div_eq_mul_inv, inv_inv]
  ring

end PaperFormalization.MatrixFactorization
