import PaperFormalization.MatrixFactorization.VectorHermiteParseval
open MeasureTheory ProbabilityTheory
open PaperFormalization.MatrixFactorization
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

-- Degrees zero and one retain the original scalar Hermite normalization.
example {d : Nat} (z : Weight d) (w : UnitSphere d) :
    inner Real (normalizedHermiteTensor d 0 z).val (tensorPower 0 w.val) = 1 := by
  rw [normalizedHermiteTensor_unit, normalizedHermite_zero]
example {d : Nat} (z : Weight d) (w : UnitSphere d) :
    inner Real (normalizedHermiteTensor d 1 z).val (tensorPower 1 w.val) = inner Real w.val z := by
  rw [normalizedHermiteTensor_unit, normalizedHermite_one]
example {d : Nat} (pole : UnitSphere d) (T : MomentTensor d 0) (U : MomentTensor d 1) :
    (∫ z : Weight d, inner Real (normalizedHermiteTensor d 0 z).val T *
      inner Real (normalizedHermiteTensor d 1 z).val U ∂stdGaussian (Weight d)) = 0 :=
  normalizedHermiteTensor_gaussian_inner_of_ne pole T U (by decide)

-- Arbitrary nonsymmetric full inputs are projected by the actual factorial average.
example {d : Nat} (pole : UnitSphere d) (T : MomentTensor d 2) :
    (∫ z : Weight d, (inner Real (normalizedHermiteTensor d 2 z).val T)^2 ∂stdGaussian (Weight d)) =
      ‖tensorSymmetrize d 2 T‖^2 := normalizedHermiteTensor_gaussian_sq pole T
example {d n : Nat} (w : UnitSphere d) :
    (∫ z : Weight d, (inner Real (normalizedHermiteTensor d n z).val (tensorPower n w.val))^2
      ∂stdGaussian (Weight d)) = 1 := by
  rw [normalizedHermiteTensor_gaussian_sq w, tensorSymmetrize_tensorPower, tensorPower_unit_norm, one_pow]
example {d n : Nat} (pole : UnitSphere d) (T : MomentTensor d n) (e : Equiv.Perm (Fin n)) :
    (∫ z : Weight d, (inner Real (normalizedHermiteTensor d n z).val (T - tensorPermute e T))^2
      ∂stdGaussian (Weight d)) = 0 := by
  rw [normalizedHermiteTensor_gaussian_sq pole, map_sub, tensorSymmetrize_permute, sub_self, norm_zero, zero_pow (by decide)]

-- Empty degree sets, empty output coordinates, and arbitrary integrable finite blocks are retained.
example {d : Nat} (T : ∀ n, MomentTensor d n) (z : Weight d) : tensorHermitePolynomial ∅ T z = 0 := by
  simp [tensorHermitePolynomial]
example {d : Nat} (pole : UnitSphere d) (O : Finset Nat) (T : ∀ n, Empty → MomentTensor d n) :
    (∫ z : Weight d, ‖tensorHermiteVectorPolynomial O T z‖^2 ∂stdGaussian (Weight d)) = 0 := by
  rw [tensorHermiteVectorPolynomial_gaussian_sq pole]
  simp
example {d : Nat} (O : Finset Nat) (T : ∀ n, (Fin 2 × Fin 2) → MomentTensor d n) :
    Integrable (fun z : Weight d => ‖tensorHermiteVectorPolynomial O T z‖^2)
      (stdGaussian (Weight d)) := tensorHermiteVectorPolynomial_sq_integrable O T

-- The matrix residual uses the full Frobenius/tensor Hilbert norm and the literal one-half factor.
example {d h : Nat} (pole : UnitSphere d) (O : Finset Nat)
    (T U : ∀ n, SymmetricHermiteCoefficient d (Fin h × Fin h) n) :
    (1 / 2 : Real) * (∫ z : Weight d,
      ‖tensorHermiteVectorPolynomial O (fun n i => (T n i).val) z -
        tensorHermiteVectorPolynomial O (fun n i => (U n i).val) z‖^2 ∂stdGaussian (Weight d)) =
      (1 / 2 : Real) * ∑ n ∈ O, ‖T n - U n‖^2 :=
  congrArg (fun x : Real => (1 / 2 : Real) * x)
    (symmetricHermiteCoefficient_residual_parseval pole O T U)
example {d : Nat} (pole : UnitSphere d)
    (T : ∀ n, SymmetricHermiteCoefficient d (Fin 1) n) :
    (∫ z : Weight d, ‖tensorHermiteVectorPolynomial {0} (fun n i => (T n i).val) z‖^2
      ∂stdGaussian (Weight d)) = ‖T 0‖^2 := by
  rw [symmetricHermiteCoefficient_parseval pole]
  simp
example {d h : Nat} (pole : UnitSphere d) (O : Finset Nat)
    (T : ∀ n, SymmetricHermiteCoefficient d (Fin h × Fin h) n) :
    (∫ z : Weight d,
      ‖tensorHermiteVectorPolynomial O (fun n i => (T n i).val) z -
        tensorHermiteVectorPolynomial O (fun n i => (T n i).val) z‖^2 ∂stdGaussian (Weight d)) = 0 := by
  rw [symmetricHermiteCoefficient_residual_parseval pole]
  simp
