import PaperFormalization.MatrixFactorization.HermiteTensorRodrigues

open scoped ContDiff
open PaperFormalization.MatrixFactorization

-- Analyticity discharges every finite differentiability requirement.
example (d : Nat) : ContDiff Real ω (gaussianTensorKernel d) := gaussianTensorKernel_contDiff d

-- The exact original scalar normalization is retained at arbitrary order.
example (n : Nat) (x : Real) :
    iteratedDeriv n (fun y : Real => Real.exp (-(y ^ 2 / 2))) x =
      (-1 : Real) ^ n * Real.sqrt (n.factorial : Real) * normalizedHermite n x *
        Real.exp (-(x ^ 2 / 2)) := normalizedHermite_gaussian_iteratedDeriv n x

-- Zero direction and degree zero do not get discarded in the line argument.
example (z : Weight 0) :
    iteratedDeriv 0 (fun t : Real => gaussianTensorKernel 0 (z + t • (0 : Weight 0))) 0 =
      (-1 : Real) ^ 0 * Real.sqrt (Nat.factorial 0 : Real) * gaussianTensorKernel 0 z *
        inner Real (normalizedHermiteTensor 0 0 z).val (tensorPower 0 0) :=
  gaussianTensorKernel_directional_derivative 0 z 0

example {d : Nat} (n : Nat) (z : Weight d) :
    iteratedDeriv (n + 1) (fun t : Real => gaussianTensorKernel d (z + t • (0 : Weight d))) 0 = 0 := by
  rw [gaussianTensorKernel_directional_derivative]
  simp [tensorPower_zero_succ]

-- The whole multilinear derivative, not only one selected direction.
example {d : Nat} (n : Nat) (z : Weight d) :
    iteratedFDeriv Real n (gaussianTensorKernel d) z =
      ((-1 : Real) ^ n * Real.sqrt (n.factorial : Real) * gaussianTensorKernel d z) •
        hermiteTensorMultilinear d n z := gaussianTensorKernel_iteratedFDeriv n z

-- Arbitrary permutations preserve the original full tensor observations.
example {d n : Nat} (T : SymmetricMomentTensor d n) (v : Fin n → Weight d)
    (e : Equiv.Perm (Fin n)) :
    inner Real T.val (mixedTensorMap d n (v ∘ e)) = inner Real T.val (mixedTensorMap d n v) :=
  symmetricTensor_inner_mixed_perm T v e

-- These are original coordinate tensors of actual derivatives.
example (z : Weight 0) :
    gaussianDerivativeTensor 0 0 z =
      ((-1 : Real) ^ 0 * Real.sqrt (Nat.factorial 0 : Real) * gaussianTensorKernel 0 z) •
        (normalizedHermiteTensor 0 0 z).val := gaussianDerivativeTensor_eq 0 z

example {d : Nat} (n : Nat) (z : Weight d) :
    gaussianDerivativeTensor d n z =
      ((-1 : Real) ^ n * Real.sqrt (n.factorial : Real) * gaussianTensorKernel d z) •
        (normalizedHermiteTensor d n z).val := gaussianDerivativeTensor_eq n z

-- Both manuscript presentations retain the sign and factorial, for all orders.
example {d : Nat} (n : Nat) (z : Weight d) :
    (normalizedHermiteTensor d n z).val =
      (((-1 : Real) ^ n / Real.sqrt (n.factorial : Real)) / gaussianTensorKernel d z) •
        gaussianDerivativeTensor d n z := normalizedHermiteTensor_rodrigues n z

example {d : Nat} (n : Nat) (z : Weight d) :
    (normalizedHermiteTensor d n z).val =
      ((Real.sqrt (n.factorial : Real))⁻¹ * Real.exp (‖z‖ ^ 2 / 2) * (-1 : Real) ^ n) •
        gaussianDerivativeTensor d n z := normalizedHermiteTensor_rodrigues_exp n z

example (z : Weight 0) :
    (normalizedHermiteTensor 0 3 z).val =
      ((Real.sqrt (Nat.factorial 3 : Real))⁻¹ * Real.exp (‖z‖ ^ 2 / 2) * (-1 : Real) ^ 3) •
        gaussianDerivativeTensor 0 3 z := normalizedHermiteTensor_rodrigues_exp 3 z

example {d : Nat} (z : Weight d) :
    (normalizedHermiteTensor d 4 z).val =
      ((Real.sqrt (Nat.factorial 4 : Real))⁻¹ * Real.exp (‖z‖ ^ 2 / 2) * (-1 : Real) ^ 4) •
        gaussianDerivativeTensor d 4 z := normalizedHermiteTensor_rodrigues_exp 4 z
