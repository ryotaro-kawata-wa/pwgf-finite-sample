import PaperFormalization.MatrixFactorization.NormalizedChaosCoefficient

open PaperFormalization.MatrixFactorization

-- Empty spatial coordinate sets and no matched slots are included.
example (A : MomentTensor 0 (0 + 0)) (B : MomentTensor 0 (0 + 0)) :
    ‖tensorContraction 0 0 0 0 A B‖ ≤ ‖A‖ * ‖B‖ := tensorContraction_norm_le A B

-- Positive-order tensors in zero spatial dimension are also included.
example (A : MomentTensor 0 (1 + 2)) (B : MomentTensor 0 (2 + 1)) :
    ‖tensorContraction 0 1 1 2 A B‖ ≤ ‖A‖ * ‖B‖ := tensorContraction_norm_le A B

-- Full contraction is precisely the Frobenius inner product.
example {d r : Nat} (A B : MomentTensor d r) (I : Fin (0 + 0) → Fin d) :
    tensorContraction d 0 0 r
      (tensorOrderEquiv (by omega : r = 0 + r) A)
      (tensorOrderEquiv (by omega : r = r + 0) B) I = inner Real A B :=
  tensorContraction_full A B I

-- Partial contraction has the expected original unit-power normalization.
example {d : Nat} (u v : Weight d) :
    tensorContraction d 2 3 1 (tensorPower (2 + 1) u) (tensorPower (1 + 3) v) =
      (inner Real u v) ^ 1 • mixedTensorMap d (2 + 3)
        (Fin.append (fun _ => u) (fun _ => v)) := tensorContraction_tensorPower u v

-- Symmetric averaging does not insert a dimension factor.
example {d n m r : Nat} (A : MomentTensor d (n + r)) (B : MomentTensor d (r + m)) :
    ‖symmetricTensorContraction d n m r A B‖ ≤ ‖A‖ * ‖B‖ :=
  symmetricTensorContraction_norm_le A B

-- The source-order version preserves the same estimate.
example {d : Nat} (A : MomentTensor d 3) (B : MomentTensor d 5) :
    ‖tensorContractOrders d 3 5 2 (by decide) (by decide) A B‖ ≤ ‖A‖ * ‖B‖ :=
  tensorContractOrders_norm_le _ _ A B

-- The normalized first-chaos product has two different coefficients.
example : normalizedChaosCoefficient 1 1 0 = Real.sqrt 2 := by simp
example : normalizedChaosCoefficient 1 1 1 = 1 := by simp

-- The zeroth chaos and out-of-range indices are not silently removed.
example (n : Nat) : normalizedChaosCoefficient n 0 0 = 1 := by simp
example : normalizedChaosCoefficient 1 3 2 = 0 :=
  normalizedChaosCoefficient_eq_zero_of_left_lt (by decide)
example : normalizedChaosCoefficient 3 1 2 = 0 :=
  normalizedChaosCoefficient_eq_zero_of_right_lt (by decide)

-- General factorial normalization includes odd, even, and zero orders.
example (n m r : Nat) :
    normalizedChaosCoefficient n m r * Real.sqrt (n.factorial : Real) *
      Real.sqrt (m.factorial : Real) =
    (r.factorial : Real) * (n.choose r : Real) * (m.choose r : Real) *
      Real.sqrt ((n + m - 2 * r).factorial : Real) :=
  normalizedChaosCoefficient_rescale n m r
