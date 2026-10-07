import PaperFormalization.MatrixFactorization.HermiteTensorProduct

open scoped ContDiff
open PaperFormalization.MatrixFactorization

-- Zero displacement and degenerate spatial dimension are retained.
example {d : Nat} (z : Weight d) : hermiteGenerating z 0 = 1 := by
  simp [hermiteGenerating]
example (z : Weight 0) : hermiteGenerating z 0 = 1 := by
  simp [hermiteGenerating]
example {d : Nat} (z x : Weight d) :
    hermiteGenerating z x * hermiteGenerating z (-x) = Real.exp (-‖x‖ ^ 2) := by
  rw [hermiteGenerating_add]
  simp [hermiteGenerating]
example {d : Nat} (z : Weight d) (n : Nat) :
    iteratedDeriv (n + 1) (fun t : Real => hermiteGenerating z (t • (0 : Weight d))) 0 = 0 := by
  simp [hermiteGenerating, iteratedDeriv_const]

-- Leibniz power extraction distinguishes an excessive order from exact order.
example : iteratedDeriv 2 (fun t : Real => t ^ 3 * Real.exp t) 0 = 0 := by
  rw [iteratedDeriv_pow_mul_zero 2 3 (by fun_prop)]
  norm_num
example : iteratedDeriv 3 (fun t : Real => t ^ 3 * Real.exp t) 0 = 6 := by
  rw [iteratedDeriv_pow_mul_zero 3 3 (by fun_prop)]
  norm_num
example : iteratedDeriv 4 (fun t : Real => t ^ 3 * Real.exp t) 0 = 24 := by
  rw [iteratedDeriv_pow_mul_zero 4 3 (by fun_prop)]
  norm_num [iteratedDeriv_one, Real.deriv_exp]
example {f : Real → Real} (_hf : ContDiffAt Real 0 f 0) :
    iteratedDeriv 0 (fun t : Real => t ^ 0 * f t) 0 = f 0 := by simp

-- Full symmetric inputs, rather than only unit powers, enter the product.
example {d n m : Nat} (z : Weight d) (A : SymmetricMomentTensor d n)
    (B : SymmetricMomentTensor d m) :
    inner Real (normalizedHermiteTensor d n z).val A.val *
      inner Real (normalizedHermiteTensor d m z).val B.val =
        hermiteProductExpansion d n m z A.val B.val := by
  rw [hermiteProductExpansion_apply, normalizedHermiteTensor_product]
example {d : Nat} (z : Weight d) (A : SymmetricMomentTensor d 2)
    (B : SymmetricMomentTensor d 3) :
    inner Real (normalizedHermiteTensor d 2 z).val A.val *
      inner Real (normalizedHermiteTensor d 3 z).val B.val =
        hermiteProductExpansion d 2 3 z A.val B.val := by
  rw [hermiteProductExpansion_apply, normalizedHermiteTensor_product]
example {d : Nat} (z : Weight d) (A : SymmetricMomentTensor d 0)
    (B : SymmetricMomentTensor d 4) :
    inner Real (normalizedHermiteTensor d 0 z).val A.val *
      inner Real (normalizedHermiteTensor d 4 z).val B.val =
        hermiteProductExpansion d 0 4 z A.val B.val := by
  rw [hermiteProductExpansion_apply, normalizedHermiteTensor_product]
example (z : Weight 0) (A B : SymmetricMomentTensor 0 0) :
    inner Real (normalizedHermiteTensor 0 0 z).val A.val *
      inner Real (normalizedHermiteTensor 0 0 z).val B.val =
        hermiteProductExpansion 0 0 0 z A.val B.val := by
  rw [hermiteProductExpansion_apply, normalizedHermiteTensor_product]
example {d n m : Nat} (z : Weight d) (A : MomentTensor d n) :
    hermiteProductExpansion d n m z A 0 = 0 := by simp
example {d n m : Nat} (z : Weight d) (B : MomentTensor d m) :
    hermiteProductExpansion d n m z 0 B = 0 := by simp
example {d n m : Nat} (z : Weight d) (A : MomentTensor d n) (B : MomentTensor d m) :
    hermiteProductExpansion d n m z (-A) B = -hermiteProductExpansion d n m z A B := by simp
example {d : Nat} (z u v : Weight d) :
    iteratedDeriv 0 (fun t : Real =>
      iteratedDeriv 0 (fun s : Real => hermiteGenerating z (t • u + s • v)) 0) 0 = 1 := by
  simp [hermiteGenerating]
