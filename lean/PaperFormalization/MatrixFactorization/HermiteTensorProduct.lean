import PaperFormalization.MatrixFactorization.HermiteProductPowers

/-! # MF46: the normalized product formula for all symmetric tensors

Both sides are bilinear in the original tensor arguments. The verified
spanning theorem extends the actual pure-power calculation to every
symmetric tensor, without a nonzero-direction or positive-dimension premise.
-/
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

/-- The explicit contraction side of the product formula, as a bilinear map. -/
noncomputable def hermiteProductExpansion (d n m : Nat) (z : Weight d) :
    MomentTensor d n →ₗ[Real] MomentTensor d m →ₗ[Real] Real :=
  ∑ r : Fin (min n m + 1), normalizedChaosCoefficient n m r.val •
    ((tensorContractOrders d n m r.val
      (by have := r.isLt; omega) (by have := r.isLt; omega)).compr₂
        (((innerSL Real (normalizedHermiteTensor d (n + m - 2 * r.val) z).val).comp
          (tensorSymmetrize d (n + m - 2 * r.val))).toLinearMap))

/-- The bilinear packaging retains exactly the printed finite contraction sum. -/
theorem hermiteProductExpansion_apply {d n m : Nat} (z : Weight d)
    (A : MomentTensor d n) (B : MomentTensor d m) :
    hermiteProductExpansion d n m z A B =
      ∑ r : Fin (min n m + 1), normalizedChaosCoefficient n m r.val *
        inner Real (normalizedHermiteTensor d (n + m - 2 * r.val) z).val
          (tensorSymmetrize d (n + m - 2 * r.val)
            (tensorContractOrders d n m r.val
              (by have := r.isLt; omega) (by have := r.isLt; omega) A B)) := by
  simp [hermiteProductExpansion]

/-- The manuscript's general normalized Wiener-chaos tensor product formula.
The inputs use the original full Hilbert--Schmidt symmetric tensor spaces. -/
theorem normalizedHermiteTensor_product {d n m : Nat} (z : Weight d)
    (A : SymmetricMomentTensor d n) (B : SymmetricMomentTensor d m) :
    inner Real (normalizedHermiteTensor d n z).val A.val *
        inner Real (normalizedHermiteTensor d m z).val B.val =
      ∑ r : Fin (min n m + 1), normalizedChaosCoefficient n m r.val *
        inner Real (normalizedHermiteTensor d (n + m - 2 * r.val) z).val
          (tensorSymmetrize d (n + m - 2 * r.val)
            (tensorContractOrders d n m r.val
              (by have := r.isLt; omega) (by have := r.isLt; omega) A.val B.val)) := by
  classical
  let l := (innerSL Real (normalizedHermiteTensor d n z).val).toLinearMap.comp
    (symmetricTensorSubmodule d n).subtype
  let k := (innerSL Real (normalizedHermiteTensor d m z).val).toLinearMap.comp
    (symmetricTensorSubmodule d m).subtype
  let L := l.smulRight k
  let R := (hermiteProductExpansion d n m z).compl₁₂
    (symmetricTensorSubmodule d n).subtype (symmetricTensorSubmodule d m).subtype
  have he : L = R := by
    apply LinearMap.ext_on (symmetricTensorPower_span d n)
    rintro _ ⟨u, rfl⟩
    apply LinearMap.ext_on (symmetricTensorPower_span d m)
    rintro _ ⟨v, rfl⟩
    simpa [L, R, l, k, symmetricTensorPower, hermiteProductExpansion_apply] using
      normalizedHermiteTensor_product_power n m z u v
  rw [← hermiteProductExpansion_apply]
  exact congrArg (fun f => f A B) he

end PaperFormalization.MatrixFactorization
