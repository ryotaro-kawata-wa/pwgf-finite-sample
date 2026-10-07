import PaperFormalization.MatrixFactorization.TensorHilbertNorm

/-! # MF33: mixed full tensor products as genuine multilinear maps

Each input slot is a Euclidean weight. The target retains every tensor
coordinate with the Hilbert--Schmidt norm; no coordinatewise norm loss is used.
-/
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def mixedTensorMap (d n : Nat) :
    ContinuousMultilinearMap Real (fun _ : Fin n => Weight d) (MomentTensor d n) :=
  (PiLp.continuousLinearEquiv 2 Real (fun _ : Fin n → Fin d => Real)).symm.toContinuousLinearMap.compContinuousMultilinearMap
    (ContinuousMultilinearMap.pi (fun I : Fin n → Fin d =>
      (ContinuousMultilinearMap.mkPiAlgebra Real (Fin n) Real).compContinuousLinearMap
        (fun j => PiLp.proj (𝕜 := Real) 2 (fun _ : Fin d => Real) (I j))))

@[simp] theorem mixedTensorMap_apply {d n : Nat} (v : Fin n → Weight d)
    (I : Fin n → Fin d) : mixedTensorMap d n v I = ∏ j, v j (I j) := rfl

/-- The mixed tensor diagonal is literally the original tensor-power map. -/
theorem mixedTensorMap_diagonal {d n : Nat} (w : Weight d) :
    mixedTensorMap d n (fun _ => w) = tensorPower n w := rfl

/-- Exact Hilbert--Schmidt multiplicativity, including the empty tensor. -/
theorem mixedTensorMap_norm_sq {d n : Nat} (v : Fin n → Weight d) :
    ‖mixedTensorMap d n v‖ ^ 2 = ∏ j, ‖v j‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [mixedTensorMap_apply, ← Finset.prod_pow, EuclideanSpace.real_norm_sq_eq]
  exact (Fintype.prod_sum (fun j (k : Fin d) => v j k ^ 2)).symm

theorem mixedTensorMap_norm {d n : Nat} (v : Fin n → Weight d) :
    ‖mixedTensorMap d n v‖ = ∏ j, ‖v j‖ := by
  have h := mixedTensorMap_norm_sq v
  rw [Finset.prod_pow] at h
  have hp : 0 ≤ ∏ j, ‖v j‖ := Finset.prod_nonneg (fun j _ => norm_nonneg _)
  nlinarith [norm_nonneg (mixedTensorMap d n v)]

/-- A tensor curve differentiates by replacing exactly one slot at a time. -/
theorem mixedTensorMap_hasDerivAt {d n : Nat} {f : Real → Fin n → Weight d}
    {v : Fin n → Weight d} {t : Real} (hf : ∀ j, HasDerivAt (fun s => f s j) (v j) t) :
    HasDerivAt (fun s => mixedTensorMap d n (f s))
      (∑ j, mixedTensorMap d n (Function.update (f t) j (v j))) t := by
  have h := ((mixedTensorMap d n).hasFDerivAt (f t)).comp_hasDerivAt t (hasDerivAt_pi.mpr hf)
  convert h using 1 <;> first | rfl | simp only [ContinuousMultilinearMap.linearDeriv_apply]

end PaperFormalization.MatrixFactorization
