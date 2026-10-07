import PaperFormalization.MatrixFactorization.HermiteTensorLowOrder

/-! # MF44: literal zeroth, first, and second Hermite tensors

The identity tensor is the original coordinate identity. The formulas below
hold as full tensor equalities, including zero spatial dimension.
-/
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The original identity tensor, as the sum of coordinate basis squares. -/
noncomputable def tensorIdentity (d : Nat) : MomentTensor d 2 :=
  ∑ i : Fin d, tensorPower 2 (EuclideanSpace.single i (1 : Real))

/-- Every coordinate is the ordinary Kronecker identity entry. -/
@[simp] theorem tensorIdentity_apply {d : Nat} (I : Fin 2 → Fin d) :
    tensorIdentity d I = if I 0 = I 1 then 1 else 0 := by
  classical
  simp [tensorIdentity, tensorPower_apply, Fin.prod_univ_two]

/-- Its pure-power pairing is exactly the Euclidean squared norm. -/
theorem tensorIdentity_inner_power {d : Nat} (u : Weight d) :
    inner Real (tensorIdentity d) (tensorPower 2 u) = ‖u‖ ^ 2 := by
  simp [tensorIdentity, sum_inner, tensorPower_inner, EuclideanSpace.inner_single_left, EuclideanSpace.real_norm_sq_eq]

/-- The identity tensor is symmetric in its original spatial coordinates. -/
theorem tensorIdentity_symmetric (d : Nat) :
    tensorIdentity d ∈ symmetricTensorSubmodule d 2 := by
  apply Submodule.sum_mem
  intro i hi
  exact tensorPower_permutation _

/-- Zeroth normalized Hermite tensor is the scalar tensor one. -/
theorem normalizedHermiteTensor_zero_eq (d : Nat) (z : Weight d) :
    (normalizedHermiteTensor d 0 z).val = tensorPower 0 z := by
  have he := symmetricTensor_ext_of_power_inner (normalizedHermiteTensor d 0 z)
    (symmetricTensorPower 0 z) (fun u => by
      simpa [symmetricTensorPower, tensorPower_inner] using normalizedHermiteTensor_power_zero d z u)
  exact congrArg Subtype.val he

/-- First normalized Hermite tensor is exactly the original input vector,
represented in the unweighted first-order tensor coordinates. -/
theorem normalizedHermiteTensor_one_eq {d : Nat} (z : Weight d) :
    (normalizedHermiteTensor d 1 z).val = tensorPower 1 z := by
  have he := symmetricTensor_ext_of_power_inner (normalizedHermiteTensor d 1 z)
    (symmetricTensorPower 1 z) (fun u => by
      simp [normalizedHermiteTensor_power_one, symmetricTensorPower, tensorPower_inner, real_inner_comm])
  exact congrArg Subtype.val he

/-- The source's exact `(z ⊗ z - I) / sqrt(2)` tensor identity. -/
theorem normalizedHermiteTensor_two_eq {d : Nat} (z : Weight d) :
    (normalizedHermiteTensor d 2 z).val =
      (Real.sqrt 2)⁻¹ • (tensorPower 2 z - tensorIdentity d) := by
  let T : SymmetricMomentTensor d 2 :=
    ⟨(Real.sqrt 2)⁻¹ • (tensorPower 2 z - tensorIdentity d),
      (symmetricTensorSubmodule d 2).smul_mem _
        ((symmetricTensorSubmodule d 2).sub_mem (tensorPower_permutation z) (tensorIdentity_symmetric d))⟩
  have he : normalizedHermiteTensor d 2 z = T := by
    apply symmetricTensor_ext_of_power_inner
    intro u
    change inner Real (normalizedHermiteTensor d 2 z).val (tensorPower 2 u) =
      inner Real ((Real.sqrt 2)⁻¹ • (tensorPower 2 z - tensorIdentity d)) (tensorPower 2 u)
    rw [normalizedHermiteTensor_power_two, real_inner_smul_left, inner_sub_left,
      tensorPower_inner, tensorIdentity_inner_power, real_inner_comm z u]
    ring
  exact congrArg Subtype.val he

end PaperFormalization.MatrixFactorization
