import PaperFormalization.MatrixFactorization.TensorHermiteEvaluation
import PaperFormalization.MatrixFactorization.MixedTensorHilbert

/-! # MF40: the manuscript's averaged symmetric tensor projection

The permutation average acts on full Hilbert--Schmidt coordinates and uses
exactly 1/n!. It is not a changed norm or an assumed tensor identity.
-/
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000

/-- A single-order symmetric tensor subspace with its inherited raw Hilbert norm. -/
def symmetricTensorSubmodule (d n : Nat) : Submodule Real (MomentTensor d n) where
  carrier := {T | ∀ I (e : Equiv.Perm (Fin n)), T (I.comp e) = T I}
  zero_mem' := by intro I e; rfl
  add_mem' := by intro T U hT hU I e; change T (I.comp e) + U (I.comp e) = _; rw [hT I e, hU I e]; rfl
  smul_mem' := by intro c T hT I e; change c * T (I.comp e) = _; rw [hT I e]; rfl

abbrev SymmetricMomentTensor (d n : Nat) := symmetricTensorSubmodule d n

def tensorIndexPermutation {d n : Nat} (e : Equiv.Perm (Fin n)) :
    (Fin n → Fin d) ≃ (Fin n → Fin d) where
  toFun I := I.comp e.symm
  invFun I := I.comp e
  left_inv I := by funext j; simp [Function.comp_def]
  right_inv I := by funext j; simp [Function.comp_def]

noncomputable def tensorPermute {d n : Nat} (e : Equiv.Perm (Fin n)) :
    MomentTensor d n ≃ₗᵢ[Real] MomentTensor d n :=
  LinearIsometryEquiv.piLpCongrLeft 2 Real Real (tensorIndexPermutation e)

@[simp] theorem tensorPermute_apply {d n : Nat} (e : Equiv.Perm (Fin n))
    (T : MomentTensor d n) (I : Fin n → Fin d) : tensorPermute e T I = T (I.comp e) := rfl

noncomputable def tensorSymmetrize (d n : Nat) : MomentTensor d n →L[Real] MomentTensor d n :=
  (1 / (n.factorial : Real)) • ∑ e : Equiv.Perm (Fin n),
    (tensorPermute (d := d) e).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem tensorSymmetrize_apply {d n : Nat} (T : MomentTensor d n) (I : Fin n → Fin d) :
    tensorSymmetrize d n T I = (1 / (n.factorial : Real)) *
      ∑ e : Equiv.Perm (Fin n), T (I.comp e) := by
  simp [tensorSymmetrize]

/-- Averaging over all permutations produces a symmetric tensor at every order. -/
theorem tensorSymmetrize_symmetric {d n : Nat} (T : MomentTensor d n) :
    tensorSymmetrize d n T ∈ symmetricTensorSubmodule d n := by
  intro I e
  simp only [tensorSymmetrize_apply]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft e) _ _ (fun f => rfl)

/-- Symmetric tensors are fixed with the exact factorial normalization. -/
theorem tensorSymmetrize_of_symmetric {d n : Nat} (T : MomentTensor d n)
    (hT : T ∈ symmetricTensorSubmodule d n) : tensorSymmetrize d n T = T := by
  apply PiLp.ext
  intro I
  simp only [tensorSymmetrize_apply, hT I, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  have hn : (n.factorial : Real) ≠ 0 := by positivity
  field_simp

@[simp] theorem tensorSymmetrize_idempotent {d n : Nat} (T : MomentTensor d n) :
    tensorSymmetrize d n (tensorSymmetrize d n T) = tensorSymmetrize d n T :=
  tensorSymmetrize_of_symmetric _ (tensorSymmetrize_symmetric T)

@[simp] theorem tensorSymmetrize_tensorPower {d n : Nat} (w : Weight d) :
    tensorSymmetrize d n (tensorPower n w) = tensorPower n w :=
  tensorSymmetrize_of_symmetric _ (tensorPower_permutation w)

/-- Averaging is a contraction for the original Hilbert--Schmidt norm. -/
theorem tensorSymmetrize_norm_le {d n : Nat} (T : MomentTensor d n) :
    ‖tensorSymmetrize d n T‖ ≤ ‖T‖ := by
  have hn : (0 : Real) < n.factorial := by positivity
  have he : tensorSymmetrize d n T = (1 / (n.factorial : Real)) •
      ∑ e : Equiv.Perm (Fin n), tensorPermute e T := by
    simp [tensorSymmetrize]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hn)]
  calc
    _ ≤ (1 / (n.factorial : Real)) * ∑ e : Equiv.Perm (Fin n), ‖tensorPermute e T‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (one_div_nonneg.mpr hn.le)
    _ = ‖T‖ := by
      simp only [LinearIsometryEquiv.norm_map, Finset.sum_const, Finset.card_univ,
        Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
      field_simp

/-- Averaging preserves the inner product against every symmetric tensor. -/
theorem tensorSymmetrize_inner_symmetric {d n : Nat} (T U : MomentTensor d n)
    (hU : U ∈ symmetricTensorSubmodule d n) :
    inner Real (tensorSymmetrize d n T) U = inner Real T U := by
  have hp (e : Equiv.Perm (Fin n)) : inner Real (tensorPermute e T) U = inner Real T U := by
    have he : tensorPermute e U = U := by apply PiLp.ext; intro I; exact hU I e
    calc
      _ = inner Real (tensorPermute e T) (tensorPermute e U) := by rw [he]
      _ = inner Real T U := (tensorPermute e).inner_map_map T U
  have he : tensorSymmetrize d n T = (1 / (n.factorial : Real)) •
      ∑ e : Equiv.Perm (Fin n), tensorPermute e T := by simp [tensorSymmetrize]
  rw [he, real_inner_smul_left, sum_inner]
  simp only [hp, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul]
  have hn : (n.factorial : Real) ≠ 0 := by positivity
  field_simp

/-- The residual of the explicit average is orthogonal to the symmetric space. -/
theorem tensorSymmetrize_residual_orthogonal {d n : Nat} (T : MomentTensor d n) :
    T - tensorSymmetrize d n T ∈ (symmetricTensorSubmodule d n)ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro U hU
  rw [inner_sub_left, tensorSymmetrize_inner_symmetric T U hU, sub_self]

/-- The explicit factorial average is exactly the Hilbert orthogonal projection. -/
theorem tensorSymmetrize_eq_starProjection {d n : Nat} (T : MomentTensor d n) :
    tensorSymmetrize d n T = (symmetricTensorSubmodule d n).starProjection T :=
  ((symmetricTensorSubmodule d n).eq_starProjection_of_mem_orthogonal
    (tensorSymmetrize_symmetric T) (tensorSymmetrize_residual_orthogonal T)).symm

/-- In particular, the original tensor-power observations only see the symmetric part. -/
theorem tensorSymmetrize_inner_tensorPower {d n : Nat} (T : MomentTensor d n) (w : Weight d) :
    inner Real (tensorSymmetrize d n T) (tensorPower n w) = inner Real T (tensorPower n w) :=
  tensorSymmetrize_inner_symmetric T _ (tensorPower_permutation w)

/-- The average is unchanged by an arbitrary permutation of its input slots. -/
theorem tensorSymmetrize_permute {d n : Nat} (e : Equiv.Perm (Fin n)) (T : MomentTensor d n) :
    tensorSymmetrize d n (tensorPermute e T) = tensorSymmetrize d n T := by
  apply PiLp.ext
  intro I
  simp only [tensorSymmetrize_apply, tensorPermute_apply]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight e) _ _ (fun f => rfl)

/-- The explicit average is self-adjoint in the original full tensor Hilbert norm. -/
theorem tensorSymmetrize_inner {d n : Nat} (T U : MomentTensor d n) :
    inner Real (tensorSymmetrize d n T) U = inner Real T (tensorSymmetrize d n U) := by
  calc
    _ = inner Real U (tensorSymmetrize d n T) := real_inner_comm _ _
    _ = inner Real (tensorSymmetrize d n U) (tensorSymmetrize d n T) :=
      (tensorSymmetrize_inner_symmetric U _ (tensorSymmetrize_symmetric T)).symm
    _ = inner Real (tensorSymmetrize d n T) (tensorSymmetrize d n U) := real_inner_comm _ _
    _ = _ := tensorSymmetrize_inner_symmetric T _ (tensorSymmetrize_symmetric U)

/-- Tensor powers take their values in the original symmetric subspace. -/
noncomputable def symmetricTensorPower {d : Nat} (n : Nat) (w : Weight d) : SymmetricMomentTensor d n :=
  ⟨tensorPower n w, tensorPower_permutation w⟩

end PaperFormalization.MatrixFactorization
