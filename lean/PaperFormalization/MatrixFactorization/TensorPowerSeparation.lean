import PaperFormalization.MatrixFactorization.SymmetricTensorProjection
import Mathlib.Analysis.Analytic.IteratedFDeriv

/-! # MF40: pure powers separate and span symmetric raw tensors

The separation argument differentiates an actual homogeneous diagonal
polynomial. Mathlib's permutation formula for its n-th derivative supplies
the exact n! factor; no polarization or spanning premise is introduced.
-/
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

/-- Mixed products of coordinate vectors are the full tensor coordinate basis. -/
theorem mixedTensorMap_standardBasis {d n : Nat} (I : Fin n → Fin d) :
    mixedTensorMap d n (fun j => EuclideanSpace.single (I j) (1 : Real)) =
      EuclideanSpace.single I (1 : Real) := by
  classical
  apply PiLp.ext
  intro J
  by_cases h : I = J
  · subst J
    simp [mixedTensorMap_apply]
  · have h' : J ≠ I := Ne.symm h
    obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    have hp : (∏ k : Fin n, (EuclideanSpace.single (I k) (1 : Real) : Weight d) (J k)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [EuclideanSpace.single_apply, hj, Ne.symm hj]
    simpa [mixedTensorMap_apply, EuclideanSpace.single_apply, h, h'] using hp

/-- Zero observations on every pure power force a symmetric tensor to be zero. -/
theorem symmetricTensor_eq_zero_of_power_inner_zero {d n : Nat} (T : MomentTensor d n)
    (hT : T ∈ symmetricTensorSubmodule d n)
    (hz : ∀ w : Weight d, inner Real T (tensorPower n w) = 0) : T = 0 := by
  let L : ContinuousMultilinearMap Real (fun _ : Fin n => Weight d) Real :=
    (innerSL Real T).compContinuousMultilinearMap (mixedTensorMap d n)
  have he : (fun w : Weight d => L (fun _ => w)) = fun _ => (0 : Real) := funext hz
  apply PiLp.ext
  intro I
  have hd := L.iteratedFDeriv_comp_diagonal (0 : Weight d)
    (fun j => EuclideanSpace.single (I j) (1 : Real))
  have hs (e : Equiv.Perm (Fin n)) :
      L (fun j => EuclideanSpace.single (I (e j)) (1 : Real)) = T I := by
    change inner Real T (mixedTensorMap d n (fun j => EuclideanSpace.single ((I.comp e) j) (1 : Real))) = _
    rw [mixedTensorMap_standardBasis]
    simpa only [EuclideanSpace.inner_single_right, RCLike.conj_to_real, one_mul] using hT I e
  rw [he] at hd
  simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, ContinuousMultilinearMap.zero_apply,
    hs, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul] at hd
  have hn : (n.factorial : Real) ≠ 0 := by positivity
  change T I = 0
  exact (mul_eq_zero.mp hd.symm).resolve_left hn

/-- Equality is determined by the same pure-power observations, with no tensor-norm change. -/
theorem symmetricTensor_ext_of_power_inner {d n : Nat} (T U : SymmetricMomentTensor d n)
    (he : ∀ w : Weight d, inner Real T.val (tensorPower n w) =
      inner Real U.val (tensorPower n w)) : T = U := by
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply symmetricTensor_eq_zero_of_power_inner_zero _
    ((symmetricTensorSubmodule d n).sub_mem T.property U.property)
  intro w
  rw [inner_sub_left, he w, sub_self]

/-- The actual pure powers span the whole symmetric Hilbert space, also at order zero. -/
theorem symmetricTensorPower_span (d n : Nat) :
    Submodule.span Real (Set.range (@symmetricTensorPower d n)) = ⊤ := by
  apply (Submodule.orthogonal_eq_bot_iff).mp
  apply eq_bot_iff.mpr
  intro T hT
  apply Subtype.ext
  apply symmetricTensor_eq_zero_of_power_inner_zero T.val T.property
  intro w
  have hp : symmetricTensorPower n w ∈ Submodule.span Real (Set.range (@symmetricTensorPower d n)) :=
    Submodule.subset_span ⟨w, rfl⟩
  exact (Submodule.mem_orthogonal' _ _).mp hT _ hp

end PaperFormalization.MatrixFactorization
