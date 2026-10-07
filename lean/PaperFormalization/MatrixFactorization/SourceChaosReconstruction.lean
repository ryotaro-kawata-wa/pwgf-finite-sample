import PaperFormalization.MatrixFactorization.HermiteTensorProduct
import PaperFormalization.MatrixFactorization.SourceChaosFitPolynomial

/-! # MF47: the general source chaos expansion is the original matrix feature

Finite sums and literal contractions are connected to the same active
Hermite features, for arbitrary finite active sets and symmetric raw inputs.
-/
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

/-- A printed coefficient term has exactly its original Hermite observation,
independently of the equal-order cast used to put it in the output block. -/
theorem normalizedChaosTerm_pairing {d h n m r q : Nat}
    (hn : r ≤ n) (hm : r ≤ m) (hq : n + m - 2 * r = q) (a b : Weight h)
    (A : MomentTensor d n) (B : MomentTensor d m) (z : Weight d) (ij : Fin h × Fin h) :
    inner Real (normalizedHermiteTensor d q z).val
      (normalizedChaosTerm hn hm hq a b A B ij).val =
      normalizedChaosCoefficient n m r * (a ij.1 * b ij.2) *
        inner Real (normalizedHermiteTensor d (n + m - 2 * r) z).val
          (tensorSymmetrize d (n + m - 2 * r) (tensorContractOrders d n m r hn hm A B)) := by
  rw [normalizedChaosTerm_apply, real_inner_smul_right,
    normalizedHermiteTensor_pairing_symmetrize, normalizedHermiteTensor_pairing_orderEquiv,
    normalizedHermiteTensor_pairing_symmetrize]

/-- Taking an output entry and a Hermite observation commutes with the
literal finite coefficient construction. -/
theorem activeChaosCoefficient_pairing {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (q : Nat) (X Y : ActiveMomentSpace d O) (z : Weight d) (ij : Fin h × Fin h) :
    inner Real (normalizedHermiteTensor d q z).val (activeChaosCoefficient O a q X Y ij).val =
      ∑ n : O, ∑ m : O, ∑ r : Fin (min n.val m.val + 1),
        if n.val + m.val - 2 * r.val = q then
          normalizedChaosCoefficient n.val m.val r.val * (a n.val ij.1 * a m.val ij.2) *
            inner Real (normalizedHermiteTensor d (n.val + m.val - 2 * r.val) z).val
              (tensorSymmetrize d (n.val + m.val - 2 * r.val)
                (tensorContractOrders d n.val m.val r.val
                  (by have := r.isLt; omega) (by have := r.isLt; omega) (X.val n) (Y.val m)))
        else 0 := by
  classical
  let ev : SymmetricHermiteCoefficient d (Fin h × Fin h) q →ₗ[Real] Real :=
    ((innerSL Real (normalizedHermiteTensor d q z).val).comp
      ((symmetricTensorSubmodule d q).subtypeL.comp
        (PiLp.proj (𝕜 := Real) 2 (fun _ : Fin h × Fin h => SymmetricMomentTensor d q) ij))).toLinearMap
  change ev (activeChaosCoefficient O a q X Y) = _
  unfold activeChaosCoefficient
  simp only [LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs with hq
  · exact normalizedChaosTerm_pairing _ _ hq _ _ _ _ _ _
  · simp

/-- The original active feature uses precisely the same Hermite observations. -/
theorem activeHermiteFeature_tensor_apply {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (z : Weight d) (X : ActiveMomentSpace d O) :
    activeHermiteFeature O a z X =
      ∑ n : O, inner Real (normalizedHermiteTensor d n.val z).val (X.val n) • a n.val := by
  rw [activeHermiteFeature_apply]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← normalizedHermiteTensor_pairing_symmetric z ⟨X.val n, X.property n⟩]
  rfl

/-- The complete finite coefficient reconstruction is the original matrix
feature product, for every finite active set and every original tensor input. -/
theorem sourceChaosMatrixPolynomial_eq_outer {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (X Y : ActiveMomentSpace d O) (z : Weight d) :
    sourceChaosMatrixPolynomial O a X Y z =
      outer (activeHermiteFeature O a z X) (activeHermiteFeature O a z Y) := by
  classical
  apply PiLp.ext
  intro ij
  change (∑ q ∈ activeChaosDegrees O, inner Real (normalizedHermiteTensor d q z).val
    (activeChaosCoefficient O a q X Y ij).val) =
      (activeHermiteFeature O a z X) ij.1 * (activeHermiteFeature O a z Y) ij.2
  simp_rw [activeChaosCoefficient_pairing]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext n
    rw [Finset.sum_comm]
    arg 2
    ext m
    rw [Finset.sum_comm]
  rw [activeHermiteFeature_tensor_apply, activeHermiteFeature_tensor_apply]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  have hnmax : n.val ≤ activationOrder O := Finset.le_sup (f := id) n.property
  have hmmax : m.val ≤ activationOrder O := Finset.le_sup (f := id) m.property
  have hq (r : Fin (min n.val m.val + 1)) : n.val + m.val - 2 * r.val ∈ activeChaosDegrees O := by
    simp only [activeChaosDegrees, Finset.mem_range]
    omega
  simp only [Finset.sum_ite_eq, hq, if_true]
  have hp := normalizedHermiteTensor_product z
    (⟨X.val n, X.property n⟩ : SymmetricMomentTensor d n.val)
    (⟨Y.val m, Y.property m⟩ : SymmetricMomentTensor d m.val)
  change _ = (inner Real (normalizedHermiteTensor d n.val z).val (X.val n) * a n.val ij.1) *
    (inner Real (normalizedHermiteTensor d m.val z).val (Y.val m) * a m.val ij.2)
  calc
    _ = (a n.val ij.1 * a m.val ij.2) *
        (∑ r : Fin (min n.val m.val + 1), normalizedChaosCoefficient n.val m.val r.val *
          inner Real (normalizedHermiteTensor d (n.val + m.val - 2 * r.val) z).val
            (tensorSymmetrize d (n.val + m.val - 2 * r.val)
              (tensorContractOrders d n.val m.val r.val
                (by have := r.isLt; omega) (by have := r.isLt; omega) (X.val n) (Y.val m)))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = _ := by rw [← hp]; ring

end PaperFormalization.MatrixFactorization
