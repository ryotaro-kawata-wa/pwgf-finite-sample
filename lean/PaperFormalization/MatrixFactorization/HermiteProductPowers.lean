import PaperFormalization.MatrixFactorization.GeneratingProductDerivatives
import PaperFormalization.MatrixFactorization.FirstChaosProduct

/-! # MF46: the all-order product formula on actual tensor powers

The factorial and binomial factors are derived from the generating-function
calculus. The contractions below are the literal coordinate contractions,
including zero-order terms and arbitrary, possibly zero, directions.
-/
open scoped ContDiff
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

/-- The multilinear form evaluates the original mixed tensor directly. -/
theorem hermiteTensorMultilinear_apply {d n : Nat} (z : Weight d) (v : Fin n → Weight d) :
    hermiteTensorMultilinear d n z v =
      inner Real (normalizedHermiteTensor d n z).val (mixedTensorMap d n v) := rfl

/-- Reindexing equal tensor orders does not change a Hermite observation. -/
theorem normalizedHermiteTensor_pairing_orderEquiv {d n m : Nat} (h : n = m)
    (z : Weight d) (T : MomentTensor d n) :
    inner Real (normalizedHermiteTensor d m z).val (tensorOrderEquiv h T) =
      inner Real (normalizedHermiteTensor d n z).val T := by
  subst m
  rfl

/-- The actual matched-index contraction on pure powers supplies one
Euclidean pairing for each contracted slot. -/
theorem tensorContractOrders_power_pairing {d n m r : Nat} (hn : r ≤ n) (hm : r ≤ m)
    (z u v : Weight d) :
    inner Real (normalizedHermiteTensor d (n + m - 2 * r) z).val
      (tensorContractOrders d n m r hn hm (tensorPower n u) (tensorPower m v)) =
      (inner Real u v) ^ r *
        inner Real (normalizedHermiteTensor d (n - r + (m - r)) z).val
          (mixedTensorMap d (n - r + (m - r)) (Fin.append (fun _ => u) (fun _ => v))) := by
  unfold tensorContractOrders
  simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply,
    LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
  rw [tensorOrderEquiv_tensorPower, tensorOrderEquiv_tensorPower,
    normalizedHermiteTensor_pairing_orderEquiv, tensorContraction_tensorPower,
    real_inner_smul_right]

/-- Every pair of actual tensor powers satisfies the manuscript's exact
normalized product formula, for arbitrary natural orders. -/
theorem normalizedHermiteTensor_product_power {d : Nat} (n m : Nat) (z u v : Weight d) :
    inner Real (normalizedHermiteTensor d n z).val (tensorPower n u) *
        inner Real (normalizedHermiteTensor d m z).val (tensorPower m v) =
      ∑ r : Fin (min n m + 1), normalizedChaosCoefficient n m r.val *
        inner Real (normalizedHermiteTensor d (n + m - 2 * r.val) z).val
          (tensorSymmetrize d (n + m - 2 * r.val)
            (tensorContractOrders d n m r.val
              (by have := r.isLt; omega) (by have := r.isLt; omega)
              (tensorPower n u) (tensorPower m v))) := by
  classical
  simp_rw [normalizedHermiteTensor_pairing_symmetrize, tensorContractOrders_power_pairing]
  let F (r : Nat) : Real :=
    (m.choose r : Real) * (inner Real u v) ^ r * (n.choose r : Real) *
      (r.factorial : Real) * Real.sqrt ((n - r + (m - r)).factorial : Real) *
      inner Real (normalizedHermiteTensor d (n - r + (m - r)) z).val
        (mixedTensorMap d (n - r + (m - r)) (Fin.append (fun _ => u) (fun _ => v)))
  have hd := hermiteGenerating_product_derivatives z u v n m
  simp_rw [hermiteGenerating_directional, hermiteGenerating_iteratedFDeriv] at hd
  simp only [smul_apply, smul_eq_mul, hermiteTensorMultilinear_apply] at hd
  have hsum : (∑ r ∈ Finset.range (m + 1), F r) =
      ∑ r ∈ Finset.range (min n m + 1), F r := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro r hr hn
    have hrm := Finset.mem_range.mp hr
    have hrmin : min n m + 1 ≤ r := Nat.le_of_not_lt (by simpa using hn)
    have hrn : n < r := by omega
    simp [F, Nat.choose_eq_zero_of_lt hrn]
  have hn0 := (hermite_normalizer_pos n).ne'
  have hm0 := (hermite_normalizer_pos m).ne'
  apply mul_left_cancel₀ (mul_ne_zero hn0 hm0)
  calc
    _ = ∑ r ∈ Finset.range (m + 1), F r := by
      convert hd using 1
      · ring
      · apply Finset.sum_congr rfl
        intro r hr
        dsimp [F]
        ring
    _ = ∑ r ∈ Finset.range (min n m + 1), F r := hsum
    _ = ∑ r : Fin (min n m + 1), F r.val := (Fin.sum_univ_eq_sum_range F _).symm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      have he : n - r.val + (m - r.val) = n + m - 2 * r.val := by
        have := r.isLt
        omega
      have hc := normalizedChaosCoefficient_rescale n m r.val
      dsimp [F]
      rw [← he] at hc
      linear_combination -(inner Real u v) ^ r.val *
        inner Real (normalizedHermiteTensor d (n - r.val + (m - r.val)) z).val
          (mixedTensorMap d (n - r.val + (m - r.val))
            (Fin.append (fun _ => u) (fun _ => v))) * hc

end PaperFormalization.MatrixFactorization
