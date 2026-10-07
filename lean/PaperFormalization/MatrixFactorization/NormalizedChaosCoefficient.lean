import PaperFormalization.MatrixFactorization.TensorContractionBounds

/-! # MF42: source orders and normalized chaos coefficients

The source-facing contraction rewrites only equal tensor orders. The
coefficient below is exactly the printed factorial/binomial/square-root
factor; defining it does not assert the unproved full product formula.
-/
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The source's `r`-fold matched contraction, retaining exactly
`n + m - 2 * r` free slots. The two inequalities express its original domain. -/
noncomputable def tensorContractOrders (d n m r : Nat) (hn : r ≤ n) (hm : r ≤ m) :
    MomentTensor d n →ₗ[Real] MomentTensor d m →ₗ[Real]
      MomentTensor d (n + m - 2 * r) :=
  ((tensorContraction d (n - r) (m - r) r).compl₁₂
    (tensorOrderEquiv (d := d) (by omega : n = n - r + r)).toLinearEquiv.toLinearMap
    (tensorOrderEquiv (d := d) (by omega : m = r + (m - r))).toLinearEquiv.toLinearMap).compr₂
      (tensorOrderEquiv (d := d) (by omega : n - r + (m - r) = n + m - 2 * r)).toLinearEquiv.toLinearMap

/-- Order bookkeeping preserves the dimension-free constant one. -/
theorem tensorContractOrders_norm_le {d n m r : Nat} (hn : r ≤ n) (hm : r ≤ m)
    (A : MomentTensor d n) (B : MomentTensor d m) :
    ‖tensorContractOrders d n m r hn hm A B‖ ≤ ‖A‖ * ‖B‖ := by
  unfold tensorContractOrders
  simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply,
    LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
  rw [LinearIsometryEquiv.norm_map]
  exact (tensorContraction_norm_le _ _).trans_eq (by simp)

/-- The literal normalized Wiener-chaos coefficient from the manuscript. -/
noncomputable def normalizedChaosCoefficient (n m r : Nat) : Real :=
  (r.factorial : Real) * (n.choose r : Real) * (m.choose r : Real) *
    Real.sqrt (( (n + m - 2 * r).factorial : Real) /
      ((n.factorial : Real) * (m.factorial : Real)))

theorem normalizedChaosCoefficient_nonneg (n m r : Nat) :
    0 ≤ normalizedChaosCoefficient n m r := by
  unfold normalizedChaosCoefficient
  positivity

theorem normalizedChaosCoefficient_eq_zero_of_left_lt {n m r : Nat} (h : n < r) :
    normalizedChaosCoefficient n m r = 0 := by
  simp [normalizedChaosCoefficient, Nat.choose_eq_zero_of_lt h]

theorem normalizedChaosCoefficient_eq_zero_of_right_lt {n m r : Nat} (h : m < r) :
    normalizedChaosCoefficient n m r = 0 := by
  simp [normalizedChaosCoefficient, Nat.choose_eq_zero_of_lt h]

/-- Exchanging the input orders does not change the source coefficient. -/
theorem normalizedChaosCoefficient_comm (n m r : Nat) :
    normalizedChaosCoefficient n m r = normalizedChaosCoefficient m n r := by
  simp only [normalizedChaosCoefficient, Nat.add_comm n m]
  congr 1 <;> ring

/-- The square-root ratio is precisely the conversion between normalized
and unnormalized Hermite tensors. Every factorial is strictly positive. -/
theorem normalizedChaosCoefficient_rescale (n m r : Nat) :
    normalizedChaosCoefficient n m r * Real.sqrt (n.factorial : Real) *
        Real.sqrt (m.factorial : Real) =
      (r.factorial : Real) * (n.choose r : Real) * (m.choose r : Real) *
        Real.sqrt ((n + m - 2 * r).factorial : Real) := by
  have hn : 0 < (n.factorial : Real) := by positivity
  have hm : 0 < (m.factorial : Real) := by positivity
  unfold normalizedChaosCoefficient
  rw [Real.sqrt_div (by positivity), Real.sqrt_mul (le_of_lt hn)]
  have hs₁ := Real.sqrt_pos.2 hn
  have hs₂ := Real.sqrt_pos.2 hm
  field_simp

@[simp] theorem normalizedChaosCoefficient_one_one_zero :
    normalizedChaosCoefficient 1 1 0 = Real.sqrt 2 := by
  norm_num [normalizedChaosCoefficient]

@[simp] theorem normalizedChaosCoefficient_one_one_one :
    normalizedChaosCoefficient 1 1 1 = 1 := by
  norm_num [normalizedChaosCoefficient]

@[simp] theorem normalizedChaosCoefficient_zero_right (n : Nat) :
    normalizedChaosCoefficient n 0 0 = 1 := by
  have hn : (n.factorial : Real) ≠ 0 := by positivity
  simp [normalizedChaosCoefficient, hn]

end PaperFormalization.MatrixFactorization
