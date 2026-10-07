import PaperFormalization.MatrixFactorization.NormalizedHermiteTensor
import PaperFormalization.MatrixFactorization.NormalizedChaosCoefficient

/-! # MF44: actual first and second normalized Hermite observations

These identities retain zero and nonunit directions. They will be used to
check a genuine product formula, rather than just its numerical coefficients.
-/
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

/-- Homogeneous extension of the original unit-direction Hermite identity. -/
theorem normalizedHermiteTensor_directional {d n : Nat} (z u : Weight d) (hu : u ≠ 0) :
    inner Real (normalizedHermiteTensor d n z).val (tensorPower n u) =
      ‖u‖ ^ n * normalizedHermite n (inner Real u z / ‖u‖) := by
  have hnorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  let w : UnitSphere d := ⟨‖u‖⁻¹ • u, by
    change ‖‖u‖⁻¹ • u - 0‖ = 1
    rw [sub_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg u)),
      inv_mul_cancel₀ hnorm]⟩
  have he : ‖u‖ • w.val = u := by
    change ‖u‖ • (‖u‖⁻¹ • u) = u
    rw [smul_smul, mul_inv_cancel₀ hnorm, one_smul]
  calc
    _ = inner Real (normalizedHermiteTensor d n z).val (tensorPower n (‖u‖ • w.val)) := by rw [he]
    _ = ‖u‖ ^ n * normalizedHermite n (inner Real w.val z) := by
      rw [tensorPower_smul, real_inner_smul_right, normalizedHermiteTensor_unit]
    _ = _ := by
      congr 2
      change inner Real (‖u‖⁻¹ • u) z = _
      rw [real_inner_smul_left]
      ring

/-- The exact normalized quadratic polynomial, with probabilists' convention. -/
theorem normalizedHermite_two (x : Real) :
    normalizedHermite 2 x = (x ^ 2 - 1) / Real.sqrt 2 := by
  norm_num [normalizedHermite, Polynomial.hermite_succ, Polynomial.hermite_one,
    Polynomial.derivative_X, Polynomial.coeff_one, Finset.sum_range_succ]
  ring

/-- First-order observation is the original Euclidean linear feature, also
at the zero direction. -/
theorem normalizedHermiteTensor_power_one {d : Nat} (z u : Weight d) :
    inner Real (normalizedHermiteTensor d 1 z).val (tensorPower 1 u) = inner Real u z := by
  by_cases hu : u = 0
  · subst u
    simp [tensorPower_zero_succ]
  · rw [normalizedHermiteTensor_directional z u hu, normalizedHermite_one, pow_one]
    exact mul_div_cancel₀ _ (norm_ne_zero_iff.mpr hu)

/-- The second tensor's directional observation has the literal covariance
subtraction, with no restriction to unit directions. -/
theorem normalizedHermiteTensor_power_two {d : Nat} (z u : Weight d) :
    inner Real (normalizedHermiteTensor d 2 z).val (tensorPower 2 u) =
      ((inner Real u z) ^ 2 - ‖u‖ ^ 2) / Real.sqrt 2 := by
  by_cases hu : u = 0
  · subst u
    simp [tensorPower_zero_succ]
  · rw [normalizedHermiteTensor_directional z u hu, normalizedHermite_two]
    have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    field_simp

/-- Mixed quadratic coordinates are the polarization of actual tensor powers. -/
theorem tensorPower_two_add {d : Nat} (u v : Weight d) :
    tensorPower 2 (u + v) = tensorPower 2 u + tensorPower 2 v +
      mixedTensorMap d 2 ![u, v] + mixedTensorMap d 2 ![v, u] := by
  apply PiLp.ext
  intro I
  simp [tensorPower_apply, mixedTensorMap_apply, Fin.prod_univ_two]
  ring

/-- Symmetric tensor observations do not depend on the order of two slots. -/
theorem symmetricTensor_inner_mixed_two_comm {d : Nat} (T : SymmetricMomentTensor d 2)
    (u v : Weight d) :
    inner Real T.val (mixedTensorMap d 2 ![u, v]) =
      inner Real T.val (mixedTensorMap d 2 ![v, u]) := by
  have hp : tensorPermute (Equiv.swap (0 : Fin 2) 1) (mixedTensorMap d 2 ![u, v]) =
      mixedTensorMap d 2 ![v, u] := by
    apply PiLp.ext
    intro I
    simp [tensorPermute_apply, mixedTensorMap_apply, Fin.prod_univ_two, Function.comp_def]
    ring
  have ht : tensorPermute (Equiv.swap (0 : Fin 2) 1) T.val = T.val := by
    apply PiLp.ext
    intro I
    exact T.property I _
  have hi := (tensorPermute (d := d) (Equiv.swap (0 : Fin 2) 1)).inner_map_map
    T.val (mixedTensorMap d 2 ![u, v])
  rw [ht, hp] at hi
  exact hi.symm

/-- The exact normalized mixed second-chaos evaluation. -/
theorem normalizedHermiteTensor_mixed_two {d : Nat} (z u v : Weight d) :
    inner Real (normalizedHermiteTensor d 2 z).val (mixedTensorMap d 2 ![u, v]) =
      (inner Real u z * inner Real v z - inner Real u v) / Real.sqrt 2 := by
  have hh := congrArg (fun T : MomentTensor d 2 => inner Real (normalizedHermiteTensor d 2 z).val T)
    (tensorPower_two_add u v)
  simp only [inner_add_right, normalizedHermiteTensor_power_two, inner_add_left,
    norm_add_sq_real] at hh
  rw [symmetricTensor_inner_mixed_two_comm (normalizedHermiteTensor d 2 z) v u] at hh
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  field_simp at hh ⊢
  nlinarith

/-- Tracing down to the same order is exactly the identity map. -/
theorem tensorTraceTo_self (d n : Nat) : tensorTraceTo d n n = ContinuousLinearMap.id Real _ := by
  classical
  have h : ∃ r : Nat, n = n + 2 * r := ⟨0, by omega⟩
  have aux (r : Nat) (he : n = n + 2 * r) (T : MomentTensor d n) :
      tensorIteratedTrace d n r (tensorOrderEquiv he T) = T := by
    have hr : r = 0 := by omega
    subst r
    simp only [tensorIteratedTrace]
    apply PiLp.ext
    intro I
    simp [tensorOrderEquiv_apply, Function.comp_def]
  apply ContinuousLinearMap.ext
  intro T
  rw [tensorTraceTo, dif_pos h]
  exact aux h.choose h.choose_spec T

/-- The scalar zeroth chaos is one, including an empty spatial space. -/
theorem normalizedHermiteTensor_power_zero (d : Nat) (z u : Weight d) :
    inner Real (normalizedHermiteTensor d 0 z).val (tensorPower 0 u) = 1 := by
  rw [normalizedHermiteTensor_pairing, tensorSymmetrize_tensorPower]
  simp [tensorHermiteEvaluation, Polynomial.hermite_zero, tensorTraceTo_self, tensorPower_inner]

end PaperFormalization.MatrixFactorization
