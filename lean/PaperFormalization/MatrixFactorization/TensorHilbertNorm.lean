import PaperFormalization.MatrixFactorization.SphereMoments

/-! # MF32: the full Hilbert--Schmidt norm of original moment tensors

The full finite tensor coordinate norm is retained, including order zero.
The estimates use the original probability measure and its Bochner integral.
-/
open MeasureTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Tensor powers have the exact Hilbert--Schmidt normalization. -/
theorem tensorPower_norm_sq {d n : Nat} (w : Weight d) :
    ‖tensorPower n w‖ ^ 2 = (‖w‖ ^ 2) ^ n := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [tensorPower_apply, ← Finset.prod_pow]
  exact (Fintype.sum_pow (fun j : Fin d => w j ^ 2) n).symm

/-- No dimension-dependent factor is introduced by full tensor coordinates. -/
theorem tensorPower_norm {d n : Nat} (w : Weight d) :
    ‖tensorPower n w‖ = ‖w‖ ^ n := by
  have h := tensorPower_norm_sq (n := n) w
  have hp : (‖w‖ ^ 2) ^ n = (‖w‖ ^ n) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [hp] at h
  nlinarith [norm_nonneg (tensorPower n w), pow_nonneg (norm_nonneg w) n]

/-- Unit sphere tensors also have norm one at order zero. -/
theorem tensorPower_unit_norm {d n : Nat} (w : UnitSphere d) :
    ‖tensorPower n w.val‖ = 1 := by
  have hw : ‖w.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using w.property
  simp [tensorPower_norm, hw]

/-- Jensen's norm inequality is applied only after genuine integrability. -/
theorem rawMoment_norm_le_one {d : Nat} (mu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] (n : Nat) : ‖rawMoment mu n‖ ≤ 1 := by
  have hi := rawMoment_integrable mu n
  calc
    ‖rawMoment mu n‖ ≤ ∫ w, ‖tensorPower n w.val‖ ∂mu := norm_integral_le_integral_norm _
    _ = 1 := by simp only [tensorPower_unit_norm]; simp

/-- Every symmetric or antisymmetric raw block has its original unit bound. -/
theorem symmetricMoment_norm_le_one {d : Nat} (mu nu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (n : Nat) :
    ‖symmetricMoment mu nu n‖ ≤ 1 := by
  have hm := rawMoment_norm_le_one mu n
  have hn := rawMoment_norm_le_one nu n
  have hsum := norm_add_le (rawMoment mu n) (rawMoment nu n)
  rw [symmetricMoment, norm_smul]
  norm_num
  linarith

/-- This bound does not require the reflected branch or odd degrees. -/
theorem antisymmetricMoment_norm_le_one {d : Nat} (mu nu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] (n : Nat) :
    ‖antisymmetricMoment mu nu n‖ ≤ 1 := by
  have hm := rawMoment_norm_le_one mu n
  have hn := rawMoment_norm_le_one nu n
  have hsum := norm_sub_le (rawMoment mu n) (rawMoment nu n)
  rw [antisymmetricMoment, norm_smul]
  norm_num
  linarith

end PaperFormalization.MatrixFactorization
