import PaperFormalization.MatrixFactorization.ActiveHermiteFeature
import PaperFormalization.MatrixFactorization.GaussianIntegrability

/-! # MF38: polynomial envelopes for the actual tensor Hermite evaluator

The constants below justify Gaussian integrability on the entire active
Hilbert space. They are domination constants, not the source curvature constant.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def tensorHermiteMass (d n : Nat) : Real :=
  ∑ k ∈ Finset.range (n + 1),
    |((Polynomial.hermite n).coeff k : Real) / Real.sqrt (n.factorial : Real)| *
      ‖tensorTraceTo d n k‖

theorem tensorHermiteMass_nonneg (d n : Nat) : 0 ≤ tensorHermiteMass d n :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (norm_nonneg _))

theorem tensorHermiteEvaluation_continuous_input {d n : Nat} (T : MomentTensor d n) :
    Continuous (fun z : Weight d => tensorHermiteEvaluation d n z T) := by
  classical
  simp only [tensorHermiteEvaluation, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_eq_mul]
  apply continuous_finsetSum
  intro k hk
  exact continuous_const.mul ((tensorPower_continuous d k).inner continuous_const)

/-- The coefficient bound is uniform over every raw tensor, not only moments of laws. -/
theorem tensorHermiteEvaluation_bound {d n : Nat} (T : MomentTensor d n) (z : Weight d) :
    ‖tensorHermiteEvaluation d n z T‖ ≤ tensorHermiteMass d n * ‖T‖ * (1 + ‖z‖) ^ n := by
  classical
  simp only [tensorHermiteEvaluation, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_eq_mul]
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        ‖(((Polynomial.hermite n).coeff k : Real) / Real.sqrt (n.factorial : Real)) *
          inner Real (tensorPower k z) (tensorTraceTo d n k T)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        (|((Polynomial.hermite n).coeff k : Real) / Real.sqrt (n.factorial : Real)| *
          ‖tensorTraceTo d n k‖) * ‖T‖ * (1 + ‖z‖) ^ n := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
      have hp : ‖z‖ ^ k ≤ (1 + ‖z‖) ^ n :=
        (pow_le_pow_left₀ (norm_nonneg z) (by linarith) k).trans
          (pow_le_pow_right₀ (by linarith [norm_nonneg z]) hkn)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      calc
        _ ≤ |((Polynomial.hermite n).coeff k : Real) / Real.sqrt (n.factorial : Real)| *
            (‖tensorPower k z‖ * ‖tensorTraceTo d n k T‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
        _ ≤ |((Polynomial.hermite n).coeff k : Real) / Real.sqrt (n.factorial : Real)| *
            ((1 + ‖z‖) ^ n * (‖tensorTraceTo d n k‖ * ‖T‖)) := by
          rw [tensorPower_norm]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul hp ((tensorTraceTo d n k).le_opNorm T) (norm_nonneg _)
              (by positivity)) (abs_nonneg _)
        _ = _ := by ring
    _ = _ := by unfold tensorHermiteMass; rw [Finset.sum_mul, Finset.sum_mul]

/-- A polynomial envelope gives all natural Gaussian moments, including power zero. -/
theorem tensorHermiteEvaluation_gaussian_power_integrable {d n : Nat}
    (T : MomentTensor d n) (q : Nat) :
    Integrable (fun z : Weight d => ‖tensorHermiteEvaluation d n z T‖ ^ q)
      (stdGaussian (Weight d)) := by
  have hc : Continuous (fun z : Weight d => tensorHermiteEvaluation d n z T) :=
    tensorHermiteEvaluation_continuous_input T
  have hi := (gaussian_one_add_norm_pow_integrable d (n * q)).const_mul
    ((tensorHermiteMass d n * ‖T‖) ^ q)
  apply hi.mono' (hc.norm.pow q).aestronglyMeasurable
  filter_upwards [] with z
  change ‖(‖tensorHermiteEvaluation d n z T‖ ^ q : Real)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  calc
    _ ≤ (tensorHermiteMass d n * ‖T‖ * (1 + ‖z‖) ^ n) ^ q :=
      pow_le_pow_left₀ (norm_nonneg _) (tensorHermiteEvaluation_bound T z) q
    _ = _ := by rw [mul_pow, ← pow_mul]

end PaperFormalization.MatrixFactorization
