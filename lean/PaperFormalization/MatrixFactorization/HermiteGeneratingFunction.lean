import PaperFormalization.MatrixFactorization.HermiteTensorRodrigues

/-! # MF46: the actual Hermite generating function

The exponential is evaluated in the original Euclidean space. Its derivatives
are identified with the already constructed Hermite tensors; no generating
series or product formula is assumed.
-/
open scoped ContDiff
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

/-- The actual Gaussian exponential generating function. -/
noncomputable def hermiteGenerating {d : Nat} (z x : Weight d) : Real :=
  Real.exp (inner Real z x - ‖x‖ ^ 2 / 2)

/-- The generating function is analytic in its displacement. -/
theorem hermiteGenerating_contDiff {d : Nat} (z : Weight d) :
    ContDiff Real ω (hermiteGenerating z) := by
  unfold hermiteGenerating
  exact Real.contDiff_exp.comp ((contDiff_const.inner Real contDiff_id).sub
    ((contDiff_norm_sq Real).div_const 2))

/-- Completing the square relates the exponential to the same Gaussian kernel. -/
theorem hermiteGenerating_gaussian {d : Nat} (z x : Weight d) :
    hermiteGenerating z x = (gaussianTensorKernel d z)⁻¹ * gaussianTensorKernel d (z - x) := by
  simp only [hermiteGenerating, gaussianTensorKernel, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  rw [norm_sub_sq_real]
  ring

/-- Multiplication has exactly the cross-covariance exponential factor. -/
theorem hermiteGenerating_add {d : Nat} (z x y : Weight d) :
    hermiteGenerating z x * hermiteGenerating z y =
      Real.exp (inner Real x y) * hermiteGenerating z (x + y) := by
  simp only [hermiteGenerating, ← Real.exp_add, inner_add_right, norm_add_sq_real]
  congr 1
  ring

/-- The directional generating derivatives have the positive sqrt(n!)
normalization, including zero order and zero directions. -/
theorem hermiteGenerating_directional {d : Nat} (n : Nat) (z u : Weight d) :
    iteratedDeriv n (fun t : Real => hermiteGenerating z (t • u)) 0 =
      Real.sqrt (n.factorial : Real) *
        inner Real (normalizedHermiteTensor d n z).val (tensorPower n u) := by
  have he : (fun t : Real => hermiteGenerating z (t • u)) =
      fun t => (gaussianTensorKernel d z)⁻¹ * gaussianTensorKernel d (z + (-t) • u) := by
    funext t
    rw [hermiteGenerating_gaussian, sub_eq_add_neg, neg_smul]
  rw [he, iteratedDeriv_const_mul_field]
  rw [show (fun t : Real => gaussianTensorKernel d (z + (-t) • u)) =
    (fun t : Real => (fun s : Real => gaussianTensorKernel d (z + s • u)) (-t)) from rfl]
  rw [iteratedDeriv_comp_neg n (fun s : Real => gaussianTensorKernel d (z + s • u)) 0]
  simp only [neg_zero, smul_eq_mul]
  rw [gaussianTensorKernel_directional_derivative]
  have hs : (-1 : Real) ^ n * (-1 : Real) ^ n = 1 := by
    rw [← mul_pow]; simp
  have hg : gaussianTensorKernel d z ≠ 0 := Real.exp_ne_zero _
  calc
    _ = ((-1 : Real) ^ n * (-1 : Real) ^ n) *
        ((gaussianTensorKernel d z)⁻¹ * gaussianTensorKernel d z) *
        (Real.sqrt (n.factorial : Real) *
          inner Real (normalizedHermiteTensor d n z).val (tensorPower n u)) := by ring
    _ = _ := by rw [hs, inv_mul_cancel₀ hg]; ring

/-- All mixed derivatives, rather than only diagonal directions, represent
exactly the same normalized Hermite tensor. -/
theorem hermiteGenerating_iteratedFDeriv {d : Nat} (n : Nat) (z : Weight d) :
    iteratedFDeriv Real n (hermiteGenerating z) 0 =
      Real.sqrt (n.factorial : Real) • hermiteTensorMultilinear d n z := by
  apply symmetricMultilinear_ext_of_diagonal
  · intro v e
    exact (hermiteGenerating_contDiff z).contDiffAt.iteratedFDeriv_comp_perm v e
  · intro v e
    change _ * inner Real (normalizedHermiteTensor d n z).val (mixedTensorMap d n (v ∘ e)) =
      _ * inner Real (normalizedHermiteTensor d n z).val (mixedTensorMap d n v)
    rw [symmetricTensor_inner_mixed_perm]
  · intro u
    let L : Real →L[Real] Weight d := (ContinuousLinearMap.id Real Real).smulRight u
    have he := congrArg (fun M : ContinuousMultilinearMap Real (fun _ : Fin n => Real) Real =>
      M (fun _ => 1)) (L.iteratedFDeriv_comp_right (hermiteGenerating_contDiff z)
        (0 : Real) (i := n) (by simp))
    have hd := hermiteGenerating_directional n z u
    rw [iteratedDeriv_eq_iteratedFDeriv] at hd
    simpa [L, Function.comp_def, ContinuousMultilinearMap.compContinuousLinearMap_apply,
      hermiteTensorMultilinear, mixedTensorMap_diagonal] using he.symm.trans hd

end PaperFormalization.MatrixFactorization
