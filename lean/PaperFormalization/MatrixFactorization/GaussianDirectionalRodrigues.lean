import PaperFormalization.MatrixFactorization.HermiteTensorLowOrder
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # MF45: all-order Gaussian directional derivatives

The same normalized Hermite observations are recovered from actual iterated
derivatives of the Gaussian kernel, including zero directions and order zero.
-/
open scoped ContDiff
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

noncomputable def gaussianTensorKernel (d : Nat) (z : Weight d) : Real :=
  Real.exp (-(‖z‖ ^ 2 / 2))

theorem gaussianTensorKernel_contDiff (d : Nat) : ContDiff Real ω (gaussianTensorKernel d) := by
  unfold gaussianTensorKernel
  exact Real.contDiff_exp.comp (((contDiff_norm_sq Real).div_const 2).neg)

/-- The scalar Rodrigues formula uses the actual probabilists' polynomial
and the original sqrt(n!) normalizer. -/
theorem normalizedHermite_gaussian_iteratedDeriv (n : Nat) (x : Real) :
    iteratedDeriv n (fun y : Real => Real.exp (-(y ^ 2 / 2))) x =
      (-1 : Real) ^ n * Real.sqrt (n.factorial : Real) * normalizedHermite n x *
        Real.exp (-(x ^ 2 / 2)) := by
  rw [iteratedDeriv_eq_iterate, Polynomial.deriv_gaussian_eq_hermite_mul_gaussian]
  rw [normalizedHermite_eval]
  have hn : Real.sqrt (n.factorial : Real) ≠ 0 := (hermite_normalizer_pos n).ne'
  change (-1 : Real) ^ n * (Polynomial.hermite n).eval₂ (Int.castRingHom Real) x * _ = _
  field_simp

/-- Completing the square along the actual ambient affine line. -/
theorem gaussianTensorKernel_line_factor {d : Nat} (z u : Weight d) (hu : u ≠ 0) (t : Real) :
    gaussianTensorKernel d (z + t • u) =
      Real.exp (-(‖z‖ ^ 2 / 2) + (inner Real u z / ‖u‖) ^ 2 / 2) *
        Real.exp (-((‖u‖ * t + inner Real u z / ‖u‖) ^ 2 / 2)) := by
  rw [← Real.exp_add]
  unfold gaussianTensorKernel
  congr 1
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_comm z u]
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  field_simp
  ring

/-- The nth derivative along an arbitrary direction is the original tensor
observation with exactly its sign, factorial, and Gaussian factors. -/
theorem gaussianTensorKernel_directional_derivative {d : Nat} (n : Nat) (z u : Weight d) :
    iteratedDeriv n (fun t : Real => gaussianTensorKernel d (z + t • u)) 0 =
      (-1 : Real) ^ n * Real.sqrt (n.factorial : Real) * gaussianTensorKernel d z *
        inner Real (normalizedHermiteTensor d n z).val (tensorPower n u) := by
  by_cases hu : u = 0
  · subst u
    cases n with
    | zero => simp [iteratedDeriv_zero, normalizedHermiteTensor_power_zero]
    | succ n => simp [iteratedDeriv_const, tensorPower_zero_succ]
  · let c : Real := inner Real u z / ‖u‖
    let C : Real := Real.exp (-(‖z‖ ^ 2 / 2) + c ^ 2 / 2)
    have he : (fun t : Real => gaussianTensorKernel d (z + t • u)) =
        fun t => C * Real.exp (-((‖u‖ * t + c) ^ 2 / 2)) :=
      funext (gaussianTensorKernel_line_factor z u hu)
    have hc : ContDiff Real n (fun t : Real => Real.exp (-((t + c) ^ 2 / 2))) := by fun_prop
    have hd : iteratedDeriv n (fun t : Real => Real.exp (-((‖u‖ * t + c) ^ 2 / 2))) 0 =
        ‖u‖ ^ n * iteratedDeriv n (fun t : Real => Real.exp (-(t ^ 2 / 2))) c := by
      rw [iteratedDeriv_comp_const_mul hc ‖u‖,
        iteratedDeriv_comp_add_const n (fun t : Real => Real.exp (-(t ^ 2 / 2))) c]
      simp
    have hC : C * Real.exp (-(c ^ 2 / 2)) = gaussianTensorKernel d z := by
      rw [← Real.exp_add]
      unfold gaussianTensorKernel
      congr 1
      ring
    rw [he, iteratedDeriv_const_mul_field, hd, normalizedHermite_gaussian_iteratedDeriv,
      normalizedHermiteTensor_directional z u hu]
    change C * (‖u‖ ^ n * ((-1 : Real) ^ n * Real.sqrt (n.factorial : Real) *
      normalizedHermite n c * Real.exp (-(c ^ 2 / 2)))) = _
    calc
      _ = (-1 : Real) ^ n * Real.sqrt (n.factorial : Real) *
        (C * Real.exp (-(c ^ 2 / 2))) * (‖u‖ ^ n * normalizedHermite n c) := by ring
      _ = _ := by rw [hC]

/-- The actual iterated Frechet derivative has the same diagonal values. -/
theorem gaussianTensorKernel_iteratedFDeriv_diagonal {d : Nat} (n : Nat) (z u : Weight d) :
    iteratedFDeriv Real n (gaussianTensorKernel d) z (fun _ => u) =
      (-1 : Real) ^ n * Real.sqrt (n.factorial : Real) * gaussianTensorKernel d z *
        inner Real (normalizedHermiteTensor d n z).val (tensorPower n u) := by
  let L : Real →L[Real] Weight d := (ContinuousLinearMap.id Real Real).smulRight u
  have hc : ContDiff Real ω (fun x : Weight d => gaussianTensorKernel d (z + x)) :=
    (gaussianTensorKernel_contDiff d).comp (contDiff_const.add contDiff_id)
  have he := congrArg (fun M : ContinuousMultilinearMap Real (fun _ : Fin n => Real) Real =>
    M (fun _ => 1)) (L.iteratedFDeriv_comp_right hc (0 : Real) (i := n) (by simp))
  have hd := gaussianTensorKernel_directional_derivative n z u
  rw [iteratedDeriv_eq_iteratedFDeriv] at hd
  simpa [L, Function.comp_def, iteratedFDeriv_comp_add_left,
    ContinuousMultilinearMap.compContinuousLinearMap_apply] using he.symm.trans hd

end PaperFormalization.MatrixFactorization
