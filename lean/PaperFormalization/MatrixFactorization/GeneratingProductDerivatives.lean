import PaperFormalization.MatrixFactorization.MixedDirectionalDerivatives

/-! # MF46: extracting the Gaussian product coefficients by differentiation

Finite Leibniz sums supply every contraction coefficient. The proof works
with actual analytic exponentials, so no formal-series convergence or
coefficient identity is supplied as an assumption.
-/
open scoped ContDiff
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

/-- Partial directional derivatives depend smoothly on the other displacement. -/
theorem generating_partial_contDiff {d : Nat} (z u v : Weight d) (k : Nat) :
    ContDiff Real ω (fun t : Real =>
      iteratedDeriv k (fun s : Real => hermiteGenerating z (t • u + s • v)) 0) := by
  simp_rw [iteratedDeriv_affine_line (hermiteGenerating_contDiff z)]
  exact (ContinuousMultilinearMap.apply Real (fun _ : Fin k => Weight d) Real
    (fun _ => v)).contDiff.comp
    (((hermiteGenerating_contDiff z).iteratedFDeriv_right (by simp)).comp (by fun_prop))

/-- Differentiating in the second displacement produces a finite sum of
powers of the first displacement and actual remaining derivatives. -/
theorem hermiteGenerating_partial_product {d : Nat} (z u v : Weight d) (m : Nat) (t : Real) :
    hermiteGenerating z (t • u) *
        iteratedDeriv m (fun s : Real => hermiteGenerating z (s • v)) 0 =
      ∑ r ∈ Finset.range (m + 1), (m.choose r : Real) * (t * inner Real u v) ^ r *
        iteratedDeriv (m - r) (fun s : Real => hermiteGenerating z (t • u + s • v)) 0 := by
  have he : (fun s : Real => hermiteGenerating z (t • u) * hermiteGenerating z (s • v)) =
      fun s : Real => Real.exp ((t * inner Real u v) * s) *
        hermiteGenerating z (t • u + s • v) := by
    funext s
    rw [hermiteGenerating_add, real_inner_smul_left, real_inner_smul_right]
    congr 2
    ring
  have hd := congrArg (fun f : Real → Real => iteratedDeriv m f 0) he
  rw [iteratedDeriv_const_mul_field] at hd
  have hc : ContDiffAt Real m
      (fun s : Real => hermiteGenerating z (t • u + s • v)) 0 :=
    (((hermiteGenerating_contDiff z).comp (by fun_prop)).of_le (by simp)).contDiffAt
  rw [iteratedDeriv_fun_mul (f := fun s : Real => Real.exp ((t * inner Real u v) * s))
    (by fun_prop) hc] at hd
  simpa only [iteratedDeriv_exp_const_mul, mul_zero, Real.exp_zero, mul_one] using hd

/-- Two genuine derivative orders recover the exact binomial/factorial
sum. Terms above either input order vanish by their binomial coefficients. -/
theorem hermiteGenerating_product_derivatives {d : Nat}
    (z u v : Weight d) (n m : Nat) :
    iteratedDeriv n (fun t : Real => hermiteGenerating z (t • u)) 0 *
        iteratedDeriv m (fun s : Real => hermiteGenerating z (s • v)) 0 =
      ∑ r ∈ Finset.range (m + 1),
        (m.choose r : Real) * (inner Real u v) ^ r * (n.choose r : Real) *
          (r.factorial : Real) *
        iteratedFDeriv Real (n - r + (m - r)) (hermiteGenerating z) 0
          (Fin.append (fun _ => u) (fun _ => v)) := by
  have he := congrArg (fun f : Real → Real => iteratedDeriv n f 0)
    (funext (hermiteGenerating_partial_product z u v m))
  rw [iteratedDeriv_mul_const_field] at he
  have hs (r : Nat) : ContDiff Real ω (fun t : Real =>
      (m.choose r : Real) * (t * inner Real u v) ^ r *
        iteratedDeriv (m - r) (fun s : Real => hermiteGenerating z (t • u + s • v)) 0) :=
    (contDiff_const.mul ((contDiff_id.mul contDiff_const).pow r)).mul
      (generating_partial_contDiff z u v (m - r))
  rw [iteratedDeriv_fun_sum (fun r _ => ((hs r).of_le (by simp)).contDiffAt)] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro r hr
  have hf := generating_partial_contDiff z u v (m - r)
  have hterm : (fun t : Real => (m.choose r : Real) * (t * inner Real u v) ^ r *
        iteratedDeriv (m - r) (fun s : Real => hermiteGenerating z (t • u + s • v)) 0) =
      fun t : Real => ((m.choose r : Real) * (inner Real u v) ^ r) *
        (t ^ r * iteratedDeriv (m - r)
          (fun s : Real => hermiteGenerating z (t • u + s • v)) 0) := by
    funext t
    rw [mul_pow]
    ring
  rw [hterm, iteratedDeriv_const_mul_field,
    iteratedDeriv_pow_mul_zero n r (hf.of_le (by simp)).contDiffAt]
  have hd := iteratedDeriv_two_directions (hermiteGenerating_contDiff z)
    (n - r) (m - r) 0 u v
  simp only [zero_add] at hd
  rw [hd]
  ring

end PaperFormalization.MatrixFactorization
