import PaperFormalization.MatrixFactorization.HermiteGeneratingFunction

/-! # MF46: mixed directional derivatives and exact power extraction

These calculus lemmas retain genuine derivatives of smooth functions. They
allow the Gaussian generating identity to yield its actual mixed tensor
coefficients, with the factorials supplied by Leibniz' rule.
-/
open scoped ContDiff
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

/-- The scalar derivative of an ambient affine line is the actual directional derivative. -/
theorem deriv_affine_line {d : Nat} {f : Weight d → Real}
    (hf : Differentiable Real f) (x u : Weight d) (t : Real) :
    deriv (fun s : Real => f (x + s • u)) t = fderiv Real f (x + t • u) u := by
  have hl : HasDerivAt (fun s : Real => x + s • u) u t := by
    simpa using ((hasDerivAt_id t).smul_const u).const_add x
  exact ((hf _).hasFDerivAt.comp_hasDerivAt t hl).deriv

/-- Iterating on an affine line gives the diagonal of the actual Frechet derivative. -/
theorem iteratedDeriv_affine_line {d : Nat} {f : Weight d → Real}
    (hf : ContDiff Real ω f) (n : Nat) (x u : Weight d) :
    iteratedDeriv n (fun t : Real => f (x + t • u)) 0 =
      iteratedFDeriv Real n f x (fun _ => u) := by
  let L : Real →L[Real] Weight d := (ContinuousLinearMap.id Real Real).smulRight u
  have hc : ContDiff Real ω (fun y : Weight d => f (x + y)) :=
    hf.comp (contDiff_const.add contDiff_id)
  have he := congrArg (fun M : ContinuousMultilinearMap Real (fun _ : Fin n => Real) Real =>
    M (fun _ => 1)) (L.iteratedFDeriv_comp_right hc (0 : Real) (i := n) (by simp))
  simpa [iteratedDeriv_eq_iteratedFDeriv, L, Function.comp_def,
    iteratedFDeriv_comp_add_left, ContinuousMultilinearMap.compContinuousLinearMap_apply] using he

/-- The two scalar derivative orders are the corresponding mixed Frechet
coefficient. The first block contains the outer direction. -/
theorem iteratedDeriv_two_directions {d : Nat} {f : Weight d → Real}
    (hf : ContDiff Real ω f) (m n : Nat) (x v u : Weight d) :
    iteratedDeriv m (fun t : Real =>
      iteratedDeriv n (fun s : Real => f (x + t • v + s • u)) 0) 0 =
      iteratedFDeriv Real (m + n) f x (Fin.append (fun _ => v) (fun _ => u)) := by
  induction n generalizing f with
  | zero =>
    simpa [Fin.append_right_nil, Function.comp_def] using iteratedDeriv_affine_line hf m x v
  | succ n ih =>
    let g : Weight d → Real := fun y => fderiv Real f y u
    have hdf : ContDiff Real ω (fderiv Real f) := hf.fderiv_right (by simp)
    have hg : ContDiff Real ω g := hdf.clm_apply contDiff_const
    have he (t : Real) :
        iteratedDeriv (n + 1) (fun s : Real => f (x + t • v + s • u)) 0 =
          iteratedDeriv n (fun s : Real => g (x + t • v + s • u)) 0 := by
      rw [iteratedDeriv_succ']
      congr 2
      funext s
      exact deriv_affine_line (hf.differentiable (by simp)) (x + t • v) u s
    simp_rw [he]
    rw [ih hg]
    rw [iteratedFDeriv_clm_apply_const_apply hdf (by simp)]
    have ha : Fin.append (fun _ : Fin m => v) (fun _ : Fin (n + 1) => u) =
        Fin.snoc (Fin.append (fun _ : Fin m => v) (fun _ : Fin n => u)) u := by
      rw [← Fin.append_snoc]
      congr 1
      funext i
      cases i using Fin.lastCases <;> simp
    rw [ha]
    have hh := (iteratedFDeriv_succ_apply_right (𝕜 := Real) (f := f) (x := x)
        (Fin.snoc (Fin.append (fun _ : Fin m => v) (fun _ : Fin n => u)) u)).symm
    simp only [Fin.init_snoc, Fin.snoc_last] at hh
    convert hh using 1
    congr 1

/-- A power at the origin selects exactly one term of the genuine Leibniz
sum. Degrees larger than the derivative order give zero automatically. -/
theorem iteratedDeriv_pow_mul_zero (m r : Nat) {f : Real → Real}
    (hf : ContDiffAt Real m f 0) :
    iteratedDeriv m (fun t : Real => t ^ r * f t) 0 =
      (m.choose r : Real) * (r.factorial : Real) * iteratedDeriv (m - r) f 0 := by
  rw [iteratedDeriv_fun_mul (by fun_prop) hf]
  simp only [iteratedDeriv_fun_pow_zero]
  by_cases hr : r ≤ m
  · rw [Finset.sum_eq_single r]
    · simp
    · intro b hb hbr
      simp [hbr]
    · intro h
      exact (h (Finset.mem_range.mpr (by omega))).elim
  · have hz : m.choose r = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hz]
    simp only [Nat.cast_zero, zero_mul]
    apply Finset.sum_eq_zero
    intro i hi
    have hir : i ≠ r := by have := Finset.mem_range.mp hi; omega
    simp [hir]

end PaperFormalization.MatrixFactorization
