import PaperFormalization.MatrixFactorization.NormalizedHermiteTensor

/-! # MF41: finite normalized tensor Parseval from actual Gaussian integrals

All cross terms are integrable before sums and integrals are interchanged.
The coefficient norm is the original symmetric Hilbert--Schmidt norm.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

noncomputable def tensorHermitePolynomial {d : Nat} (O : Finset Nat)
    (T : ∀ n : Nat, MomentTensor d n) (z : Weight d) : Real :=
  ∑ n ∈ O, inner Real (normalizedHermiteTensor d n z).val (T n)

theorem tensorHermitePolynomial_product {d : Nat} (O : Finset Nat)
    (T U : ∀ n : Nat, MomentTensor d n) (z : Weight d) :
    tensorHermitePolynomial O T z * tensorHermitePolynomial O U z =
      ∑ n ∈ O, ∑ m ∈ O, inner Real (normalizedHermiteTensor d n z).val (T n) *
        inner Real (normalizedHermiteTensor d m z).val (U m) := by
  simp only [tensorHermitePolynomial, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

/-- Finite chaos polynomials have genuinely integrable cross products. -/
theorem tensorHermitePolynomial_product_integrable {d : Nat} (O : Finset Nat)
    (T U : ∀ n : Nat, MomentTensor d n) :
    Integrable (fun z : Weight d => tensorHermitePolynomial O T z * tensorHermitePolynomial O U z)
      (stdGaussian (Weight d)) := by
  simp_rw [tensorHermitePolynomial_product]
  exact integrable_finsetSum O (fun n _ => integrable_finsetSum O
    (fun m _ => normalizedHermiteTensor_product_integrable (T n) (U m)))

/-- The finite mixed Parseval identity includes arbitrary nonsymmetric tensor inputs. -/
theorem tensorHermitePolynomial_gaussian_inner {d : Nat} (pole : UnitSphere d) (O : Finset Nat)
    (T U : ∀ n : Nat, MomentTensor d n) :
    (∫ z : Weight d, tensorHermitePolynomial O T z * tensorHermitePolynomial O U z
      ∂stdGaussian (Weight d)) =
      ∑ n ∈ O, inner Real (tensorSymmetrize d n (T n)) (tensorSymmetrize d n (U n)) := by
  classical
  simp_rw [tensorHermitePolynomial_product]
  rw [integral_finsetSum O (fun n _ => integrable_finsetSum O
    (fun m _ => normalizedHermiteTensor_product_integrable (T n) (U m)))]
  apply Finset.sum_congr rfl
  intro n hn
  rw [integral_finsetSum O (fun m _ => normalizedHermiteTensor_product_integrable (T n) (U m))]
  rw [Finset.sum_eq_single n]
  · exact normalizedHermiteTensor_gaussian_inner pole (T n) (U n)
  · intro m hm hmn
    exact normalizedHermiteTensor_gaussian_inner_of_ne pole (T n) (U m) (Ne.symm hmn)
  · intro h
    exact (h hn).elim

/-- Squaring introduces no factorial weight beyond the original Hermite normalization. -/
theorem tensorHermitePolynomial_gaussian_sq {d : Nat} (pole : UnitSphere d) (O : Finset Nat)
    (T : ∀ n : Nat, MomentTensor d n) :
    (∫ z : Weight d, (tensorHermitePolynomial O T z) ^ 2 ∂stdGaussian (Weight d)) =
      ∑ n ∈ O, ‖tensorSymmetrize d n (T n)‖ ^ 2 := by
  simpa only [pow_two, real_inner_self_eq_norm_sq] using tensorHermitePolynomial_gaussian_inner pole O T T

end PaperFormalization.MatrixFactorization
