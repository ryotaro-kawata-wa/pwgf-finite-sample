import PaperFormalization.MatrixFactorization.TensorHermiteParseval

/-! # MF41: vector and Frobenius Parseval with the exact tensor coefficient norm

Finite output coordinates carry an L2 norm. In particular, taking the output
index to be a pair of matrix indices yields Frobenius, not operator, norm.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

noncomputable def tensorHermiteVectorPolynomial {d : Nat} {ι : Type*} [Fintype ι]
    (O : Finset Nat) (T : ∀ n : Nat, ι → MomentTensor d n) (z : Weight d) : EuclideanSpace Real ι :=
  WithLp.toLp 2 (fun i => tensorHermitePolynomial O (fun n => T n i) z)

/-- The vector output retains the exact sum of squared coordinate observations. -/
theorem tensorHermiteVectorPolynomial_norm_sq {d : Nat} {ι : Type*} [Fintype ι]
    (O : Finset Nat) (T : ∀ n : Nat, ι → MomentTensor d n) (z : Weight d) :
    ‖tensorHermiteVectorPolynomial O T z‖ ^ 2 =
      ∑ i : ι, (tensorHermitePolynomial O (fun n => T n i) z) ^ 2 :=
  EuclideanSpace.real_norm_sq_eq _

theorem tensorHermiteVectorPolynomial_sq_integrable {d : Nat} {ι : Type*} [Fintype ι]
    (O : Finset Nat) (T : ∀ n : Nat, ι → MomentTensor d n) :
    Integrable (fun z : Weight d => ‖tensorHermiteVectorPolynomial O T z‖ ^ 2)
      (stdGaussian (Weight d)) := by
  simp_rw [tensorHermiteVectorPolynomial_norm_sq]
  apply integrable_finsetSum Finset.univ
  intro i hi
  simpa only [pow_two] using tensorHermitePolynomial_product_integrable O (fun n => T n i) (fun n => T n i)

/-- Full output/tensor Hilbert--Schmidt Parseval follows by two justified finite exchanges. -/
theorem tensorHermiteVectorPolynomial_gaussian_sq {d : Nat} {ι : Type*} [Fintype ι]
    (pole : UnitSphere d) (O : Finset Nat) (T : ∀ n : Nat, ι → MomentTensor d n) :
    (∫ z : Weight d, ‖tensorHermiteVectorPolynomial O T z‖ ^ 2 ∂stdGaussian (Weight d)) =
      ∑ n ∈ O, ∑ i : ι, ‖tensorSymmetrize d n (T n i)‖ ^ 2 := by
  simp_rw [tensorHermiteVectorPolynomial_norm_sq]
  have hi (i : ι) : Integrable (fun z : Weight d => (tensorHermitePolynomial O (fun n => T n i) z) ^ 2)
      (stdGaussian (Weight d)) := by
    simpa only [pow_two] using tensorHermitePolynomial_product_integrable O (fun n => T n i) (fun n => T n i)
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp_rw [tensorHermitePolynomial_gaussian_sq pole]
  exact Finset.sum_comm

abbrev SymmetricHermiteCoefficient (d : Nat) (ι : Type*) [Fintype ι] (n : Nat) :=
  PiLp 2 (fun _ : ι => SymmetricMomentTensor d n)

/-- Symmetric coefficient blocks have exactly the source's unweighted full HS norm. -/
theorem symmetricHermiteCoefficient_parseval {d : Nat} {ι : Type*} [Fintype ι]
    (pole : UnitSphere d) (O : Finset Nat) (T : ∀ n : Nat, SymmetricHermiteCoefficient d ι n) :
    (∫ z : Weight d, ‖tensorHermiteVectorPolynomial O (fun n i => (T n i).val) z‖ ^ 2
      ∂stdGaussian (Weight d)) = ∑ n ∈ O, ‖T n‖ ^ 2 := by
  rw [tensorHermiteVectorPolynomial_gaussian_sq pole]
  apply Finset.sum_congr rfl
  intro n hn
  simp_rw [tensorSymmetrize_of_symmetric _ (T n _).property]
  exact (PiLp.norm_sq_eq_of_L2 _ (T n)).symm

/-- The same exact identity holds for a finite matrix-valued residual. -/
theorem symmetricHermiteCoefficient_residual_parseval {d : Nat} {ι : Type*} [Fintype ι]
    (pole : UnitSphere d) (O : Finset Nat)
    (T U : ∀ n : Nat, SymmetricHermiteCoefficient d ι n) :
    (∫ z : Weight d, ‖tensorHermiteVectorPolynomial O (fun n i => (T n i).val) z -
      tensorHermiteVectorPolynomial O (fun n i => (U n i).val) z‖ ^ 2
      ∂stdGaussian (Weight d)) = ∑ n ∈ O, ‖T n - U n‖ ^ 2 := by
  have he (z : Weight d) :
      tensorHermiteVectorPolynomial O (fun n i => (T n i).val) z -
      tensorHermiteVectorPolynomial O (fun n i => (U n i).val) z =
      tensorHermiteVectorPolynomial O (fun n i => ((T n - U n) i).val) z := by
    apply PiLp.ext
    intro i
    change (∑ n ∈ O, inner Real (normalizedHermiteTensor d n z).val (T n i).val) -
      (∑ n ∈ O, inner Real (normalizedHermiteTensor d n z).val (U n i).val) =
      ∑ n ∈ O, inner Real (normalizedHermiteTensor d n z).val ((T n - U n) i).val
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    exact (inner_sub_right _ _ _).symm
  simp_rw [he]
  exact symmetricHermiteCoefficient_parseval pole O (fun n => T n - U n)

end PaperFormalization.MatrixFactorization
