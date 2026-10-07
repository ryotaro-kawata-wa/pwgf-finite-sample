import PaperFormalization.MatrixFactorization.SphereMoments

/-! # MF01: Frobenius geometry of the literal rank-one matrix output

Output h is the Euclidean space indexed by matrix entries.
Its norm is exactly Frobenius, not the matrix operator norm or row supremum norm.
No spatial/Hermite tensor contraction is postulated here.
-/

namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

abbrev Output (h : Nat) := EuclideanSpace Real (Fin h × Fin h)

noncomputable def outer {h : Nat} (u v : Weight h) : Output h :=
  WithLp.toLp 2 (fun ij => u ij.1*v ij.2)

@[simp] theorem outer_apply {h : Nat} (u v : Weight h) (i j : Fin h) :
    outer u v (i,j) = u i*v j := rfl

@[simp] theorem outer_zero_left {h : Nat} (v : Weight h) : outer 0 v = 0 := by
  ext ij
  simp [outer]

@[simp] theorem outer_zero_right {h : Nat} (u : Weight h) : outer u 0 = 0 := by
  ext ij
  simp [outer]

@[simp] theorem outer_neg_left {h : Nat} (u v : Weight h) : outer (-u) v = -outer u v := by
  ext ij
  simp [outer]

@[simp] theorem outer_neg_right {h : Nat} (u v : Weight h) : outer u (-v) = -outer u v := by
  ext ij
  simp [outer]

theorem outer_smul_left {h : Nat} (t : Real) (u v : Weight h) :
    outer (t • u) v = t • outer u v := by
  ext ij
  simp [outer, smul_eq_mul, mul_assoc]

theorem outer_smul_right {h : Nat} (t : Real) (u v : Weight h) :
    outer u (t • v) = t • outer u v := by
  ext ij
  simp [outer, smul_eq_mul, mul_left_comm]

theorem outer_scale_both {h : Nat} (t : Real) (u v : Weight h) :
    outer (t • u) (t • v) = (t^2) • outer u v := by
  rw [outer_smul_left, outer_smul_right, smul_smul, pow_two]

theorem outer_continuous (h : Nat) :
    Continuous (fun p : Weight h × Weight h => outer p.1 p.2) := by
  unfold outer
  fun_prop

/-- Exact Frobenius inner product, including the empty output dimension. -/
theorem outer_inner {h : Nat} (u v x y : Weight h) :
    inner Real (outer u v) (outer x y) = inner Real u x * inner Real v y := by
  simp [outer, PiLp.inner_apply, Fintype.sum_prod_type,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  exact Finset.sum_comm

theorem outer_norm_sq {h : Nat} (u v : Weight h) :
    norm (outer u v)^2 = norm u^2 * norm v^2 := by
  rw [<- real_inner_self_eq_norm_sq, outer_inner]
  simp only [real_inner_self_eq_norm_sq]

theorem outer_norm {h : Nat} (u v : Weight h) :
    norm (outer u v) = norm u*norm v := by
  have hs := outer_norm_sq u v
  nlinarith [norm_nonneg (outer u v), norm_nonneg u, norm_nonneg v,
    mul_nonneg (norm_nonneg u) (norm_nonneg v)]

/-- The degree-four ray is derived from the rank-one matrix, with its exact 1/2. -/
theorem outer_ray_loss_polynomial {h : Nat} (H : Output h) (u v : Weight h) (t : Real) :
    norm (outer (t • u) (t • v)-H)^2 =
      norm H^2 - 2*t^2*inner Real H (outer u v) + t^4*norm (outer u v)^2 := by
  rw [outer_scale_both, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg t), real_inner_smul_left, real_inner_comm]
  ring

/-- Antisymmetric branch: fitting cross term has the POSITIVE sign. -/
theorem antisymmetric_outer_loss {h : Nat} (teacher u : Weight h) :
    norm (outer u (-u)-outer teacher teacher)^2 =
      norm teacher^4 + 2*(inner Real teacher u)^2 + norm u^4 := by
  rw [outer_neg_right, norm_sub_sq_real, norm_neg, outer_norm_sq, outer_norm_sq,
    inner_neg_left, outer_inner]
  rw [real_inner_comm u teacher]
  ring

/-- Same-density branch: the cross term has the opposite sign. -/
theorem symmetric_outer_loss {h : Nat} (teacher u : Weight h) :
    norm (outer u u-outer teacher teacher)^2 =
      norm teacher^4 - 2*(inner Real teacher u)^2 + norm u^4 := by
  rw [norm_sub_sq_real, outer_norm_sq, outer_norm_sq, outer_inner]
  rw [real_inner_comm u teacher]
  ring

end PaperFormalization.MatrixFactorization
