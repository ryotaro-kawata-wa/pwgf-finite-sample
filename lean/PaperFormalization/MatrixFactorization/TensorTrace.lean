import PaperFormalization.MatrixFactorization.MixedTensorHilbert

/-! # MF37: literal contractions of raw tensor coordinates

A trace contracts two spatial indices in the full Hilbert--Schmidt tensor.
Its action on tensor powers is proved with the original Euclidean norm.
-/
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def tensorTraceLinear (d n : Nat) :
    MomentTensor d (n + 2) →ₗ[Real] MomentTensor d n where
  toFun T := WithLp.toLp 2 (fun I => ∑ j : Fin d, T (Fin.cons j (Fin.cons j I)))
  map_add' T U := by
    apply PiLp.ext
    intro I
    change (∑ j : Fin d, (T (Fin.cons j (Fin.cons j I)) + U (Fin.cons j (Fin.cons j I)))) = _
    exact Finset.sum_add_distrib
  map_smul' c T := by
    apply PiLp.ext
    intro I
    change (∑ j : Fin d, c * T (Fin.cons j (Fin.cons j I))) = _
    exact (Finset.mul_sum _ _ _).symm

noncomputable def tensorTrace (d n : Nat) :
    MomentTensor d (n + 2) →L[Real] MomentTensor d n :=
  (tensorTraceLinear d n).toContinuousLinearMap

@[simp] theorem tensorTrace_apply {d n : Nat} (T : MomentTensor d (n + 2))
    (I : Fin n → Fin d) :
    tensorTrace d n T I = ∑ j : Fin d, T (Fin.cons j (Fin.cons j I)) := rfl

/-- Contracting a repeated pair contributes precisely the squared Euclidean norm. -/
theorem tensorTrace_tensorPower {d n : Nat} (w : Weight d) :
    tensorTrace d n (tensorPower (n + 2) w) = ‖w‖ ^ 2 • tensorPower n w := by
  apply PiLp.ext
  intro I
  simp only [tensorTrace_apply, tensorPower_apply, Fin.prod_univ_succ, Fin.cons_zero,
    Fin.cons_succ, PiLp.smul_apply, smul_eq_mul, EuclideanSpace.real_norm_sq_eq]
  simp_rw [← mul_assoc, ← sq]
  exact (Finset.sum_mul Finset.univ (fun j : Fin d => w j ^ 2)
    (∏ j : Fin n, w (I j))).symm

/-- Tensor-power pairing has no degree factorial or dimension-dependent normalization. -/
theorem tensorPower_inner {d n : Nat} (u v : Weight d) :
    inner Real (tensorPower n u) (tensorPower n v) = (inner Real u v) ^ n := by
  simp only [PiLp.inner_apply, tensorPower_apply, RCLike.inner_apply, conj_trivial,
    ← Finset.prod_mul_distrib]
  exact (Fintype.sum_pow (fun j : Fin d => v j * u j) n).symm

end PaperFormalization.MatrixFactorization
