import PaperFormalization.MatrixFactorization.IteratedTensorTrace
import PaperFormalization.MatrixFactorization.HermiteFeatures

/-! # MF37: actual normalized Hermite evaluation on raw tensor blocks

The coefficients are Mathlib's probabilists' Hermite coefficients divided by
sqrt(n!). Lower monomials are obtained by genuine pair contractions. On the
unit sphere this evaluates exactly to the original normalized activation.
-/
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def tensorTraceTo (d n k : Nat) : MomentTensor d n →L[Real] MomentTensor d k := by
  classical
  exact if h : ∃ r : Nat, n = k + 2 * r then
    (tensorIteratedTrace d k h.choose).comp (tensorOrderEquiv h.choose_spec).toContinuousLinearMap
  else 0

/-- Only an equality of tensor orders is used in selecting the number of contractions. -/
theorem tensorTraceTo_unit {d n k : Nat} (h : ∃ r : Nat, n = k + 2 * r)
    (w : UnitSphere d) : tensorTraceTo d n k (tensorPower n w.val) = tensorPower k w.val := by
  classical
  rw [tensorTraceTo, dif_pos h]
  change tensorIteratedTrace d k h.choose
    (tensorOrderEquiv h.choose_spec (tensorPower n w.val)) = _
  rw [tensorOrderEquiv_tensorPower, tensorIteratedTrace_unit]

/-- A missing contraction order is exactly a zero Hermite coefficient in the used range. -/
theorem hermite_coeff_eq_zero_of_no_trace {n k : Nat} (hk : k ≤ n)
    (h : ¬ ∃ r : Nat, n = k + 2 * r) : (Polynomial.hermite n).coeff k = 0 := by
  apply Polynomial.coeff_hermite_of_odd_add
  rcases Nat.even_or_odd (n + k) with he | ho
  · rcases he with ⟨j, hj⟩
    exact False.elim (h ⟨(n - k) / 2, by omega⟩)
  · exact ho

noncomputable def tensorHermiteEvaluation (d n : Nat) (z : Weight d) :
    MomentTensor d n →L[Real] Real :=
  ∑ k ∈ Finset.range (n + 1),
    (((Polynomial.hermite n).coeff k : Real) / Real.sqrt (n.factorial : Real)) •
      ((innerSL Real (tensorPower k z)).comp (tensorTraceTo d n k))

/-- The source's directional Hermite identity holds for the original sphere feature. -/
theorem tensorHermiteEvaluation_unit {d n : Nat} (z : Weight d) (w : UnitSphere d) :
    tensorHermiteEvaluation d n z (tensorPower n w.val) = normalizedHermite n (inner Real w.val z) := by
  classical
  simp only [tensorHermiteEvaluation, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_eq_mul]
  rw [normalizedHermite, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : ∃ r : Nat, n = k + 2 * r
  · rw [tensorTraceTo_unit h, tensorPower_inner, real_inner_comm w.val z]
    ring
  · have hc := hermite_coeff_eq_zero_of_no_trace (n := n) (k := k)
      (by have := Finset.mem_range.mp hk; omega) h
    simp [hc]

/-- Every tensor-power coordinate is an actual polynomial in the input. -/
theorem tensorPower_contDiff (d n : Nat) : ContDiff Real ⊤ (@tensorPower d n) := by
  exact (mixedTensorMap d n).contDiff.comp (by fun_prop)

/-- The block evaluator is smooth jointly in the tensor and Gaussian input. -/
theorem tensorHermiteEvaluation_contDiff (d n : Nat) :
    ContDiff Real ⊤ (fun p : MomentTensor d n × Weight d => tensorHermiteEvaluation d n p.2 p.1) := by
  classical
  simp only [tensorHermiteEvaluation, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_eq_mul]
  apply ContDiff.sum
  intro k hk
  exact contDiff_const.mul (((tensorPower_contDiff d k).comp contDiff_snd).inner Real
    ((tensorTraceTo d n k).contDiff.comp contDiff_fst))

end PaperFormalization.MatrixFactorization
