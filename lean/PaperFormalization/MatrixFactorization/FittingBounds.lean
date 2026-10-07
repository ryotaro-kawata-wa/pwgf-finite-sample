import PaperFormalization.MatrixFactorization.FittingDifferential

/-! # MF04: domination of the matrix fitting integrand and its derivatives

These finite-dimensional estimates use the exact Frobenius outer product.
A single nonnegative feature bound controls the loss and both derivatives.
The model construction later supplies that bound from actual Gaussian envelopes.
-/
open MeasureTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

theorem outerFirst_norm_bound {h : Nat} (x y dx dy : Weight h) (B : Real)
    (hB : 0 ≤ B) (hx : norm x ≤ B) (hy : norm y ≤ B)
    (hdx : norm dx ≤ B) (hdy : norm dy ≤ B) : norm (outerFirst x y dx dy) ≤ 2*B^2 := by
  calc
    _ ≤ norm (outer dx y)+norm (outer x dy) := norm_add_le _ _
    _ ≤ B*B+B*B := by
      simp only [outer_norm]
      exact add_le_add (mul_le_mul hdx hy (norm_nonneg _) hB)
        (mul_le_mul hx hdy (norm_nonneg _) hB)
    _ = _ := by ring

theorem outerSecond_norm_bound {h : Nat} (x y dx dy ddx ddy : Weight h) (B : Real)
    (hB : 0 ≤ B) (hx : norm x ≤ B) (hy : norm y ≤ B)
    (hdx : norm dx ≤ B) (hdy : norm dy ≤ B)
    (hddx : norm ddx ≤ B) (hddy : norm ddy ≤ B) :
    norm (outerSecond x y dx dy ddx ddy) ≤ 4*B^2 := by
  have hb1 := mul_le_mul hddx hy (norm_nonneg _) hB
  have hb2 := mul_le_mul hdx hdy (norm_nonneg _) hB
  have hb3 := mul_le_mul hx hddy (norm_nonneg _) hB
  unfold outerSecond
  calc
    _ ≤ norm (outer ddx y)+norm ((2 : Real) • outer dx dy)+norm (outer x ddy) :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = norm ddx*norm y + 2*(norm dx*norm dy) + norm x*norm ddy := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2), outer_norm]
    _ ≤ B*B+2*(B*B)+B*B := add_le_add (add_le_add hb1 (by linarith)) hb3
    _ = _ := by ring

theorem matrixPoint_uniform_bounds {h : Nat} (H : Output h) (x y dx dy ddx ddy : Weight h)
    (B : Real) (hB : 0 ≤ B) (hH : norm H ≤ B^2)
    (hx : norm x ≤ B) (hy : norm y ≤ B) (hdx : norm dx ≤ B) (hdy : norm dy ≤ B)
    (hddx : norm ddx ≤ B) (hddy : norm ddy ≤ B) :
    norm (matrixPointLoss H x y) ≤ 2*B^4 ∧
    norm (matrixPointFirst H x y dx dy) ≤ 4*B^4 ∧
    norm (matrixPointSecond H x y dx dy ddx ddy) ≤ 12*B^4 := by
  have hR : norm (outer x y-H) ≤ 2*B^2 := by
    calc
      _ ≤ norm (outer x y)+norm H := norm_sub_le _ _
      _ ≤ B*B+B^2 := by
        rw [outer_norm]
        exact add_le_add (mul_le_mul hx hy (norm_nonneg _) hB) hH
      _ = _ := by ring
  have hA := outerFirst_norm_bound x y dx dy B hB hx hy hdx hdy
  have hAA := outerSecond_norm_bound x y dx dy ddx ddy B hB hx hy hdx hdy hddx hddy
  refine ⟨?_, ?_, ?_⟩
  · rw [matrixPointLoss, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hs := pow_le_pow_left₀ (norm_nonneg (outer x y-H)) hR 2
    nlinarith
  · change |inner Real (outer x y-H) (outerFirst x y dx dy)| ≤ _
    calc
      _ ≤ norm (outer x y-H)*norm (outerFirst x y dx dy) := abs_real_inner_le_norm _ _
      _ ≤ (2*B^2)*(2*B^2) := mul_le_mul hR hA (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · unfold matrixPointSecond
    calc
      _ ≤ norm (norm (outerFirst x y dx dy)^2) +
          norm (inner Real (outer x y-H) (outerSecond x y dx dy ddx ddy)) := norm_add_le _ _
      _ ≤ (2*B^2)^2 + (2*B^2)*(4*B^2) := by
        apply add_le_add
        · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact pow_le_pow_left₀ (norm_nonneg _) hA 2
        · exact (abs_real_inner_le_norm _ _).trans (mul_le_mul hR hAA (norm_nonneg _) (by positivity))
      _ = _ := by ring

theorem matrixPoint_stronglyMeasurable {Omega : Type*} [MeasurableSpace Omega] {h : Nat}
    (H : Omega → Output h) (X Y DX DY DDX DDY : Omega → Weight h)
    (hH : StronglyMeasurable H) (hX : StronglyMeasurable X) (hY : StronglyMeasurable Y)
    (hDX : StronglyMeasurable DX) (hDY : StronglyMeasurable DY)
    (hDDX : StronglyMeasurable DDX) (hDDY : StronglyMeasurable DDY) :
    StronglyMeasurable (fun z => matrixPointLoss (H z) (X z) (Y z)) ∧
    StronglyMeasurable (fun z => matrixPointFirst (H z) (X z) (Y z) (DX z) (DY z)) ∧
    StronglyMeasurable (fun z => matrixPointSecond (H z) (X z) (Y z) (DX z) (DY z) (DDX z) (DDY z)) := by
  have hR := (outer_stronglyMeasurable X Y hX hY).sub hH
  have hA := (outer_stronglyMeasurable DX Y hDX hY).add (outer_stronglyMeasurable X DY hX hDY)
  have hAA := ((outer_stronglyMeasurable DDX Y hDDX hY).add
    ((outer_stronglyMeasurable DX DY hDX hDY).const_smul (2 : Real))).add
    (outer_stronglyMeasurable X DDY hX hDDY)
  exact ⟨(hR.norm.pow 2).div stronglyMeasurable_const, hR.inner hA,
    (hA.norm.pow 2).add (hR.inner hAA)⟩

end PaperFormalization.MatrixFactorization
