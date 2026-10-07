import PaperFormalization.MatrixFactorization.SphericalObjectiveTeacher
/-! # MF06: energy-scaled lower bounds for the actual fitting integrand

The elementary variance inequality controls first speed moments by the genuine
second moments. The matrix estimate then retains the nonnegative squared first
output derivative and bounds only the possibly negative residual contribution.
The resulting bound is quadratic in the original tangent energy.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

theorem sphere_speed_integral_sq_le {d : Nat} (mu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] (v : UnitSphere d → Weight d) (hc : Continuous v) :
    (∫ w, norm (v w) ∂mu)^2 ≤ ∫ w, norm (v w)^2 ∂mu := by
  let m := ∫ w, norm (v w) ∂mu
  have hi := sphere_integrable mu _ hc.norm
  have hi2 : Integrable (fun w => norm (v w)^2) mu := sphere_integrable mu _ (hc.norm.pow 2)
  have hn : 0 ≤ ∫ w, (norm (v w)-m)^2 ∂mu := integral_nonneg (fun w => sq_nonneg _)
  have he : (fun w => (norm (v w)-m)^2) = (fun w => norm (v w)^2 - (2*m)*norm (v w) + m^2) := by
    funext w
    ring
  rw [he] at hn
  have hs : Integrable (fun w => norm (v w)^2 - (2*m)*norm (v w)) mu :=
    hi2.sub (hi.const_mul (2*m))
  rw [integral_add (f := fun w => norm (v w)^2 - (2*m)*norm (v w))
    (g := fun _ => m^2) hs (integrable_const (m^2)),
    integral_sub (f := fun w => norm (v w)^2) (g := fun w => (2*m)*norm (v w))
      hi2 (hi.const_mul (2*m)), integral_const_mul] at hn
  simp only [integral_const, probReal_univ, one_smul] at hn
  change 0 ≤ (∫ w, norm (v w)^2 ∂mu) - (2*m)*m + m^2 at hn
  change m^2 ≤ _
  nlinarith

theorem matrixPointSecond_energy_lower {h : Nat} (H : Output h)
    (x y dx dy ddx ddy : Weight h) (B Lx Ly Qx Qy : Real)
    (hB : 0 ≤ B) (hLx : 0 ≤ Lx) (hLy : 0 ≤ Ly) (hQx : 0 ≤ Qx) (hQy : 0 ≤ Qy)
    (hcross : 2*Lx*Ly ≤ Qx+Qy) (hH : norm H ≤ B^2)
    (hx : norm x ≤ B) (hy : norm y ≤ B)
    (hdx : norm dx ≤ Lx*B) (hdy : norm dy ≤ Ly*B)
    (hddx : norm ddx ≤ Qx*B) (hddy : norm ddy ≤ Qy*B) :
    -(4*B^4)*(Qx+Qy) ≤ matrixPointSecond H x y dx dy ddx ddy := by
  have hR : norm (outer x y-H) ≤ 2*B^2 := by
    calc
      _ ≤ norm (outer x y)+norm H := norm_sub_le _ _
      _ ≤ B*B+B^2 := by
        rw [outer_norm]
        exact add_le_add (mul_le_mul hx hy (norm_nonneg _) hB) hH
      _ = _ := by ring
  have hAA : norm (outerSecond x y dx dy ddx ddy) ≤ 2*(Qx+Qy)*B^2 := by
    unfold outerSecond
    calc
      _ ≤ norm (outer ddx y)+norm ((2 : Real) • outer dx dy)+norm (outer x ddy) :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = norm ddx*norm y+2*(norm dx*norm dy)+norm x*norm ddy := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2), outer_norm]
      _ ≤ (Qx*B)*B+2*((Lx*B)*(Ly*B))+B*(Qy*B) :=
        add_le_add (add_le_add (mul_le_mul hddx hy (norm_nonneg _) (mul_nonneg hQx hB))
          (mul_le_mul_of_nonneg_left (mul_le_mul hdx hdy (norm_nonneg _) (mul_nonneg hLx hB)) (by norm_num)))
          (mul_le_mul hx hddy (norm_nonneg _) hB)
      _ = (Qx+2*Lx*Ly+Qy)*B^2 := by ring
      _ ≤ 2*(Qx+Qy)*B^2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have hp := mul_le_mul hR hAA (norm_nonneg _) (by positivity)
  have hi := neg_le_of_abs_le (abs_real_inner_le_norm (outer x y-H) (outerSecond x y dx dy ddx ddy))
  have hs := sq_nonneg (norm (outerFirst x y dx dy))
  unfold matrixPointSecond
  nlinarith

end PaperFormalization.MatrixFactorization
