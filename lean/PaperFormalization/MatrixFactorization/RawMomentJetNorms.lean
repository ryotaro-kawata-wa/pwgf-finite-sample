import PaperFormalization.MatrixFactorization.RawMomentExpVariation
import PaperFormalization.MatrixFactorization.TransverseVisibility

/-! # MF33: the source n and n-squared moment derivative bounds

The derivatives are those of the original moment under actual EXP pushforward.
Cauchy--Schwarz uses the original probability law, after both integrability
and differentiation exchanges have been proved.
-/
open MeasureTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Original-law Cauchy--Schwarz with no dimension-dependent loss. -/
theorem sphere_integral_norm_le_sqrt_energy {d : Nat} (mu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] (v : UnitSphere d → Weight d) (hc : Continuous v) :
    (∫ w, ‖v w‖ ∂mu) ≤ Real.sqrt (∫ w, ‖v w‖ ^ 2 ∂mu) := by
  have hi := sphere_integrable mu _ hc.norm
  have hi2 := sphere_integrable mu _ (hc.norm.pow 2)
  exact (Real.le_sqrt (integral_nonneg (fun w => norm_nonneg _))
    (integral_nonneg (fun w => sq_nonneg _))).mpr
      (probability_integral_sq_ge_sq_integral mu _ hi hi2)

/-- The pointwise full-tensor bound is integrated before using Cauchy--Schwarz. -/
theorem rawMomentAlongExpFirst_norm_le {d n : Nat} (mu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] (v : UnitSphere d → Weight d)
    (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) (t : Real) :
    ‖rawMomentAlongExpFirst n mu v t‖ ≤ (n : Real) * Real.sqrt (∫ w, ‖v w‖ ^ 2 ∂mu) := by
  have hi := (rawMomentAlongExp_integrable (n := n) mu v hv hc t).2.1
  have hn := sphere_integrable mu _ hc.norm
  calc
    ‖rawMomentAlongExpFirst n mu v t‖ ≤ ∫ w, ‖sphericalTensorFirst n w (v w) t‖ ∂mu :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ w, (n : Real) * ‖v w‖ ∂mu :=
      integral_mono hi.norm (hn.const_mul _) (fun w => sphericalTensorFirst_norm_le w (v w) (hv w) t)
    _ = (n : Real) * ∫ w, ‖v w‖ ∂mu := integral_const_mul _ _
    _ ≤ (n : Real) * Real.sqrt (∫ w, ‖v w‖ ^ 2 ∂mu) :=
      mul_le_mul_of_nonneg_left (sphere_integral_norm_le_sqrt_energy mu v hc) (Nat.cast_nonneg _)

/-- Both the off-diagonal velocity terms and radial acceleration are included. -/
theorem rawMomentAlongExpSecond_norm_le {d n : Nat} (mu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] (v : UnitSphere d → Weight d)
    (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) (t : Real) :
    ‖rawMomentAlongExpSecond n mu v t‖ ≤ (n : Real) ^ 2 * (∫ w, ‖v w‖ ^ 2 ∂mu) := by
  have hi := (rawMomentAlongExp_integrable (n := n) mu v hv hc t).2.2
  have hn := sphere_integrable mu _ (hc.norm.pow 2)
  calc
    ‖rawMomentAlongExpSecond n mu v t‖ ≤ ∫ w, ‖sphericalTensorSecond n w (v w) t‖ ∂mu :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ w, (n : Real) ^ 2 * ‖v w‖ ^ 2 ∂mu :=
      integral_mono hi.norm (hn.const_mul _) (fun w => sphericalTensorSecond_norm_le w (v w) (hv w) t)
    _ = (n : Real) ^ 2 * (∫ w, ‖v w‖ ^ 2 ∂mu) := integral_const_mul _ _

/-- Source degree factors for actual first and second derivatives, not formal jets. -/
theorem rawMomentAlongExp_derivative_bounds {d n : Nat} (mu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] (v : UnitSphere d → Weight d)
    (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) (t : Real) :
    Integrable (fun w => ‖v w‖ ^ 2) mu ∧
    ‖deriv (rawMomentAlongExp n mu v hv) t‖ ≤ (n : Real) * Real.sqrt (∫ w, ‖v w‖ ^ 2 ∂mu) ∧
    ‖deriv (deriv (rawMomentAlongExp n mu v hv)) t‖ ≤ (n : Real) ^ 2 * (∫ w, ‖v w‖ ^ 2 ∂mu) := by
  refine ⟨sphere_integrable mu _ (hc.norm.pow 2), ?_, ?_⟩
  · rw [(rawMomentAlongExp_variations mu v hv hc t).1.deriv]
    exact rawMomentAlongExpFirst_norm_le mu v hv hc t
  · rw [(rawMomentAlongExp_second_derivative mu v hv hc t).deriv]
    exact rawMomentAlongExpSecond_norm_le mu v hv hc t

end PaperFormalization.MatrixFactorization
