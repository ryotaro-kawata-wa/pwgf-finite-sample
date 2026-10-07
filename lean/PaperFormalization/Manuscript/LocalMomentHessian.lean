import PaperFormalization.Manuscript.MomentGradientField
import Mathlib.Tactic

/-! # Local comparison bounds for the actual moment-gradient construction

All norms below are Hilbert and operator norms, without dimension factors.
The signed field is the existing negative gradient field; the two Hessian
blocks are its existing positive blocks. Primitive derivative norm and
difference estimates are explicit inputs to the source constant corollaries.
-/

namespace PaperFormalization.Manuscript

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Adjoint evaluation preserves the operator norm. -/
theorem norm_adjoint_apply_le (A : E →L[ℝ] H) (g : H) :
    ‖A.adjoint g‖ ≤ ‖A‖ * ‖g‖ := by
  simpa only [LinearIsometryEquiv.norm_map] using A.adjoint.le_opNorm g

/-- Magnitude of the actual signed gradient field. -/
theorem norm_momentGradientField_le (dφ : E → E →L[ℝ] H) (gradG : H → H)
    (theta : H) (x : E) :
    ‖momentGradientField dφ gradG (theta, x)‖ ≤ ‖dφ x‖ * ‖gradG theta‖ := by
  simpa only [momentGradientField, norm_neg] using norm_adjoint_apply_le (dφ x) (gradG theta)

/-- Magnitude of the constructed spatial Hessian. -/
theorem norm_momentSpatialHessian_le (ddφ : E →L[ℝ] (E →L[ℝ] H)) (g : H) :
    ‖momentSpatialHessian ddφ g‖ ≤ ‖ddφ‖ * ‖g‖ := by
  apply (momentSpatialHessian ddφ g).opNorm_le_bound (mul_nonneg (norm_nonneg ddφ) (norm_nonneg g))
  intro v
  change ‖(ddφ v).adjoint g‖ ≤ _
  calc
    _ ≤ ‖ddφ v‖ * ‖g‖ := norm_adjoint_apply_le _ _
    _ ≤ (‖ddφ‖ * ‖v‖) * ‖g‖ := mul_le_mul_of_nonneg_right (ddφ.le_opNorm v) (norm_nonneg _)
    _ = (‖ddφ‖ * ‖g‖) * ‖v‖ := by ring

/-- Magnitude of the two-point Hessian, keeping both feature factors. -/
theorem norm_momentIntegralHessian_le (A C : E →L[ℝ] H) (B : H →L[ℝ] H) :
    ‖momentIntegralHessian A C B‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ := by
  calc
    _ ≤ ‖A.adjoint‖ * ‖B.comp C‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A‖ * (‖B‖ * ‖C‖) := by
      simpa only [LinearIsometryEquiv.norm_map] using
        mul_le_mul_of_nonneg_left (B.opNorm_comp_le C) (norm_nonneg A.adjoint)
    _ = _ := by ring

/-- The measure slot of the actual signed field. -/
theorem norm_momentGradientField_sub_measure_le
    (dφ : E → E →L[ℝ] H) (gradG : H → H) (theta theta' : H) (x : E) :
    ‖momentGradientField dφ gradG (theta, x) - momentGradientField dφ gradG (theta', x)‖ ≤
      ‖dφ x‖ * ‖gradG theta - gradG theta'‖ := by
  have heq : momentGradientField dφ gradG (theta, x) - momentGradientField dφ gradG (theta', x) =
      -(dφ x).adjoint (gradG theta - gradG theta') := by
    simp [momentGradientField, sub_eq_add_neg, add_comm]
  rw [heq, norm_neg]
  exact norm_adjoint_apply_le _ _

/-- The spatial slot of the actual signed field. -/
theorem norm_momentGradientField_sub_spatial_le
    (dφ : E → E →L[ℝ] H) (gradG : H → H) (theta : H) (x x' : E) :
    ‖momentGradientField dφ gradG (theta, x) - momentGradientField dφ gradG (theta, x')‖ ≤
      ‖dφ x - dφ x'‖ * ‖gradG theta‖ := by
  have heq : momentGradientField dφ gradG (theta, x) - momentGradientField dφ gradG (theta, x') =
      -(dφ x - dφ x').adjoint (gradG theta) := by
    simp [momentGradientField, sub_eq_add_neg, add_comm]
  rw [heq, norm_neg]
  exact norm_adjoint_apply_le _ _

/-- The measure slot of the constructed spatial Hessian. -/
theorem norm_momentSpatialHessian_sub_measure_le
    (ddφ : E →L[ℝ] (E →L[ℝ] H)) (g g' : H) :
    ‖momentSpatialHessian ddφ g - momentSpatialHessian ddφ g'‖ ≤ ‖ddφ‖ * ‖g - g'‖ := by
  have heq : momentSpatialHessian ddφ g - momentSpatialHessian ddφ g' =
      momentSpatialHessian ddφ (g - g') := by
    ext v
    simp [momentSpatialHessian]
  rw [heq]
  exact norm_momentSpatialHessian_le _ _

/-- The spatial slot of the constructed spatial Hessian. -/
theorem norm_momentSpatialHessian_sub_spatial_le
    (ddφ ddφ' : E →L[ℝ] (E →L[ℝ] H)) (g : H) :
    ‖momentSpatialHessian ddφ g - momentSpatialHessian ddφ' g‖ ≤ ‖ddφ - ddφ'‖ * ‖g‖ := by
  have heq : momentSpatialHessian ddφ g - momentSpatialHessian ddφ' g =
      momentSpatialHessian (ddφ - ddφ') g := by
    ext v
    simp [momentSpatialHessian]
  rw [heq]
  exact norm_momentSpatialHessian_le _ _

/-- The measure slot of the actual two-point Hessian. -/
theorem norm_momentIntegralHessian_sub_measure_le
    (A C : E →L[ℝ] H) (B B' : H →L[ℝ] H) :
    ‖momentIntegralHessian A C B - momentIntegralHessian A C B'‖ ≤
      ‖A‖ * ‖B - B'‖ * ‖C‖ := by
  have heq : momentIntegralHessian A C B - momentIntegralHessian A C B' =
      momentIntegralHessian A C (B - B') := by
    ext v
    simp [momentIntegralHessian]
  rw [heq]
  exact norm_momentIntegralHessian_le _ _ _

/-- Change the two spatial slots separately, preserving their distinct factors. -/
theorem norm_momentIntegralHessian_sub_spatial_le
    (A A' C C' : E →L[ℝ] H) (B : H →L[ℝ] H) :
    ‖momentIntegralHessian A C B - momentIntegralHessian A' C' B‖ ≤
      ‖A - A'‖ * ‖B‖ * ‖C‖ + ‖A'‖ * ‖B‖ * ‖C - C'‖ := by
  have heq : momentIntegralHessian A C B - momentIntegralHessian A' C' B =
      momentIntegralHessian (A - A') C B + momentIntegralHessian A' (C - C') B := by
    ext v
    simp [momentIntegralHessian, map_sub]
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_momentIntegralHessian_le _ _ _) (norm_momentIntegralHessian_le _ _ _))

/-- The source constant leaves enough room for two measure-Hessian errors. -/
theorem local_moment_constant_domination (Q R : ℝ) (hQ : 0 ≤ Q) (hR : 1 ≤ R) :
    Q * R ^ 2 ≤ (4 * Q * R ^ 3) / 2 ∧ Q * R ^ 3 ≤ 4 * Q * R ^ 3 := by
  have hR0 : 0 ≤ R := by linarith
  have hpow : R ^ 2 ≤ R ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg R) (sub_nonneg.mpr hR)]
  have hQR : 0 ≤ Q * R ^ 3 := mul_nonneg hQ (pow_nonneg hR0 _)
  have hle := mul_le_mul_of_nonneg_left hpow hQ
  constructor <;> nlinarith

/-- The three actual magnitudes are bounded by the source's common 4 Q R^3. -/
theorem source_moment_magnitude_bounds
    (dφ : E → E →L[ℝ] H) (gradG : H → H) (theta : H) (x y : E)
    (ddφ : E →L[ℝ] (E →L[ℝ] H)) (B : H →L[ℝ] H)
    (Q R : ℝ) (hQ : 1 ≤ Q) (hR : 1 ≤ R)
    (hx : ‖dφ x‖ ≤ R) (hy : ‖dφ y‖ ≤ R) (hdd : ‖ddφ‖ ≤ R)
    (hg : ‖gradG theta‖ ≤ Q * R ^ 2) (hB : ‖B‖ ≤ Q * R) :
    ‖momentGradientField dφ gradG (theta, x)‖ ≤ 4 * Q * R ^ 3 ∧
    ‖momentSpatialHessian ddφ (gradG theta)‖ ≤ 4 * Q * R ^ 3 ∧
    ‖momentIntegralHessian (dφ x) (dφ y) B‖ ≤ 4 * Q * R ^ 3 := by
  have hQ0 : 0 ≤ Q := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hc := (local_moment_constant_domination Q R hQ0 hR).2
  constructor
  · calc
      _ ≤ ‖dφ x‖ * ‖gradG theta‖ := norm_momentGradientField_le _ _ _ _
      _ ≤ R * (Q * R ^ 2) := by gcongr
      _ = Q * R ^ 3 := by ring
      _ ≤ _ := hc
  constructor
  · calc
      _ ≤ ‖ddφ‖ * ‖gradG theta‖ := norm_momentSpatialHessian_le _ _
      _ ≤ R * (Q * R ^ 2) := by gcongr
      _ = Q * R ^ 3 := by ring
      _ ≤ _ := hc
  · calc
      _ ≤ ‖dφ x‖ * ‖B‖ * ‖dφ y‖ := norm_momentIntegralHessian_le _ _ _
      _ ≤ R * (Q * R) * R := by gcongr
      _ = Q * R ^ 3 := by ring
      _ ≤ _ := hc

/-- Primitive moment-gradient/Hessian differences give the exact common
measure bounds; the spatial and integral Hessians each use only L/2.
S may be the weighted coordinate moment discrepancy, with its norm bound
supplied by the separately constructed weighted feature space. -/
theorem source_moment_measure_bounds
    (dφ : E → E →L[ℝ] H) (gradG : H → H) (theta theta' : H) (x y : E)
    (ddφ : E →L[ℝ] (E →L[ℝ] H)) (B B' : H →L[ℝ] H)
    (Q R S : ℝ) (hQ : 1 ≤ Q) (hR : 1 ≤ R)
    (hx : ‖dφ x‖ ≤ R) (hy : ‖dφ y‖ ≤ R) (hdd : ‖ddφ‖ ≤ R)
    (hdelta : ‖theta - theta'‖ ≤ S)
    (hg : ‖gradG theta - gradG theta'‖ ≤ Q * R * ‖theta - theta'‖)
    (hB : ‖B - B'‖ ≤ Q * ‖theta - theta'‖) :
    ‖momentGradientField dφ gradG (theta, x) - momentGradientField dφ gradG (theta', x)‖ ≤
        (4 * Q * R ^ 3) * S ∧
    ‖momentSpatialHessian ddφ (gradG theta) - momentSpatialHessian ddφ (gradG theta')‖ ≤
        ((4 * Q * R ^ 3) / 2) * S ∧
    ‖momentIntegralHessian (dφ x) (dφ y) B - momentIntegralHessian (dφ x) (dφ y) B'‖ ≤
        ((4 * Q * R ^ 3) / 2) * S := by
  have hQ0 : 0 ≤ Q := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hS : 0 ≤ S := (norm_nonneg _).trans hdelta
  have hgS : ‖gradG theta - gradG theta'‖ ≤ Q * R * S :=
    hg.trans (mul_le_mul_of_nonneg_left hdelta (mul_nonneg hQ0 hR0))
  have hBS : ‖B - B'‖ ≤ Q * S :=
    hB.trans (mul_le_mul_of_nonneg_left hdelta hQ0)
  have hc := (local_moment_constant_domination Q R hQ0 hR).1
  have hcS := mul_le_mul_of_nonneg_right hc hS
  have hfull : Q * R ^ 2 * S ≤ (4 * Q * R ^ 3) * S := by
    have hconst : 0 ≤ 4 * Q * R ^ 3 := by positivity
    nlinarith [mul_nonneg hconst hS]
  constructor
  · calc
      _ ≤ ‖dφ x‖ * ‖gradG theta - gradG theta'‖ := norm_momentGradientField_sub_measure_le _ _ _ _ _
      _ ≤ R * (Q * R * S) := by gcongr
      _ = Q * R ^ 2 * S := by ring
      _ ≤ _ := hfull
  constructor
  · calc
      _ ≤ ‖ddφ‖ * ‖gradG theta - gradG theta'‖ := norm_momentSpatialHessian_sub_measure_le _ _ _
      _ ≤ R * (Q * R * S) := by gcongr
      _ = Q * R ^ 2 * S := by ring
      _ ≤ _ := hcS
  · calc
      _ ≤ ‖dφ x‖ * ‖B - B'‖ * ‖dφ y‖ := norm_momentIntegralHessian_sub_measure_le _ _ _ _
      _ ≤ R * (Q * S) * R := by gcongr
      _ = Q * R ^ 2 * S := by ring
      _ ≤ _ := hcS

/-- Primitive spatial differences give the common spatial Lipschitz bounds.
The integral Hessian changes one point slot at a time, with no extra factor. -/
theorem source_moment_spatial_bounds
    (dφ : E → E →L[ℝ] H) (gradG : H → H) (theta : H) (x x' y y' : E)
    (ddφ ddφ' : E →L[ℝ] (E →L[ℝ] H)) (B : H →L[ℝ] H)
    (Q R : ℝ) (hQ : 1 ≤ Q) (hR : 1 ≤ R)
    (hx' : ‖dφ x'‖ ≤ R) (hy : ‖dφ y‖ ≤ R)
    (hxdiff : ‖dφ x - dφ x'‖ ≤ R * ‖x - x'‖)
    (hydiff : ‖dφ y - dφ y'‖ ≤ R * ‖y - y'‖)
    (hdddiff : ‖ddφ - ddφ'‖ ≤ R * ‖x - x'‖)
    (hg : ‖gradG theta‖ ≤ Q * R ^ 2) (hB : ‖B‖ ≤ Q * R) :
    ‖momentGradientField dφ gradG (theta, x) - momentGradientField dφ gradG (theta, x')‖ ≤
        (4 * Q * R ^ 3) * ‖x - x'‖ ∧
    ‖momentSpatialHessian ddφ (gradG theta) - momentSpatialHessian ddφ' (gradG theta)‖ ≤
        (4 * Q * R ^ 3) * ‖x - x'‖ ∧
    ‖momentIntegralHessian (dφ x) (dφ y) B - momentIntegralHessian (dφ x') (dφ y') B‖ ≤
        (4 * Q * R ^ 3) * (‖x - x'‖ + ‖y - y'‖) := by
  have hQ0 : 0 ≤ Q := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hc := (local_moment_constant_domination Q R hQ0 hR).2
  constructor
  · calc
      _ ≤ ‖dφ x - dφ x'‖ * ‖gradG theta‖ := norm_momentGradientField_sub_spatial_le _ _ _ _ _
      _ ≤ (R * ‖x - x'‖) * (Q * R ^ 2) := by gcongr
      _ = (Q * R ^ 3) * ‖x - x'‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
  constructor
  · calc
      _ ≤ ‖ddφ - ddφ'‖ * ‖gradG theta‖ := norm_momentSpatialHessian_sub_spatial_le _ _ _
      _ ≤ (R * ‖x - x'‖) * (Q * R ^ 2) := by gcongr
      _ = (Q * R ^ 3) * ‖x - x'‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
  · calc
      _ ≤ ‖dφ x - dφ x'‖ * ‖B‖ * ‖dφ y‖ + ‖dφ x'‖ * ‖B‖ * ‖dφ y - dφ y'‖ :=
        norm_momentIntegralHessian_sub_spatial_le _ _ _ _ _
      _ ≤ (R * ‖x - x'‖) * (Q * R) * R + R * (Q * R) * (R * ‖y - y'‖) := by gcongr
      _ = (Q * R ^ 3) * (‖x - x'‖ + ‖y - y'‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (add_nonneg (norm_nonneg _) (norm_nonneg _))

end PaperFormalization.Manuscript
