import PaperFormalization.MatrixFactorization.SphericalRadialPairing

/-! # An explicit sufficient radius for absorbing the coarse radial error

This radius belongs to the polynomial-envelope estimate. It is not identified
with the manuscript's sharper active-block radius or its confinement radius.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def coarseRadialRadius (lambda p C : Real) : Real :=
  min 1 ((lambda / (2*(C+1))) ^ (1/(2-p/2)))

theorem coarseRadialRadius_pos (lambda p C : Real) (hlambda : 0 < lambda) (hC : 0 ≤ C) :
    0 < coarseRadialRadius lambda p C :=
  lt_min zero_lt_one (Real.rpow_pos_of_pos (div_pos hlambda (by positivity)) _)

/-- The power comparison includes zero transport and the closed radius endpoint. -/
theorem coarse_radial_error_absorbed (lambda p C Z : Real)
    (hlambda : 0 < lambda) (hp : 2 < p) (hp4 : p < 4) (hC : 0 ≤ C)
    (hZ : 0 ≤ Z) (hsmall : Z ≤ coarseRadialRadius lambda p C) :
    C * Z^2 ≤ (lambda/2) * Z^(p/2) := by
  by_cases hz : Z = 0
  · subst Z
    simp [Real.zero_rpow (show p/2 ≠ 0 by linarith)]
  have hz : 0 < Z := lt_of_le_of_ne hZ (Ne.symm hz)
  let alpha := 2-p/2
  have ha : 0 < alpha := by dsimp [alpha]; linarith
  let b := lambda / (2*(C+1))
  have hb : 0 < b := div_pos hlambda (by positivity)
  have hbound : Z^alpha ≤ b := by
    have hzle : Z ≤ b^(1/alpha) := hsmall.trans (min_le_right _ _)
    have hh := Real.rpow_le_rpow hZ hzle ha.le
    have he : (b^(1/alpha))^alpha = b := by
      rw [← Real.rpow_mul hb.le]
      have haa : (1/alpha)*alpha = 1 := by field_simp
      rw [haa,Real.rpow_one]
    exact hh.trans_eq he
  have hCb : C*b ≤ lambda/2 := by
    have hle : C/(C+1) ≤ 1 := (div_le_one (by positivity : 0 < C+1)).mpr (by linarith)
    have he : C*b = (lambda/2)*(C/(C+1)) := by
      dsimp [b]
      field_simp
    rw [he]
    nlinarith
  have hcoef : C * Z^alpha ≤ lambda/2 :=
    (mul_le_mul_of_nonneg_left hbound hC).trans hCb
  have he : Z^2 = Z^alpha * Z^(p/2) := by
    rw [← Real.rpow_add hz]
    have hae : alpha + p/2 = 2 := by dsimp [alpha]; ring
    rw [hae,Real.rpow_two]
  rw [he,← mul_assoc]
  exact mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hZ _)

end PaperFormalization.MatrixFactorization
