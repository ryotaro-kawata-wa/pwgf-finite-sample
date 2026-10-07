import PaperFormalization.MatrixFactorization.CoarseRadialMargin

/-! # Scalar margins for the coarse support barrier

The fitting constant in this file is the actual finite polynomial-envelope
constant. It is not identified with the manuscript's sharp L4 fitting constant.
-/
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- A positive sufficient bound on squared product transport for both the
mean-distance estimate and the coarse support margin. -/
noncomputable def coarseSupportBasin (lambda p C r : Real) : Real :=
  min (coarseRadialRadius lambda p (C/64))
    ((lambda*r/(2*(C+1)))^(1/((3-p)/2)))

theorem coarseSupportBasin_pos (lambda p C r : Real)
    (hl : 0 < lambda) (hC : 0 ≤ C) (hr : 0 < r) :
    0 < coarseSupportBasin lambda p C r := by
  apply lt_min (coarseRadialRadius_pos lambda p (C/64) hl (by positivity))
  exact Real.rpow_pos_of_pos (div_pos (mul_pos hl hr) (by positivity)) _

/-- The same sufficient initial squared-distance bound leaves half of the
cap radius for the fitting force, with the closed endpoint retained. -/
theorem coarseSupportBasin_bounds (lambda p C r Z0 : Real)
    (hl : 0 < lambda) (hp3 : p < 3) (hC : 0 ≤ C) (hr : 0 < r)
    (hZ0 : 0 ≤ Z0) (hs : Z0 ≤ coarseSupportBasin lambda p C r) :
    Z0 ≤ coarseRadialRadius lambda p (C/64) ∧
      (C/lambda)*Z0^((3-p)/2) ≤ r/2 := by
  refine ⟨hs.trans (min_le_left _ _),?_⟩
  let beta := (3-p)/2
  have hb : 0 < beta := by dsimp [beta]; linarith
  let b := lambda*r/(2*(C+1))
  have hpos : 0 < b := div_pos (mul_pos hl hr) (by positivity)
  have hz : Z0^beta ≤ b := by
    have hzle : Z0 ≤ b^(1/beta) := hs.trans (min_le_right _ _)
    have hh := Real.rpow_le_rpow hZ0 hzle hb.le
    have he : (b^(1/beta))^beta = b := by
      rw [← Real.rpow_mul hpos.le]
      have hbe : (1/beta)*beta = 1 := by field_simp
      rw [hbe,Real.rpow_one]
    exact hh.trans_eq he
  have hcoef : (C/lambda)*b ≤ r/2 := by
    have he : (C/lambda)*b = (r/2)*(C/(C+1)) := by dsimp [b]; field_simp
    rw [he]
    have hc : C/(C+1) ≤ 1 := (div_le_one (by positivity : 0 < C+1)).mpr (by linarith)
    nlinarith
  exact (mul_le_mul_of_nonneg_left hz (div_nonneg hC hl.le)).trans hcoef

end PaperFormalization.MatrixFactorization
