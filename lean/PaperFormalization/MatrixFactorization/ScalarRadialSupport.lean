import Mathlib

/-! # Scalar absorption for the supported-particle radial barrier

The forcing coefficient is arbitrary and nonnegative. The exponent range
2<p<3 makes both transport powers positive, including the zero-distance case.
No statement here supplies a trajectory inequality as an assumption.
-/
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The square-root forcing splits into the metric and support-barrier powers,
with zero transport included. -/
theorem sqrt_eq_radial_powers {p Z : Real} (hp : 2 < p) (hp3 : p < 3) (hZ : 0 ≤ Z) :
    Real.sqrt Z = Z^(p/2-1)*Z^((3-p)/2) := by
  by_cases hz : Z = 0
  · simp [hz,Real.zero_rpow (by linarith : p/2-1 ≠ 0),
      Real.zero_rpow (by linarith : (3-p)/2 ≠ 0)]
  have hz : 0 < Z := lt_of_le_of_ne hZ (Ne.symm hz)
  rw [← Real.rpow_add hz,Real.sqrt_eq_rpow]
  congr 1
  ring

/-- A radius above the initial forcing ratio makes the actual scalar radial
upper bound nonpositive, without dividing by a possibly zero transport. -/
theorem radial_forcing_absorbed {C lambda p Z Z0 r : Real}
    (hC : 0 ≤ C) (hl : 0 < lambda) (hp : 2 < p) (hp3 : p < 3)
    (hZ : 0 ≤ Z) (hZ0 : Z ≤ Z0) (hr : 0 ≤ r)
    (hbarrier : C/lambda*Z0^((3-p)/2) ≤ r) :
    C*Real.sqrt Z*r-lambda*Z^(p/2-1)*r^2 ≤ 0 := by
  have hbeta : 0 ≤ (3-p)/2 := by linarith
  have hpower := Real.rpow_le_rpow hZ hZ0 hbeta
  have hratio : C*Z0^((3-p)/2) ≤ lambda*r := by
    have hh := mul_le_mul_of_nonneg_left hbarrier hl.le
    have he : lambda*(C/lambda*Z0^((3-p)/2)) = C*Z0^((3-p)/2) := by
      field_simp [ne_of_gt hl]
    rw [he] at hh
    exact hh
  have hcoeff : C*Z^((3-p)/2) ≤ lambda*r :=
    (mul_le_mul_of_nonneg_left hpower hC).trans hratio
  have hmul := mul_le_mul_of_nonneg_right hcoeff
    (mul_nonneg (Real.rpow_nonneg hZ (p/2-1)) hr)
  rw [sqrt_eq_radial_powers hp hp3 hZ]
  nlinarith

end PaperFormalization.MatrixFactorization
