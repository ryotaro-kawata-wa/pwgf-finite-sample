import PaperFormalization.MatrixFactorization.CoarseRadialPositivity

/-! # MF15: an outer nonincrease margin for the existing closed initial radius

The established coarseRadialRadius is NOT changed.
A strictly larger auxiliary bound is used only in a first-exit argument.
Consequently initial equality at the original radius is retained. These
coarse Gaussian-envelope radii are not the manuscript's sharp Cstar basin.
-/
open MeasureTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def radialOuterRadius (lambda p C : Real) : Real :=
  (lambda/(C+1))^(1/(2-p/2))

theorem radialOuterRadius_pos (lambda p C : Real) (hl : 0 < lambda) (hC : 0 ≤ C) :
    0 < radialOuterRadius lambda p C :=
  Real.rpow_pos_of_pos (div_pos hl (by positivity)) _

theorem coarseRadialRadius_lt_outer (lambda p C : Real)
    (hl : 0 < lambda) (hC : 0 ≤ C) (hp4 : p < 4) :
    coarseRadialRadius lambda p C < radialOuterRadius lambda p C := by
  have hq : 0 < 2-p/2 := by linarith
  have hbase : lambda/(2*(C+1)) < lambda/(C+1) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  exact (min_le_right _ _).trans_lt
    (Real.rpow_lt_rpow (by positivity) hbase (by positivity : 0 < 1/(2-p/2)))

/-- The outer region absorbs the fitting error with the entire metric term.
It is used only for nonincrease; the stronger half-margin is reused after
persistence inside the original coarse radius has been proved. -/
theorem radial_outer_error_absorbed (lambda p C Z : Real)
    (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4) (hC : 0 ≤ C)
    (hZ : 0 ≤ Z) (hsmall : Z ≤ radialOuterRadius lambda p C) :
    C*Z^2 ≤ lambda*Z^(p/2) := by
  by_cases hz : Z = 0
  · simp [hz,Real.zero_rpow (show p/2 ≠ 0 by linarith)]
  have hz : 0 < Z := lt_of_le_of_ne hZ (Ne.symm hz)
  let q : Real := 2-p/2
  have hq : 0 < q := by dsimp [q]; linarith
  have hbase : 0 < lambda/(C+1) := by positivity
  have hpower : Z^q ≤ lambda/(C+1) := by
    have hh := Real.rpow_le_rpow hZ hsmall hq.le
    have he : ((lambda/(C+1))^(1/q))^q = lambda/(C+1) := by
      rw [← Real.rpow_mul hbase.le]
      have hqq : (1/q)*q = 1 := by field_simp [ne_of_gt hq]
      rw [hqq,Real.rpow_one]
    exact hh.trans_eq he
  have hCb : C*(lambda/(C+1)) ≤ lambda := by
    have hh : C/(C+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    have he : C*(lambda/(C+1)) = lambda*(C/(C+1)) := by ring
    rw [he]
    nlinarith
  have hcoef := (mul_le_mul_of_nonneg_left hpower hC).trans hCb
  have he : Z^2 = Z^q*Z^(p/2) := by
    rw [← Real.rpow_add hz]
    have hsum : q+p/2 = 2 := by dsimp [q]; ring
    rw [hsum,Real.rpow_two]
  rw [he,← mul_assoc]
  exact mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hZ _)

/-- Source radial pairing is nonnegative throughout the larger auxiliary region. -/
theorem antisymmetric_radial_pairing_outer_nonneg {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (r lambda p : Real) (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (hsmall : productAntipodalTransportSq pole mu (reflectedMeasure mu) ≤
      radialOuterRadius lambda p (fittingCurvatureConstant d O a/64)) :
    0 ≤ antisymmetricRadialObjectivePairing O a pole lambda p mu teacher := by
  letI : IsProbabilityMeasure mu := hcap.probability
  let Z := productAntipodalTransportSq pole mu (reflectedMeasure mu)
  have hZ : 0 ≤ Z := add_nonneg (sphericalWassersteinSq_nonneg _ _) (sphericalWassersteinSq_nonneg _ _)
  have herr := radial_outer_error_absorbed lambda p (fittingCurvatureConstant d O a/64) Z
    hl hp hp4 (div_nonneg (fittingCurvatureConstant_nonneg d O a) (by norm_num)) hZ hsmall
  have he : Z^(p/2-1)*Z = Z^(p/2) := by
    by_cases hz : Z = 0
    · simp [hz,Real.zero_rpow (show p/2 ≠ 0 by linarith)]
    have hz : 0 < Z := lt_of_le_of_ne hZ (Ne.symm hz)
    calc
      Z^(p/2-1)*Z = Z^(p/2-1)*Z^(1:Real) := by rw [Real.rpow_one]
      _ = Z^((p/2-1)+1) := (Real.rpow_add hz _ _).symm
      _ = Z^(p/2) := by congr 1; ring
  have hb := antisymmetricRadialObjectivePairing_lower O a hO pole r lambda p mu hcap teacher
  change lambda*Z^(p/2-1)*Z - _ ≤ _ at hb
  rw [mul_assoc,he] at hb
  linarith

end PaperFormalization.MatrixFactorization
