import PaperFormalization.MatrixFactorization.AntisymmetricSourceRadialBound
import PaperFormalization.MatrixFactorization.AntisymmetricGradientEnergy

/-! # Actual radial and squared-gradient coercivity with the printed Cstar

The source fourth-norm coefficient is used literally. The source smallness
condition is retained directly, without replacing it by the earlier sufficient
polynomial-envelope radius. The zero-distance case is included separately.
-/
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The actual original full radial pairing has the exact source fitting
remainder coefficient and the exact transport-regularizer term. -/
theorem antisymmetricRadialObjectivePairing_lower_source {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (r lambda p : Real) (hp : 2 < p)
    (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    lambda*(productAntipodalTransportSq pole mu (reflectedMeasure mu))^(p/2) -
      sourceRadialConstant d O a teacher*
        (productAntipodalTransportSq pole mu (reflectedMeasure mu))^2 ≤
      antisymmetricRadialObjectivePairing O a pole lambda p mu teacher := by
  letI : IsProbabilityMeasure mu := hcap.probability
  let Z := productAntipodalTransportSq pole mu (reflectedMeasure mu)
  have hZ : 0 ≤ Z := add_nonneg (sphericalWassersteinSq_nonneg _ _) (sphericalWassersteinSq_nonneg _ _)
  have he : Z^(p/2-1)*Z = Z^(p/2) := by
    by_cases hz : Z = 0
    · simp [hz,Real.zero_rpow (show p/2 ≠ 0 by linarith)]
    have hz : 0 < Z := lt_of_le_of_ne hZ (Ne.symm hz)
    calc
      Z^(p/2-1)*Z = Z^(p/2-1)*Z^(1:Real) := by rw [Real.rpow_one]
      _ = Z^((p/2-1)+1) := (Real.rpow_add hz _ _).symm
      _ = Z^(p/2) := by congr 1; ring
  rw [antisymmetricRadialObjectivePairing_split O a pole r lambda p mu hcap teacher]
  change lambda*Z^(p/2)-sourceRadialConstant d O a teacher*Z^2 ≤
    antisymmetricRadialFittingPairing O a pole mu teacher + lambda*Z^(p/2-1)*Z
  rw [mul_assoc,he]
  linarith [antisymmetricRadialFittingPairing_lower_source O a hO pole r mu hcap teacher]

/-- The printed closed source threshold absorbs the actual fitting error.
No coarse-radius or strict initial-smallness substitution is made. -/
theorem antisymmetric_radial_pairing_source {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (r lambda p : Real) (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (hsmall : sourceRadialConstant d O a teacher*
      (productAntipodalTransportSq pole mu (reflectedMeasure mu))^((4-p)/2) ≤ lambda/2) :
    (lambda/2)*(productAntipodalTransportSq pole mu (reflectedMeasure mu))^(p/2) ≤
      antisymmetricRadialObjectivePairing O a pole lambda p mu teacher := by
  letI : IsProbabilityMeasure mu := hcap.probability
  let Z := productAntipodalTransportSq pole mu (reflectedMeasure mu)
  have hZ : 0 ≤ Z := add_nonneg (sphericalWassersteinSq_nonneg _ _) (sphericalWassersteinSq_nonneg _ _)
  have he : Z^2 = Z^((4-p)/2)*Z^(p/2) := by
    by_cases hz : Z = 0
    · simp [hz,Real.zero_rpow (show (4-p)/2 ≠ 0 by linarith)]
    have hz : 0 < Z := lt_of_le_of_ne hZ (Ne.symm hz)
    rw [← Real.rpow_add hz]
    have hs : (4-p)/2+p/2 = (2 : Real) := by ring
    rw [hs,Real.rpow_two]
  have herr : sourceRadialConstant d O a teacher*Z^2 ≤ (lambda/2)*Z^(p/2) := by
    rw [he,← mul_assoc]
    exact mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hZ _)
  have hb := antisymmetricRadialObjectivePairing_lower_source O a hO pole r lambda p hp mu hcap teacher
  change lambda*Z^(p/2)-sourceRadialConstant d O a teacher*Z^2 ≤ _ at hb
  change (lambda/2)*Z^(p/2) ≤ _
  linarith

/-- Cauchy--Schwarz with the true radial transport energy yields the source
squared-gradient lower bound, including zero transport without cancellation. -/
theorem antisymmetricGradientEnergy_lower_source {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (r lambda p : Real) (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (hsmall : sourceRadialConstant d O a teacher*
      (productAntipodalTransportSq pole mu (reflectedMeasure mu))^((4-p)/2) ≤ lambda/2) :
    (lambda^2/4)*(productAntipodalTransportSq pole mu (reflectedMeasure mu))^(p-1) ≤
      antisymmetricGradientEnergy O a pole lambda p mu teacher := by
  letI : IsProbabilityMeasure mu := hcap.probability
  let Z := productAntipodalTransportSq pole mu (reflectedMeasure mu)
  have hZ : 0 ≤ Z := add_nonneg (sphericalWassersteinSq_nonneg _ _) (sphericalWassersteinSq_nonneg _ _)
  change (lambda^2/4)*Z^(p-1) ≤ _
  by_cases hz : Z = 0
  · rw [hz,Real.zero_rpow (show p-1 ≠ 0 by linarith),mul_zero]
    exact antisymmetricGradientEnergy_nonneg O a pole lambda p mu teacher
  have hz : 0 < Z := lt_of_le_of_ne hZ (Ne.symm hz)
  have hb := antisymmetric_radial_pairing_source O a hO pole r lambda p hl hp hp4 mu hcap teacher hsmall
  have hbn : 0 ≤ lambda/2*Z^(p/2) := mul_nonneg (by positivity) (Real.rpow_nonneg hZ _)
  have hs := pow_le_pow_left₀ hbn hb 2
  have hc := antisymmetricGradientEnergy_radial_sq O a pole r lambda p mu hcap teacher
  have he : ((lambda/2)*Z^(p/2))^2 = ((lambda^2/4)*Z^(p-1))*Z := by
    have hpow : (Z^(p/2))^2 = Z^p := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hZ]
      congr 1
      norm_num
    have hprod : Z^(p-1)*Z = Z^p := by
      calc
        Z^(p-1)*Z = Z^(p-1)*Z^(1:Real) := by rw [Real.rpow_one]
        _ = Z^((p-1)+1) := (Real.rpow_add hz _ _).symm
        _ = Z^p := by congr 1; ring
    rw [mul_pow,hpow]
    calc
      _ = (lambda^2/4)*Z^p := by ring
      _ = _ := by rw [← hprod]; ring
  rw [he] at hs
  have hfinal := hs.trans hc
  nlinarith

end PaperFormalization.MatrixFactorization
