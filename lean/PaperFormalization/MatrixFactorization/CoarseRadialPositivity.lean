import PaperFormalization.MatrixFactorization.CoarseRadialMargin
import PaperFormalization.MatrixFactorization.AntisymmetricRadialLower

/-! # Positive actual radial pairing in an explicit sufficient neighborhood

The radius is derived from the coarse Gaussian envelope. This static conclusion
is useful for a later characteristic chain rule; no time derivative of transport
or trajectory confinement is asserted here.
-/
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Small actual transport absorbs the derived fitting error. -/
theorem antisymmetric_radial_pairing_small {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (r lambda p : Real) (hlambda : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (hsmall : productAntipodalTransportSq pole mu (reflectedMeasure mu) ≤
      coarseRadialRadius lambda p (fittingCurvatureConstant d O a/64)) :
    (lambda/2)*(productAntipodalTransportSq pole mu (reflectedMeasure mu))^(p/2) ≤
      antisymmetricRadialObjectivePairing O a pole lambda p mu teacher := by
  letI : IsProbabilityMeasure mu := hcap.probability
  let Z := productAntipodalTransportSq pole mu (reflectedMeasure mu)
  have hZ : 0 ≤ Z := add_nonneg (sphericalWassersteinSq_nonneg _ _) (sphericalWassersteinSq_nonneg _ _)
  have herr := coarse_radial_error_absorbed lambda p (fittingCurvatureConstant d O a/64) Z
    hlambda hp hp4 (div_nonneg (fittingCurvatureConstant_nonneg d O a) (by norm_num)) hZ hsmall
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

/-- Positive transport in this neighborhood has a strictly positive actual
radial pairing; empty activation and zero transport are handled separately. -/
theorem antisymmetric_radial_pairing_pos {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (r lambda p : Real) (hlambda : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (hZ : 0 < productAntipodalTransportSq pole mu (reflectedMeasure mu))
    (hsmall : productAntipodalTransportSq pole mu (reflectedMeasure mu) ≤
      coarseRadialRadius lambda p (fittingCurvatureConstant d O a/64)) :
    0 < antisymmetricRadialObjectivePairing O a pole lambda p mu teacher :=
  (mul_pos (by positivity : 0 < lambda/2) (Real.rpow_pos_of_pos hZ _)).trans_le
    (antisymmetric_radial_pairing_small O a hO pole r lambda p hlambda hp hp4 mu hcap teacher hsmall)

end PaperFormalization.MatrixFactorization
