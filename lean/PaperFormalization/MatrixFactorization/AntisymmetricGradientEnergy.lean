import PaperFormalization.MatrixFactorization.CoarseRadialPositivity
import PaperFormalization.MatrixFactorization.SphericalRadialCauchy

/-! # Actual squared-gradient coercivity in the coarse radial neighborhood

The squared norm is integrated over both original branch marginals. The
estimate is static: no time differentiation or trajectory existence is assumed.
The radius remains the explicit polynomial-envelope radius, rather than the
sharper coefficient printed in the manuscript.
-/
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def antisymmetricGradientEnergy {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (lambda p : Real)
    (mu teacher : Measure (UnitSphere d)) : Real :=
  (∫ w, norm (sphericalObjectiveGradient O a pole lambda p mu (reflectedMeasure mu)
    teacher teacher 0 w)^2 ∂mu) +
  (∫ w, norm (sphericalObjectiveGradient O a pole lambda p mu (reflectedMeasure mu)
    teacher teacher 1 w)^2 ∂reflectedMeasure mu)

theorem antisymmetricGradientEnergy_nonneg {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (lambda p : Real)
    (mu teacher : Measure (UnitSphere d)) :
    0 ≤ antisymmetricGradientEnergy O a pole lambda p mu teacher :=
  add_nonneg (integral_nonneg (fun _ => sq_nonneg _))
    (integral_nonneg (fun _ => sq_nonneg _))

/-- Cauchy--Schwarz uses the exact original spherical transport as radial energy. -/
theorem antisymmetricGradientEnergy_radial_sq {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (r lambda p : Real)
    (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    (antisymmetricRadialObjectivePairing O a pole lambda p mu teacher)^2 ≤
      antisymmetricGradientEnergy O a pole lambda p mu teacher *
        productAntipodalTransportSq pole mu (reflectedMeasure mu) := by
  let nu : Fin 2 → Measure (UnitSphere d) := ![mu, reflectedMeasure mu]
  have hc : ∀ i, TwoCapClass pole r (nu i) := by
    intro i
    fin_cases i
    · exact hcap
    · exact hcap.reflected
  simpa only [nu, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    antisymmetricRadialObjectivePairing, antisymmetricGradientEnergy] using
    objective_radial_pairing_sq_le_gradient_energy O a pole r lambda p nu hc teacher teacher

/-- The actual full squared gradient controls transport to power p minus one.
The zero-distance case is included without dividing by zero. -/
theorem antisymmetricGradientEnergy_lower {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (r lambda p : Real) (hlambda : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (hsmall : productAntipodalTransportSq pole mu (reflectedMeasure mu) ≤
      coarseRadialRadius lambda p (fittingCurvatureConstant d O a/64)) :
    (lambda^2/4)*(productAntipodalTransportSq pole mu (reflectedMeasure mu))^(p-1) ≤
      antisymmetricGradientEnergy O a pole lambda p mu teacher := by
  letI : IsProbabilityMeasure mu := hcap.probability
  let Z := productAntipodalTransportSq pole mu (reflectedMeasure mu)
  have hZ : 0 ≤ Z := add_nonneg (sphericalWassersteinSq_nonneg _ _) (sphericalWassersteinSq_nonneg _ _)
  change (lambda^2/4)*Z^(p-1) ≤ _
  by_cases hz : Z = 0
  · rw [hz, Real.zero_rpow (show p-1 ≠ 0 by linarith), mul_zero]
    exact antisymmetricGradientEnergy_nonneg O a pole lambda p mu teacher
  have hz : 0 < Z := lt_of_le_of_ne hZ (Ne.symm hz)
  have hb := antisymmetric_radial_pairing_small O a hO pole r lambda p
    hlambda hp hp4 mu hcap teacher hsmall
  have hbn : 0 ≤ lambda/2*Z^(p/2) := mul_nonneg (by positivity) (Real.rpow_nonneg hZ _)
  have hs := pow_le_pow_left₀ hbn hb 2
  have hc := antisymmetricGradientEnergy_radial_sq O a pole r lambda p mu hcap teacher
  have he : ((lambda/2)*Z^(p/2))^2 = ((lambda^2/4)*Z^(p-1))*Z := by
    have hpow : (Z^(p/2))^2 = Z^p := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hZ]
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
