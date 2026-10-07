import PaperFormalization.MatrixFactorization.ActiveFittingAnnulus
open MeasureTheory
open PaperFormalization.MatrixFactorization
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

-- Empty active sets and a radius-zero ball are retained in the concrete constant.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (teacher : Measure (UnitSphere d)) [IsFiniteMeasure teacher] :
    0 ≤ activeGaussianFitCurvatureConstant O a teacher 0 :=
  activeGaussianFitCurvatureConstant_nonneg O a teacher 0 le_rfl
example {d h : Nat} (a : Nat → Weight h) (teacher : Measure (UnitSphere d))
    [IsFiniteMeasure teacher] (R : Real) : activeGaussianFitCurvatureConstant ∅ a teacher R = 0 := by
  simp [activeGaussianFitCurvatureConstant, activeC2CurvatureConstant]

-- The actual polynomial identity covers negative time and finite non-probability teachers.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher : Measure (UnitSphere d)) [IsFiniteMeasure teacher] :
    activeFittingPolynomial O a (rawActiveMoment O teacher)
      (activeMomentMapAlongRetract O P.measure P.velocity P.tangent (-1)) =
      variationRetractedFitting O a P teacher teacher (-1) :=
  activeFittingPolynomial_along_retract O a P teacher (-1)

-- Closed active-radius equality is allowed, and the velocity has no branch constraint.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher : Measure (UnitSphere d)) [IsFiniteMeasure teacher] (A : ActiveMomentSpace d O)
    (hbase : activeMomentMap O (P.measure 0) (P.measure 1) = activeAntisymmetricPoint A) :
    -(activeGaussianFitCurvatureConstant O a teacher ‖A‖) * variationEnergy P ≤
      deriv (deriv (variationRetractedFitting O a P teacher teacher)) 0 :=
  spherical_retraction_actual_fit_curvature O a P teacher ‖A‖ A hbase le_rfl

-- Zero product tangent energy is retained in the non-strict second-variation bound.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher : Measure (UnitSphere d)) [IsFiniteMeasure teacher] (A : ActiveMomentSpace d O)
    (hbase : activeMomentMap O (P.measure 0) (P.measure 1) = activeAntisymmetricPoint A)
    (hE : variationEnergy P = 0) :
    0 ≤ deriv (deriv (variationRetractedFitting O a P teacher teacher)) 0 := by
  simpa only [hE, mul_zero] using
    spherical_retraction_actual_fit_curvature O a P teacher ‖A‖ A hbase le_rfl

-- At the exact coefficient threshold only nonnegativity is asserted.
example {d h : Nat} (O : Finset Nat) (hO : ∀ n ∈ O, Odd n)
    (a : Nat → Weight h) (P : SphericalVariation d)
    (hb : P.measure 1 = reflectedMeasure (P.measure 0))
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (R lambda p zeta : Real) (hR : ‖antisymmetricActiveMoment O (P.measure 0) (P.measure 1)‖ ≤ R)
    (hl : 0 < lambda) (hp : 2 < p) (hz : 0 < zeta) (hZ : zeta^2 ≤ variationTransport P 0)
    (heq : activeGaussianFitCurvatureConstant O a teacher R =
      lambda * sphericalRadialWeight P.radius * zeta^(p-2)) :
    0 ≤ deriv (deriv (variationRetractedObjective O a P lambda p teacher teacher)) 0 := by
  have H := spherical_retraction_actual_fit_annular_lower O hO a P hb teacher R lambda p zeta hR hl hp hz hZ
  simpa only [heq, sub_self, zero_mul] using H

-- Nonintegral real exponents are included in the actual full-objective conclusion.
example {d h : Nat} (O : Finset Nat) (hO : ∀ n ∈ O, Odd n)
    (a : Nat → Weight h) (P : SphericalVariation d)
    (hb : P.measure 1 = reflectedMeasure (P.measure 0))
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (R lambda zeta : Real) (hR : ‖antisymmetricActiveMoment O (P.measure 0) (P.measure 1)‖ ≤ R)
    (hl : 0 < lambda) (hz : 0 < zeta) (hZ : zeta^2 ≤ variationTransport P 0)
    (hE : 0 < variationEnergy P)
    (hthreshold : activeGaussianFitCurvatureConstant O a teacher R <
      lambda * sphericalRadialWeight P.radius * zeta^((5 / 2 : Real)-2)) :
    0 < deriv (deriv (variationRetractedObjective O a P lambda (5 / 2) teacher teacher)) 0 :=
  spherical_retraction_actual_fit_annular_pos O hO a P hb teacher R lambda (5 / 2) zeta hR
    hl (by norm_num) hz hZ hE hthreshold

-- The universal raw active radius also permits an empty block.
example {d h : Nat} (O : Finset Nat) (hO : ∀ n ∈ O, Odd n)
    (a : Nat → Weight h) (P : SphericalVariation d)
    (hb : P.measure 1 = reflectedMeasure (P.measure 0))
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    -(activeGaussianFitCurvatureConstant O a teacher (Real.sqrt (O.card : Real))) * variationEnergy P ≤
      deriv (deriv (variationFitting O a P teacher teacher)) 0 :=
  spherical_branch_actual_fit_curvature_universal O hO a P hb teacher
