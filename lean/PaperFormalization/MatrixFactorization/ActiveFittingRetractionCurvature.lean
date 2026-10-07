import PaperFormalization.MatrixFactorization.ActiveGaussianFitPolynomial
import PaperFormalization.MatrixFactorization.ActiveC2RetractionCurvature
import PaperFormalization.MatrixFactorization.GeneralRetractionFittingVariation

/-! # MF39: the actual Gaussian fit in the source active curvature bound

This applies the already proved second chain rule to the actual fitting
polynomial. The remaining explicit chaos-coefficient identification is not
assumed here. All norms are the unchanged raw symmetric Hilbert norms.
-/
open MeasureTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

/-- The concrete constant uses actual fitting derivatives, not a supplied C2 function. -/
noncomputable def activeGaussianFitCurvatureConstant {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (teacher : Measure (UnitSphere d)) [IsFiniteMeasure teacher]
    (R : Real) : Real :=
  activeC2CurvatureConstant (activeFittingPolynomial O a (rawActiveMoment O teacher)) R

theorem activeGaussianFitCurvatureConstant_nonneg {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (teacher : Measure (UnitSphere d)) [IsFiniteMeasure teacher]
    (R : Real) (hR : 0 ≤ R) : 0 ≤ activeGaussianFitCurvatureConstant O a teacher R := by
  apply activeC2CurvatureConstant_nonneg _
    ((activeFittingPolynomial_contDiff O a (rawActiveMoment O teacher)).of_le (by simp)) R 0
  simpa only [norm_zero] using hR

/-- The equality holds for the actual normalized pushed laws at every signed time. -/
theorem activeFittingPolynomial_along_retract {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher : Measure (UnitSphere d)) [IsFiniteMeasure teacher] (t : Real) :
    activeFittingPolynomial O a (rawActiveMoment O teacher)
      (activeMomentMapAlongRetract O P.measure P.velocity P.tangent t) =
      variationRetractedFitting O a P teacher teacher t := by
  rw [activeMomentMapAlongRetract_eq, activeFittingPolynomial_original_measures]
  rfl

/-- Arbitrary continuous tangent fields are allowed at the antisymmetric active base. -/
theorem spherical_retraction_actual_fit_curvature {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher : Measure (UnitSphere d)) [IsFiniteMeasure teacher]
    (R : Real) (A : ActiveMomentSpace d O)
    (hbase : activeMomentMap O (P.measure 0) (P.measure 1) = activeAntisymmetricPoint A)
    (hA : ‖A‖ ≤ R) :
    -(activeGaussianFitCurvatureConstant O a teacher R) * variationEnergy P ≤
      deriv (deriv (variationRetractedFitting O a P teacher teacher)) 0 := by
  have hc := (spherical_retraction_c2_active_curvature O
    (activeFittingPolynomial O a (rawActiveMoment O teacher))
    ((activeFittingPolynomial_contDiff O a (rawActiveMoment O teacher)).of_le (by simp))
    P R A hbase hA).2
  have he : (fun t => activeFittingPolynomial O a (rawActiveMoment O teacher)
      (activeMomentMapAlongRetract O P.measure P.velocity P.tangent t)) =
      variationRetractedFitting O a P teacher teacher :=
    funext (activeFittingPolynomial_along_retract O a P teacher)
  rw [he] at hc
  exact hc

/-- The same concrete bound transfers to the true EXP second derivative. -/
theorem spherical_exp_actual_fit_curvature {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (R : Real) (A : ActiveMomentSpace d O)
    (hbase : activeMomentMap O (P.measure 0) (P.measure 1) = activeAntisymmetricPoint A)
    (hA : ‖A‖ ≤ R) :
    -(activeGaussianFitCurvatureConstant O a teacher R) * variationEnergy P ≤
      deriv (deriv (variationFitting O a P teacher teacher)) 0 := by
  rw [← (variationRetractedFitting_derivatives_eq_exp O a P teacher teacher).2]
  exact spherical_retraction_actual_fit_curvature O a P teacher R A hbase hA

/-- Actual reflected laws provide the active base; no branch tangency is requested. -/
theorem spherical_branch_actual_fit_curvature {d h : Nat} (O : Finset Nat)
    (hO : ∀ n ∈ O, Odd n) (a : Nat → Weight h) (P : SphericalVariation d)
    (hbranch : P.measure 1 = reflectedMeasure (P.measure 0))
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (R : Real) (hR : ‖antisymmetricActiveMoment O (P.measure 0) (P.measure 1)‖ ≤ R) :
    -(activeGaussianFitCurvatureConstant O a teacher R) * variationEnergy P ≤
      deriv (deriv (variationFitting O a P teacher teacher)) 0 :=
  spherical_exp_actual_fit_curvature O a P teacher R
    (antisymmetricActiveMoment O (P.measure 0) (P.measure 1))
    (activeMomentMap_reflected_branch O hO P hbranch) hR

/-- The universal raw active radius depends only on the number of active orders. -/
theorem spherical_branch_actual_fit_curvature_universal {d h : Nat} (O : Finset Nat)
    (hO : ∀ n ∈ O, Odd n) (a : Nat → Weight h) (P : SphericalVariation d)
    (hbranch : P.measure 1 = reflectedMeasure (P.measure 0))
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    -(activeGaussianFitCurvatureConstant O a teacher (Real.sqrt (O.card : Real))) * variationEnergy P ≤
      deriv (deriv (variationFitting O a P teacher teacher)) 0 :=
  spherical_branch_actual_fit_curvature O hO a P hbranch teacher _
    (antisymmetricActiveMoment_norm_le O (P.measure 0) (P.measure 1))

end PaperFormalization.MatrixFactorization
