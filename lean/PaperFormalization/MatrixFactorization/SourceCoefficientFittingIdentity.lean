import PaperFormalization.MatrixFactorization.SourceChaosReconstruction
import PaperFormalization.MatrixFactorization.ActiveFittingAnnulus

/-! # MF47: the source coefficient loss is the actual Gaussian fit

The identity is on the entire original active Hilbert space, so it also
identifies all derivatives and the manuscript's compact-ball curvature
constant. Neither equality nor differentiability is an extra assumption.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

/-- Parseval identifies the explicit coefficient loss with the actual Gaussian
fitting polynomial for every finite active set. -/
theorem sourceCoefficientFitPolynomial_eq_actual {d h : Nat}
    (pole : UnitSphere d) (O : Finset Nat) (a : Nat → Weight h)
    (teacher : ActiveMomentSpace d O) (X : ActiveMomentCoordinates d O) :
    sourceCoefficientFitPolynomial O a teacher X = activeFittingPolynomial O a teacher X := by
  rw [sourceCoefficientFitPolynomial_parseval pole, activeFittingPolynomial_eq_fittingEnergy]
  simp_rw [sourceChaosMatrixPolynomial_eq_outer]
  rfl

/-- The equality holds as an ambient function, not just on realizable moments. -/
theorem sourceCoefficientFitPolynomial_eq_actual_fun {d h : Nat}
    (pole : UnitSphere d) (O : Finset Nat) (a : Nat → Weight h)
    (teacher : ActiveMomentSpace d O) :
    sourceCoefficientFitPolynomial O a teacher = activeFittingPolynomial O a teacher :=
  funext (sourceCoefficientFitPolynomial_eq_actual pole O a teacher)

/-- Substitution of the original raw teacher and student moments gives the
original sphere-measure and Gaussian-input fitting energy. -/
theorem sourceCoefficientFitPolynomial_original_measures {d h : Nat}
    (pole : UnitSphere d) (O : Finset Nat) (a : Nat → Weight h)
    (teacher mu nu : Measure (UnitSphere d))
    [IsFiniteMeasure teacher] [IsFiniteMeasure mu] [IsFiniteMeasure nu] :
    sourceCoefficientFitPolynomial O a (rawActiveMoment O teacher) (activeMomentMap O mu nu) =
      fittingEnergy (stdGaussian (Weight d))
        (fun z => outer (meanFeature (finiteHermiteActivation O a) teacher z)
          (meanFeature (finiteHermiteActivation O a) teacher z))
        (meanFeature (finiteHermiteActivation O a) mu)
        (meanFeature (finiteHermiteActivation O a) nu) := by
  rw [sourceCoefficientFitPolynomial_eq_actual pole, activeFittingPolynomial_original_measures]

/-- The same equality holds along the source's actual normalized pushforward
for all signed parameters, retaining the original measures. -/
theorem sourceCoefficientFitPolynomial_along_retract {d h : Nat}
    (O : Finset Nat) (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher : Measure (UnitSphere d)) [IsFiniteMeasure teacher] (t : Real) :
    sourceCoefficientFitPolynomial O a (rawActiveMoment O teacher)
      (activeMomentMapAlongRetract O P.measure P.velocity P.tangent t) =
      variationRetractedFitting O a P teacher teacher t := by
  rw [sourceCoefficientFitPolynomial_eq_actual P.pole, activeFittingPolynomial_along_retract]

/-- The manuscript's displayed constant, evaluated on its explicit finite
contraction-coefficient polynomial and its original raw active Hilbert ball. -/
noncomputable def sourceFitCurvatureConstant {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (teacher : Measure (UnitSphere d)) [IsFiniteMeasure teacher]
    (R : Real) : Real :=
  activeC2CurvatureConstant (sourceCoefficientFitPolynomial O a (rawActiveMoment O teacher)) R

/-- Equality of the whole ambient functions identifies the source gradient
and Hessian suprema with the already verified actual-fit constant. -/
theorem sourceFitCurvatureConstant_eq_actual {d h : Nat} (pole : UnitSphere d)
    (O : Finset Nat) (a : Nat → Weight h) (teacher : Measure (UnitSphere d))
    [IsFiniteMeasure teacher] (R : Real) :
    sourceFitCurvatureConstant O a teacher R = activeGaussianFitCurvatureConstant O a teacher R := by
  unfold sourceFitCurvatureConstant activeGaussianFitCurvatureConstant
  rw [sourceCoefficientFitPolynomial_eq_actual_fun pole]

theorem sourceFitCurvatureConstant_nonneg {d h : Nat} (pole : UnitSphere d)
    (O : Finset Nat) (a : Nat → Weight h) (teacher : Measure (UnitSphere d))
    [IsFiniteMeasure teacher] (R : Real) (hR : 0 ≤ R) :
    0 ≤ sourceFitCurvatureConstant O a teacher R := by
  rw [sourceFitCurvatureConstant_eq_actual pole]
  exact activeGaussianFitCurvatureConstant_nonneg O a teacher R hR

end PaperFormalization.MatrixFactorization
