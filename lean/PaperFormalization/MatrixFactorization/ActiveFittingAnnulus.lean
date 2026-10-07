import PaperFormalization.MatrixFactorization.ActiveFittingRetractionCurvature
import PaperFormalization.MatrixFactorization.GeneralRetractionObjective

/-! # MF39: ambient annular curvature with the actual active Gaussian fit

The same concrete constant controls arbitrary product tangent perturbations
at reflected cap states. The result is pointwise in the state; no geodesic
convexity of the annulus is inferred.
-/
open MeasureTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000

/-- Combine the actual fitting Hessian with the existing true transport Hessian. -/
theorem spherical_actual_fit_objective_curvature {d h : Nat} (O : Finset Nat)
    (hO : ∀ n ∈ O, Odd n) (a : Nat → Weight h) (P : SphericalVariation d)
    (hbranch : P.measure 1 = reflectedMeasure (P.measure 0))
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (R lambda p : Real) (hR : ‖antisymmetricActiveMoment O (P.measure 0) (P.measure 1)‖ ≤ R)
    (hlambda : 0 < lambda) (hp : 2 < p) (hZ : 0 < variationTransport P 0) :
    (lambda * (variationTransport P 0) ^ (p / 2 - 1) * sphericalRadialWeight P.radius -
      activeGaussianFitCurvatureConstant O a teacher R) * variationEnergy P ≤
      deriv (deriv (variationObjective O a P lambda p teacher teacher)) 0 := by
  have hf := spherical_branch_actual_fit_curvature O hO a P hbranch teacher R hR
  rw [(spherical_fitting_source_variations O a P teacher teacher 0).2.deriv] at hf
  have hr := spherical_objective_second_lower_bound O a P lambda p hlambda hp hZ teacher teacher
  nlinarith

/-- The annulus only supplies the positive lower radius for the regularizer. -/
theorem spherical_actual_fit_annular_lower {d h : Nat} (O : Finset Nat)
    (hO : ∀ n ∈ O, Odd n) (a : Nat → Weight h) (P : SphericalVariation d)
    (hbranch : P.measure 1 = reflectedMeasure (P.measure 0))
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (R lambda p zeta : Real) (hR : ‖antisymmetricActiveMoment O (P.measure 0) (P.measure 1)‖ ≤ R)
    (hlambda : 0 < lambda) (hp : 2 < p) (hzeta : 0 < zeta)
    (hZ : zeta ^ 2 ≤ variationTransport P 0) :
    (lambda * sphericalRadialWeight P.radius * zeta ^ (p - 2) -
      activeGaussianFitCurvatureConstant O a teacher R) * variationEnergy P ≤
      deriv (deriv (variationObjective O a P lambda p teacher teacher)) 0 := by
  have hZpos : 0 < variationTransport P 0 := (sq_pos_of_pos hzeta).trans_le hZ
  have hrad := sphericalRadialWeight_pos (P.cap 0).radius_pos.le (P.cap 0).radius_lt
  have hpw := annular_rpow_lower hzeta hp hZ
  have hcoef := mul_le_mul_of_nonneg_left hpw (mul_nonneg hlambda.le hrad.le)
  have henergy := mul_le_mul_of_nonneg_right
    (sub_le_sub_right hcoef (activeGaussianFitCurvatureConstant O a teacher R))
    (variationEnergy_nonneg P)
  have hb := spherical_actual_fit_objective_curvature O hO a P hbranch teacher R lambda p hR hlambda hp hZpos
  nlinarith

/-- The actual normalized spherical pushforward has the same second variation. -/
theorem spherical_retraction_actual_fit_annular_lower {d h : Nat} (O : Finset Nat)
    (hO : ∀ n ∈ O, Odd n) (a : Nat → Weight h) (P : SphericalVariation d)
    (hbranch : P.measure 1 = reflectedMeasure (P.measure 0))
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (R lambda p zeta : Real) (hR : ‖antisymmetricActiveMoment O (P.measure 0) (P.measure 1)‖ ≤ R)
    (hlambda : 0 < lambda) (hp : 2 < p) (hzeta : 0 < zeta)
    (hZ : zeta ^ 2 ≤ variationTransport P 0) :
    (lambda * sphericalRadialWeight P.radius * zeta ^ (p - 2) -
      activeGaussianFitCurvatureConstant O a teacher R) * variationEnergy P ≤
      deriv (deriv (variationRetractedObjective O a P lambda p teacher teacher)) 0 := by
  rw [(variationRetractedObjective_derivatives_eq_exp O a P lambda p hlambda hp teacher teacher).2]
  exact spherical_actual_fit_annular_lower O hO a P hbranch teacher R lambda p zeta hR hlambda hp hzeta hZ

/-- Strict positivity is for every direction of positive product L2 norm. -/
theorem spherical_retraction_actual_fit_annular_pos {d h : Nat} (O : Finset Nat)
    (hO : ∀ n ∈ O, Odd n) (a : Nat → Weight h) (P : SphericalVariation d)
    (hbranch : P.measure 1 = reflectedMeasure (P.measure 0))
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (R lambda p zeta : Real) (hR : ‖antisymmetricActiveMoment O (P.measure 0) (P.measure 1)‖ ≤ R)
    (hlambda : 0 < lambda) (hp : 2 < p) (hzeta : 0 < zeta)
    (hZ : zeta ^ 2 ≤ variationTransport P 0) (hE : 0 < variationEnergy P)
    (hthreshold : activeGaussianFitCurvatureConstant O a teacher R <
      lambda * sphericalRadialWeight P.radius * zeta ^ (p - 2)) :
    0 < deriv (deriv (variationRetractedObjective O a P lambda p teacher teacher)) 0 :=
  (mul_pos (sub_pos.mpr hthreshold) hE).trans_le
    (spherical_retraction_actual_fit_annular_lower O hO a P hbranch teacher R lambda p zeta hR
      hlambda hp hzeta hZ)

/-- A single finite threshold controls all states in the fixed raw active ball and annulus. -/
theorem actual_fit_annular_threshold_exists {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (teacher : Measure (UnitSphere d)) [IsFiniteMeasure teacher]
    (R radius zeta p : Real) (hR : 0 ≤ R) (hradius : 0 ≤ radius)
    (hrpi : radius < Real.pi / 2) (hzeta : 0 < zeta) :
    ∃ L : Real, 0 < L ∧ ∀ lambda : Real, L < lambda →
      activeGaussianFitCurvatureConstant O a teacher R <
        lambda * sphericalRadialWeight radius * zeta ^ (p - 2) := by
  let c := sphericalRadialWeight radius * zeta ^ (p - 2)
  have hc : 0 < c := mul_pos (sphericalRadialWeight_pos hradius hrpi) (Real.rpow_pos_of_pos hzeta _)
  refine ⟨activeGaussianFitCurvatureConstant O a teacher R / c + 1, ?_, ?_⟩
  · have hn := div_nonneg (activeGaussianFitCurvatureConstant_nonneg O a teacher R hR) hc.le
    linarith
  · intro lambda hlambda
    have hdiv : activeGaussianFitCurvatureConstant O a teacher R / c < lambda := by linarith
    simpa only [c, mul_assoc] using (div_lt_iff₀ hc).mp hdiv

/-- Uniform pointwise ambient curvature, without requiring branch-tangent velocities. -/
theorem spherical_actual_fit_annular_uniform {d h : Nat} (O : Finset Nat)
    (hO : ∀ n ∈ O, Odd n) (a : Nat → Weight h)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (R radius zeta p : Real) (hR : 0 ≤ R) (hradius : 0 < radius)
    (hrpi : radius < Real.pi / 2) (hzeta : 0 < zeta) (hp : 2 < p) :
    ∃ L : Real, 0 < L ∧ ∀ lambda : Real, L < lambda →
      ∀ P : SphericalVariation d, P.radius = radius →
        P.measure 1 = reflectedMeasure (P.measure 0) →
        ‖antisymmetricActiveMoment O (P.measure 0) (P.measure 1)‖ ≤ R →
        zeta ^ 2 ≤ variationTransport P 0 → 0 < variationEnergy P →
        0 < deriv (deriv (variationRetractedObjective O a P lambda p teacher teacher)) 0 := by
  obtain ⟨L, hL, hthreshold⟩ := actual_fit_annular_threshold_exists O a teacher R radius zeta p
    hR hradius.le hrpi hzeta
  refine ⟨L, hL, ?_⟩
  intro lambda hlambda P hr hb hA hZ hE
  apply spherical_retraction_actual_fit_annular_pos O hO a P hb teacher R lambda p zeta hA
    (hL.trans hlambda) hp hzeta hZ hE
  simpa only [hr] using hthreshold lambda hlambda

end PaperFormalization.MatrixFactorization
