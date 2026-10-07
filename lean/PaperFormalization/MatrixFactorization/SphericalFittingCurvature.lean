import PaperFormalization.MatrixFactorization.FittingEnergyBounds

/-! # MF06: a uniform energy-scaled bound for spherical fitting curvature

The constant below depends only on the finite activation and Gaussian input
dimension. It is an explicit coarse bound obtained from the original features;
it is not identified with the manuscript's sharper active-block constant.
There is no supplied fitting lower-bound hypothesis in the source-facing result.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def firstSpeedMoment {d : Nat} (P : SphericalVariation d) (i : Fin 2) : Real :=
  ∫ w, norm (P.velocity i w) ∂P.measure i

noncomputable def secondSpeedMoment {d : Nat} (P : SphericalVariation d) (i : Fin 2) : Real :=
  ∫ w, norm (P.velocity i w)^2 ∂P.measure i

theorem speedMoments_nonneg {d : Nat} (P : SphericalVariation d) (i : Fin 2) :
    0 ≤ firstSpeedMoment P i ∧ 0 ≤ secondSpeedMoment P i :=
  ⟨integral_nonneg (fun w => norm_nonneg _), integral_nonneg (fun w => sq_nonneg _)⟩

theorem speedMoments_cross_bound {d : Nat} (P : SphericalVariation d) :
    2*firstSpeedMoment P 0*firstSpeedMoment P 1 ≤ secondSpeedMoment P 0+secondSpeedMoment P 1 := by
  have hs (i : Fin 2) : (firstSpeedMoment P i)^2 ≤ secondSpeedMoment P i := by
    letI : IsProbabilityMeasure (P.measure i) := (P.cap i).probability
    exact sphere_speed_integral_sq_le (P.measure i) (P.velocity i) (P.continuous_velocity i)
  have h0 := hs 0
  have h1 := hs 1
  nlinarith [sq_nonneg (firstSpeedMoment P 0-firstSpeedMoment P 1)]

theorem variationFeature_energy_bounds {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (i : Fin 2) (t : Real) (z : Weight d) :
    norm (variationFeature O a P i t z) ≤ fittingFeatureEnvelope O a z ∧
    norm (variationFeatureFirst O a P i t z) ≤ firstSpeedMoment P i*fittingFeatureEnvelope O a z ∧
    norm (variationFeatureSecond O a P i t z) ≤ secondSpeedMoment P i*fittingFeatureEnvelope O a z := by
  letI : IsProbabilityMeasure (P.measure i) := (P.cap i).probability
  have hb := meanFeatureAlongExp_bounds 0 O a (P.measure i) (P.velocity i) (P.tangent i)
    (P.continuous_velocity i) z t
  have he := fittingFeatureEnvelope_bounds O a z
  exact ⟨hb.1.trans he.1,
    hb.2.1.trans (mul_le_mul_of_nonneg_left he.2.1 (speedMoments_nonneg P i).1),
    hb.2.2.trans (mul_le_mul_of_nonneg_left he.2.2.1 (speedMoments_nonneg P i).2)⟩

theorem teacherOutput_uniform_bound {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (z : Weight d) :
    norm (teacherOutput O a teacher1 teacher2 z) ≤ (fittingFeatureEnvelope O a z)^2 := by
  have hb (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] :
      norm (meanFeature (finiteHermiteActivation O a) mu z) ≤ fittingFeatureEnvelope O a z :=
    (finiteHermite_mean_growth O a mu z).trans (fittingFeatureEnvelope_bounds O a z).2.2.2
  rw [teacherOutput, outer_norm, pow_two]
  exact mul_le_mul (hb teacher1) (hb teacher2) (norm_nonneg _) (fittingFeatureEnvelope_nonneg O a z)

/-- The lower bound is quadratic in the velocity, uniformly in the state and time. -/
theorem variationMatrixSecond_energy_lower {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (t : Real) (z : Weight d) :
    -(4*(fittingFeatureEnvelope O a z)^4)*variationEnergy P ≤
      variationMatrixSecond O a P teacher1 teacher2 t z := by
  have h0 := variationFeature_energy_bounds O a P 0 t z
  have h1 := variationFeature_energy_bounds O a P 1 t z
  have hb := matrixPointSecond_energy_lower (teacherOutput O a teacher1 teacher2 z)
    _ _ _ _ _ _ (fittingFeatureEnvelope O a z) (firstSpeedMoment P 0) (firstSpeedMoment P 1)
    (secondSpeedMoment P 0) (secondSpeedMoment P 1) (fittingFeatureEnvelope_nonneg O a z)
    (speedMoments_nonneg P 0).1 (speedMoments_nonneg P 1).1
    (speedMoments_nonneg P 0).2 (speedMoments_nonneg P 1).2 (speedMoments_cross_bound P)
    (teacherOutput_uniform_bound O a teacher1 teacher2 z) h0.1 h1.1 h0.2.1 h1.2.1 h0.2.2 h1.2.2
  simpa only [variationEnergy, Fin.sum_univ_two, secondSpeedMoment, variationMatrixSecond] using hb

noncomputable def fittingCurvatureConstant (d : Nat) {h : Nat}
    (O : Finset Nat) (a : Nat → Weight h) : Real :=
  4*∫ z : Weight d, (fittingFeatureEnvelope O a z)^4 ∂stdGaussian (Weight d)

theorem fittingCurvatureConstant_integrable (d : Nat) {h : Nat}
    (O : Finset Nat) (a : Nat → Weight h) :
    Integrable (fun z : Weight d => (fittingFeatureEnvelope O a z)^4) (stdGaussian (Weight d)) := by
  simpa only [one_mul] using fittingFeatureEnvelope_gaussian_integrable (d := d) O a 1 4

theorem fittingCurvatureConstant_nonneg (d : Nat) {h : Nat}
    (O : Finset Nat) (a : Nat → Weight h) : 0 ≤ fittingCurvatureConstant d O a :=
  mul_nonneg (by norm_num) (integral_nonneg (fun z => by positivity))

/-- A derived lower bound for the actual fit, with no auxiliary model premise. -/
theorem spherical_fitting_curvature_lower {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (t : Real) :
    -fittingCurvatureConstant d O a*variationEnergy P ≤
      deriv (deriv (variationFitting O a P teacher1 teacher2)) t := by
  rw [(spherical_fitting_source_variations O a P teacher1 teacher2 t).2.deriv]
  have hi := (((fittingCurvatureConstant_integrable d O a).const_mul 4).neg).mul_const (variationEnergy P)
  have hb := integral_mono hi (variationMatrix_integrable O a P teacher1 teacher2 t).2.2
    (variationMatrixSecond_energy_lower O a P teacher1 teacher2 t)
  simpa only [Pi.neg_apply, integral_mul_const, integral_neg, integral_const_mul,
    fittingCurvatureConstant, variationFittingSecond] using hb

end PaperFormalization.MatrixFactorization
