import PaperFormalization.MatrixFactorization.GaussianFeatureWasserstein
import PaperFormalization.MatrixFactorization.GeneralRetractionObjective

/-! # Curvature controlled by the actual distance to the teacher

The residual bound is obtained from the original finite activation and the
infimum over spherical couplings. Only the residual contribution to the
second fitting derivative can be negative. The resulting constant depends
on the fixed activation and input dimension, and no residual or curvature
hypothesis is introduced.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The matrix residual is estimated in its literal Frobenius norm. -/
theorem outer_difference_norm_bound {h : Nat} (x y u v : Weight h) :
    norm (outer x y-outer u v) ≤ norm (x-u)*norm y + norm u*norm (y-v) := by
  have he : outer x y-outer u v = outer (x-u) y + outer u (y-v) := by
    ext ij
    simp only [outer, PiLp.sub_apply, PiLp.add_apply]
    change x ij.1*y ij.2-u ij.1*v ij.2 = (x ij.1-u ij.1)*y ij.2+u ij.1*(y ij.2-v ij.2)
    ring
  rw [he]
  exact (norm_add_le _ _).trans_eq (by rw [outer_norm, outer_norm])

/-- Original first speed moments are controlled by the original tangent energy. -/
theorem outerSecond_energy_bound {h : Nat} (x y dx dy ddx ddy : Weight h)
    (B Lx Ly Qx Qy : Real) (hB : 0 ≤ B) (hLx : 0 ≤ Lx)
    (hQx : 0 ≤ Qx) (hcross : 2*Lx*Ly ≤ Qx+Qy)
    (hx : norm x ≤ B) (hy : norm y ≤ B)
    (hdx : norm dx ≤ Lx*B) (hdy : norm dy ≤ Ly*B)
    (hddx : norm ddx ≤ Qx*B) (hddy : norm ddy ≤ Qy*B) :
    norm (outerSecond x y dx dy ddx ddy) ≤ 2*(Qx+Qy)*B^2 := by
  unfold outerSecond
  calc
    _ ≤ norm (outer ddx y)+norm ((2 : Real) • outer dx dy)+norm (outer x ddy) :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = norm ddx*norm y+2*(norm dx*norm dy)+norm x*norm ddy := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2), outer_norm]
    _ ≤ (Qx*B)*B+2*((Lx*B)*(Ly*B))+B*(Qy*B) :=
      add_le_add (add_le_add (mul_le_mul hddx hy (norm_nonneg _) (mul_nonneg hQx hB))
        (mul_le_mul_of_nonneg_left (mul_le_mul hdx hdy (norm_nonneg _) (mul_nonneg hLx hB)) (by norm_num)))
        (mul_le_mul hx hddy (norm_nonneg _) hB)
    _ = (Qx+2*Lx*Ly+Qy)*B^2 := by ring
    _ ≤ 2*(Qx+Qy)*B^2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

/-- The actual product output residual tends to zero with the original
spherical Wasserstein distance to the teacher. -/
theorem variationOutput_teacher_residual_bound {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (z : Weight d) :
    norm (outer (variationFeature O a P 0 0 z) (variationFeature O a P 1 0 z)-
      teacherOutput O a teacher1 teacher2 z) ≤
        2*Real.sqrt (sphericalWassersteinSq (P.measure 0) teacher1 +
          sphericalWassersteinSq (P.measure 1) teacher2)*(fittingFeatureEnvelope O a z)^2 := by
  letI : IsProbabilityMeasure (P.measure 0) := (P.cap 0).probability
  letI : IsProbabilityMeasure (P.measure 1) := (P.cap 1).probability
  let B := fittingFeatureEnvelope O a z
  let D := Real.sqrt (sphericalWassersteinSq (P.measure 0) teacher1 +
    sphericalWassersteinSq (P.measure 1) teacher2)
  have hB : 0 ≤ B := fittingFeatureEnvelope_nonneg O a z
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have h0 := sphericalWassersteinSq_nonneg (P.measure 0) teacher1
  have h1 := sphericalWassersteinSq_nonneg (P.measure 1) teacher2
  have hd0 : Real.sqrt (sphericalWassersteinSq (P.measure 0) teacher1) ≤ D :=
    Real.sqrt_le_sqrt (le_add_of_nonneg_right h1)
  have hd1 : Real.sqrt (sphericalWassersteinSq (P.measure 1) teacher2) ≤ D :=
    Real.sqrt_le_sqrt (le_add_of_nonneg_left h0)
  have he : featureFirstEnvelope 0 O a z ≤ B := (fittingFeatureEnvelope_bounds O a z).2.1
  have hx := finiteHermite_mean_wasserstein_norm_le O a (P.measure 0) teacher1 z
  have hy := finiteHermite_mean_wasserstein_norm_le O a (P.measure 1) teacher2 z
  have hx' : norm (variationFeature O a P 0 0 z-
      meanFeature (finiteHermiteActivation O a) teacher1 z) ≤ B*D := by
    rw [variationFeature_initial]
    exact hx.trans (mul_le_mul he hd0 (Real.sqrt_nonneg _) hB)
  have hy' : norm (variationFeature O a P 1 0 z-
      meanFeature (finiteHermiteActivation O a) teacher2 z) ≤ B*D := by
    rw [variationFeature_initial]
    exact hy.trans (mul_le_mul he hd1 (Real.sqrt_nonneg _) hB)
  have hs := (variationFeature_energy_bounds O a P 1 0 z).1
  have ht : norm (meanFeature (finiteHermiteActivation O a) teacher1 z) ≤ B :=
    (finiteHermite_mean_growth O a teacher1 z).trans (fittingFeatureEnvelope_bounds O a z).2.2.2
  change _ ≤ 2*D*B^2
  calc
    _ ≤ norm (variationFeature O a P 0 0 z-meanFeature (finiteHermiteActivation O a) teacher1 z)*
        norm (variationFeature O a P 1 0 z) +
        norm (meanFeature (finiteHermiteActivation O a) teacher1 z)*
        norm (variationFeature O a P 1 0 z-meanFeature (finiteHermiteActivation O a) teacher2 z) :=
      outer_difference_norm_bound _ _ _ _
    _ ≤ (B*D)*B+B*(B*D) :=
      add_le_add (mul_le_mul hx' hs (norm_nonneg _) (mul_nonneg hB hD))
        (mul_le_mul ht hy' (norm_nonneg _) hB)
    _ = _ := by ring

/-- The nonnegative squared first output derivative is retained, and only the
residual term is bounded below. -/
theorem variationMatrixSecond_teacher_distance_lower {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (z : Weight d) :
    -(4*(fittingFeatureEnvelope O a z)^4)*
      Real.sqrt (sphericalWassersteinSq (P.measure 0) teacher1 +
        sphericalWassersteinSq (P.measure 1) teacher2)*variationEnergy P ≤
      variationMatrixSecond O a P teacher1 teacher2 0 z := by
  have h0 := variationFeature_energy_bounds O a P 0 0 z
  have h1 := variationFeature_energy_bounds O a P 1 0 z
  have hAA := outerSecond_energy_bound _ _ _ _ _ _ (fittingFeatureEnvelope O a z)
    (firstSpeedMoment P 0) (firstSpeedMoment P 1)
    (secondSpeedMoment P 0) (secondSpeedMoment P 1) (fittingFeatureEnvelope_nonneg O a z)
    (speedMoments_nonneg P 0).1 (speedMoments_nonneg P 0).2 (speedMoments_cross_bound P)
    h0.1 h1.1 h0.2.1 h1.2.1 h0.2.2 h1.2.2
  have hAA' : norm (outerSecond (variationFeature O a P 0 0 z) (variationFeature O a P 1 0 z)
      (variationFeatureFirst O a P 0 0 z) (variationFeatureFirst O a P 1 0 z)
      (variationFeatureSecond O a P 0 0 z) (variationFeatureSecond O a P 1 0 z)) ≤
        2*variationEnergy P*(fittingFeatureEnvelope O a z)^2 := by
    simpa only [variationEnergy, Fin.sum_univ_two, secondSpeedMoment] using hAA
  have hR := variationOutput_teacher_residual_bound O a P teacher1 teacher2 z
  have hp := mul_le_mul hR hAA' (norm_nonneg _) (by positivity)
  have hi := neg_le_of_abs_le (abs_real_inner_le_norm
    (outer (variationFeature O a P 0 0 z) (variationFeature O a P 1 0 z)-
      teacherOutput O a teacher1 teacher2 z)
    (outerSecond (variationFeature O a P 0 0 z) (variationFeature O a P 1 0 z)
      (variationFeatureFirst O a P 0 0 z) (variationFeatureFirst O a P 1 0 z)
      (variationFeatureSecond O a P 0 0 z) (variationFeatureSecond O a P 1 0 z)))
  have hs := sq_nonneg (norm (outerFirst (variationFeature O a P 0 0 z) (variationFeature O a P 1 0 z)
    (variationFeatureFirst O a P 0 0 z) (variationFeatureFirst O a P 1 0 z)))
  unfold variationMatrixSecond matrixPointSecond
  nlinarith

/-- The coefficient is fixed by the finite activation and Gaussian input
alone; the distance factor is derived from the original measures. -/
theorem spherical_fitting_teacher_distance_lower {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    -fittingCurvatureConstant d O a *
      Real.sqrt (sphericalWassersteinSq (P.measure 0) teacher1 +
        sphericalWassersteinSq (P.measure 1) teacher2)*variationEnergy P ≤
      deriv (deriv (variationFitting O a P teacher1 teacher2)) 0 := by
  rw [(spherical_fitting_source_variations O a P teacher1 teacher2 0).2.deriv]
  let D := Real.sqrt (sphericalWassersteinSq (P.measure 0) teacher1 +
    sphericalWassersteinSq (P.measure 1) teacher2)
  have hi := ((((fittingCurvatureConstant_integrable d O a).const_mul 4).neg).mul_const D).mul_const (variationEnergy P)
  have hb := integral_mono hi (variationMatrix_integrable O a P teacher1 teacher2 0).2.2
    (variationMatrixSecond_teacher_distance_lower O a P teacher1 teacher2)
  simpa only [Pi.neg_apply, integral_mul_const, integral_neg, integral_const_mul,
    fittingCurvatureConstant, variationFittingSecond] using hb

/-- The same bound holds for the literal normalized pushed measures. -/
theorem normalized_fitting_teacher_distance_lower {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    -fittingCurvatureConstant d O a *
      Real.sqrt (sphericalWassersteinSq (P.measure 0) teacher1 +
        sphericalWassersteinSq (P.measure 1) teacher2)*variationEnergy P ≤
      deriv (deriv (variationRetractedFitting O a P teacher1 teacher2)) 0 := by
  rw [(variationRetractedFitting_derivatives_eq_exp O a P teacher1 teacher2).2]
  exact spherical_fitting_teacher_distance_lower O a P teacher1 teacher2

/-- The actual full objective has a positive regularizer margin minus a
teacher-distance error, for every admissible product tangent direction. -/
theorem normalized_objective_teacher_distance_lower {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (lambda p : Real)
    (hlambda : 0 < lambda) (hp : 2 < p) (hZ : 0 < variationTransport P 0)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    (lambda*(variationTransport P 0)^(p/2-1)*sphericalRadialWeight P.radius -
      fittingCurvatureConstant d O a *
        Real.sqrt (sphericalWassersteinSq (P.measure 0) teacher1 +
          sphericalWassersteinSq (P.measure 1) teacher2))*variationEnergy P ≤
      deriv (deriv (variationRetractedObjective O a P lambda p teacher1 teacher2)) 0 := by
  rw [(variationRetractedObjective_derivatives_eq_exp O a P lambda p hlambda hp teacher1 teacher2).2]
  have hf := spherical_fitting_teacher_distance_lower O a P teacher1 teacher2
  rw [(spherical_fitting_source_variations O a P teacher1 teacher2 0).2.deriv] at hf
  have hr := spherical_objective_second_lower_bound O a P lambda p hlambda hp hZ teacher1 teacher2
  nlinarith

end PaperFormalization.MatrixFactorization
