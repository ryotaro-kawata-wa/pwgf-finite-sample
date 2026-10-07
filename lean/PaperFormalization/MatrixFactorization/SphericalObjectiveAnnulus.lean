import PaperFormalization.MatrixFactorization.SphericalFittingCurvature

/-! # MF06: explicit sufficient curvature on fixed metric annuli

This uses the actual objective and the derived coarse fitting constant, with no
assumed fitting lower bound. It gives a sufficient annular threshold for all
initial cap states and all continuous product tangent fields. The distinct,
sharper active-block threshold printed in the manuscript is not identified here.
-/
open MeasureTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

theorem spherical_objective_curvature_lower {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (lambda p : Real)
    (hlambda : 0 < lambda) (hp : 2 < p) (hZ : 0 < variationTransport P 0)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    (lambda*(variationTransport P 0)^(p/2-1)*sphericalRadialWeight P.radius -
      fittingCurvatureConstant d O a)*variationEnergy P ≤
      deriv (deriv (variationObjective O a P lambda p teacher1 teacher2)) 0 := by
  have hf := spherical_fitting_curvature_lower O a P teacher1 teacher2 0
  rw [(spherical_fitting_source_variations O a P teacher1 teacher2 0).2.deriv] at hf
  have hr := spherical_objective_second_lower_bound O a P lambda p hlambda hp hZ teacher1 teacher2
  nlinarith

theorem annular_rpow_lower {Z zeta p : Real} (hzeta : 0 < zeta) (hp : 2 < p)
    (hZ : zeta^2 ≤ Z) : zeta^(p-2) ≤ Z^(p/2-1) := by
  calc
    zeta^(p-2) = (zeta^2)^(p/2-1) := by
      rw [← Real.rpow_natCast_mul hzeta.le]
      congr 1
      norm_num
      ring
    _ ≤ _ := Real.rpow_le_rpow (sq_nonneg _) hZ (by linarith)

/-- A quantitative sufficient annular bound with a derived, velocity-independent constant. -/
theorem spherical_objective_annular_lower {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (lambda p zeta : Real)
    (hlambda : 0 < lambda) (hp : 2 < p) (hzeta : 0 < zeta)
    (hZ : zeta^2 ≤ variationTransport P 0) (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    (lambda*sphericalRadialWeight P.radius*zeta^(p-2) - fittingCurvatureConstant d O a)*variationEnergy P ≤
      deriv (deriv (variationObjective O a P lambda p teacher1 teacher2)) 0 := by
  have hZpos : 0 < variationTransport P 0 := (sq_pos_of_pos hzeta).trans_le hZ
  have hrad : 0 < sphericalRadialWeight P.radius :=
    sphericalRadialWeight_pos (P.cap 0).radius_pos.le (P.cap 0).radius_lt
  have hpw := annular_rpow_lower hzeta hp hZ
  have hcoef := mul_le_mul_of_nonneg_left hpw (mul_nonneg hlambda.le hrad.le)
  have henergy := mul_le_mul_of_nonneg_right
    (sub_le_sub_right hcoef (fittingCurvatureConstant d O a)) (variationEnergy_nonneg P)
  have hb := spherical_objective_curvature_lower O a P lambda p hlambda hp hZpos teacher1 teacher2
  nlinarith

theorem spherical_objective_annular_pos {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (lambda p zeta : Real)
    (hlambda : 0 < lambda) (hp : 2 < p) (hzeta : 0 < zeta)
    (hZ : zeta^2 ≤ variationTransport P 0) (hE : 0 < variationEnergy P)
    (hthreshold : fittingCurvatureConstant d O a < lambda*sphericalRadialWeight P.radius*zeta^(p-2))
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    0 < deriv (deriv (variationObjective O a P lambda p teacher1 teacher2)) 0 :=
  (mul_pos (sub_pos.mpr hthreshold) hE).trans_le
    (spherical_objective_annular_lower O a P lambda p zeta hlambda hp hzeta hZ teacher1 teacher2)

/-- For a fixed cap radius and inner annulus radius the sufficient threshold is finite. -/
theorem fitting_annular_threshold_exists (d : Nat) {h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) {radius zeta p : Real} (hradius : 0 ≤ radius)
    (hrpi : radius < Real.pi/2) (hzeta : 0 < zeta) :
    ∃ L : Real, 0 < L ∧ ∀ lambda : Real, L < lambda →
      fittingCurvatureConstant d O a < lambda*sphericalRadialWeight radius*zeta^(p-2) := by
  let c := sphericalRadialWeight radius*zeta^(p-2)
  have hc : 0 < c := mul_pos (sphericalRadialWeight_pos hradius hrpi) (Real.rpow_pos_of_pos hzeta _)
  refine ⟨fittingCurvatureConstant d O a/c+1, ?_, ?_⟩
  · have hn := div_nonneg (fittingCurvatureConstant_nonneg d O a) hc.le
    linarith
  · intro lambda hlambda
    have hdiv : fittingCurvatureConstant d O a/c < lambda := by linarith
    have hb := (div_lt_iff₀ hc).mp hdiv
    simpa only [c, mul_assoc] using hb

/-- The qualitative annular statement has one threshold for all states and
directions at the fixed cap and inner radius. No branch-tangency restriction or
fitting-curvature premise is imposed. The constant is the coarse one above. -/
theorem spherical_annular_curvature_uniform {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (radius zeta p : Real) (hradius : 0 < radius)
    (hrpi : radius < Real.pi/2) (hzeta : 0 < zeta) (hp : 2 < p)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    ∃ L : Real, 0 < L ∧ ∀ lambda : Real, L < lambda →
      ∀ P : SphericalVariation d, P.radius = radius → zeta^2 ≤ variationTransport P 0 →
        0 < variationEnergy P →
        0 < deriv (deriv (variationObjective O a P lambda p teacher1 teacher2)) 0 := by
  obtain ⟨L, hL, hthreshold⟩ := fitting_annular_threshold_exists d O a (p := p) hradius.le hrpi hzeta
  refine ⟨L, hL, ?_⟩
  intro lambda hlambda P hr hZ hE
  apply spherical_objective_annular_pos O a P lambda p zeta (hL.trans hlambda) hp hzeta hZ hE
  simpa only [hr] using hthreshold lambda hlambda

end PaperFormalization.MatrixFactorization
