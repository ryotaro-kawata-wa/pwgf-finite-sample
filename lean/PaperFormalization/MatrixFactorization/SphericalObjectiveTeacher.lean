import PaperFormalization.MatrixFactorization.SphericalObjectiveCenter

/-! # MF05: pointwise curvature at the actual teacher state

At an exact teacher state, the fitting residual vanishes and only the squared
first output derivative remains. Adding the verified metric contribution gives
strict positivity in every nonzero L2 direction when the teacher transport is
positive. This is a statement at the teacher itself; the uniform Wasserstein
neighborhood in the manuscript requires a separate continuity argument.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

theorem variationMatrix_at_teacher {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (z : Weight d) :
    variationMatrixFirst O a P (P.measure 0) (P.measure 1) 0 z = 0 ∧
    variationMatrixSecond O a P (P.measure 0) (P.measure 1) 0 z =
      norm (outerFirst (variationFeature O a P 0 0 z) (variationFeature O a P 1 0 z)
        (variationFeatureFirst O a P 0 0 z) (variationFeatureFirst O a P 1 0 z))^2 := by
  simp [variationMatrixFirst, variationMatrixSecond, matrixPointFirst, matrixPointSecond,
    variationFeature_initial, teacherOutput, sub_self, inner_zero_left, add_zero]

theorem variationFitting_teacher_first {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) : variationFittingFirst O a P (P.measure 0) (P.measure 1) 0 = 0 := by
  simp only [variationFittingFirst, (variationMatrix_at_teacher O a P _).1, integral_zero]

theorem variationFitting_teacher_second_nonneg {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) :
    0 ≤ variationFittingSecond O a P (P.measure 0) (P.measure 1) 0 := by
  apply integral_nonneg
  intro z
  rw [(variationMatrix_at_teacher O a P z).2]
  exact sq_nonneg _

theorem spherical_objective_teacher_second_lower {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (lambda p : Real)
    (hlambda : 0 < lambda) (hp : 2 < p) (hZ : 0 < variationTransport P 0) :
    lambda*(variationTransport P 0)^(p/2-1)*sphericalRadialWeight P.radius*variationEnergy P ≤
      deriv (deriv (variationObjective O a P lambda p (P.measure 0) (P.measure 1))) 0 := by
  letI : IsProbabilityMeasure (P.measure 0) := (P.cap 0).probability
  letI : IsProbabilityMeasure (P.measure 1) := (P.cap 1).probability
  have hb := spherical_objective_second_lower_bound O a P lambda p hlambda hp hZ (P.measure 0) (P.measure 1)
  have hn := variationFitting_teacher_second_nonneg O a P
  linarith

/-- Exact teacher-point positivity, without asserting stationarity or a neighborhood. -/
theorem spherical_objective_teacher_second_pos {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d) (lambda p : Real)
    (hlambda : 0 < lambda) (hp : 2 < p) (hZ : 0 < variationTransport P 0)
    (hE : 0 < variationEnergy P) :
    0 < deriv (deriv (variationObjective O a P lambda p (P.measure 0) (P.measure 1))) 0 := by
  have hr : 0 < sphericalRadialWeight P.radius :=
    sphericalRadialWeight_pos (P.cap 0).radius_pos.le (P.cap 0).radius_lt
  exact (mul_pos (mul_pos (mul_pos hlambda (Real.rpow_pos_of_pos hZ _)) hr) hE).trans_le
    (spherical_objective_teacher_second_lower O a P lambda p hlambda hp hZ)

end PaperFormalization.MatrixFactorization
