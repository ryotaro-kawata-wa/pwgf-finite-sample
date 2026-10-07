import PaperFormalization.MatrixFactorization.TeacherImbalanceTransport
import PaperFormalization.MatrixFactorization.TeacherCurvatureMargin
import PaperFormalization.MatrixFactorization.TeacherResidualCurvature

/-! # Uniform positive ambient curvature in an actual teacher neighborhood

The radius and positive margin are chosen before the state and tangent field.
The neighborhood is relative to the original closed-support cap class and is
measured by the actual all-coupling spherical transport costs. No density,
stationarity, or gradient-flow entry condition is imposed on the teacher.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Source item (iv): a uniform positive margin near the same-density teacher,
for the complete normalized objective and every continuous tangent field. -/
theorem normalized_teacher_neighborhood_curvature {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (radius : Real)
    (teacher : Measure (UnitSphere d)) (hteacher : TwoCapClass pole radius teacher)
    (lambda p : Real) (hlambda : 0 < lambda) (hp : 2 < p)
    (hZo : 0 < productAntipodalTransportSq pole teacher teacher) :
    ∃ rho c : Real, 0 < rho ∧ 0 < c ∧
      ∀ P : SphericalVariation d, P.pole = pole → P.radius = radius →
        sphericalWassersteinSq (P.measure 0) teacher +
          sphericalWassersteinSq (P.measure 1) teacher < rho^2 →
        c*variationEnergy P ≤
          deriv (deriv (variationRetractedObjective O a P lambda p teacher teacher)) 0 := by
  letI : IsProbabilityMeasure teacher := hteacher.probability
  have hk := sphericalRadialWeight_pos hteacher.radius_pos.le hteacher.radius_lt
  obtain ⟨rho,c,hrho,hc,hmargin⟩ := teacher_curvature_margin_exists lambda
    (sphericalRadialWeight radius) (p/2-1) (productAntipodalTransportSq pole teacher teacher)
    (fittingCurvatureConstant d O a) hlambda hk (by linarith) hZo
    (fittingCurvatureConstant_nonneg d O a)
  refine ⟨rho,c,hrho,hc,?_⟩
  intro P hpole hradius hnear
  have ht : TwoCapClass P.pole P.radius teacher := by
    rw [hpole,hradius]
    exact hteacher
  have hclose := productAntipodalTransportSq_teacher_sub_abs_le P.pole P.radius
    (P.measure 0) (P.measure 1) teacher (P.cap 0) (P.cap 1) ht
  have hD : Real.sqrt (sphericalWassersteinSq (P.measure 0) teacher+
      sphericalWassersteinSq (P.measure 1) teacher) < rho := (Real.sqrt_lt' hrho).mpr hnear
  have hm := hmargin (variationTransport P 0)
    (Real.sqrt (sphericalWassersteinSq (P.measure 0) teacher+
      sphericalWassersteinSq (P.measure 1) teacher)) (Real.sqrt_nonneg _) hD
    (by simpa only [variationTransport_zero,hpole] using hclose)
  have hb := normalized_objective_teacher_distance_lower O a P lambda p hlambda hp hm.1 teacher teacher
  have hm' : c ≤ lambda*(variationTransport P 0)^(p/2-1)*sphericalRadialWeight P.radius -
      fittingCurvatureConstant d O a * Real.sqrt (sphericalWassersteinSq (P.measure 0) teacher+
        sphericalWassersteinSq (P.measure 1) teacher) := by
    simpa only [hradius,mul_assoc,mul_left_comm,mul_comm] using hm.2
  exact (mul_le_mul_of_nonneg_right hm' (variationEnergy_nonneg P)).trans hb

/-- The same uniform neighborhood and margin also describe the EXP second
variation, by the proved equality of the fully integrated objectives' jets. -/
theorem spherical_teacher_neighborhood_curvature {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (radius : Real)
    (teacher : Measure (UnitSphere d)) (hteacher : TwoCapClass pole radius teacher)
    (lambda p : Real) (hlambda : 0 < lambda) (hp : 2 < p)
    (hZo : 0 < productAntipodalTransportSq pole teacher teacher) :
    ∃ rho c : Real, 0 < rho ∧ 0 < c ∧
      ∀ P : SphericalVariation d, P.pole = pole → P.radius = radius →
        sphericalWassersteinSq (P.measure 0) teacher+
          sphericalWassersteinSq (P.measure 1) teacher < rho^2 →
        c*variationEnergy P ≤
          deriv (deriv (variationObjective O a P lambda p teacher teacher)) 0 := by
  letI : IsProbabilityMeasure teacher := hteacher.probability
  obtain ⟨rho,c,hrho,hc,hh⟩ := normalized_teacher_neighborhood_curvature O a pole radius
    teacher hteacher lambda p hlambda hp hZo
  refine ⟨rho,c,hrho,hc,?_⟩
  intro P hpole hradius hnear
  have hb := hh P hpole hradius hnear
  rwa [(variationRetractedObjective_derivatives_eq_exp O a P lambda p hlambda hp teacher teacher).2] at hb

/-- In every nonzero L2 tangent direction the uniform margin is strictly
positive. The zero-energy direction is not incorrectly claimed to be strict. -/
theorem normalized_teacher_neighborhood_positive {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (radius : Real)
    (teacher : Measure (UnitSphere d)) (hteacher : TwoCapClass pole radius teacher)
    (lambda p : Real) (hlambda : 0 < lambda) (hp : 2 < p)
    (hZo : 0 < productAntipodalTransportSq pole teacher teacher) :
    ∃ rho : Real, 0 < rho ∧
      ∀ P : SphericalVariation d, P.pole = pole → P.radius = radius →
        sphericalWassersteinSq (P.measure 0) teacher+
          sphericalWassersteinSq (P.measure 1) teacher < rho^2 → 0 < variationEnergy P →
        0 < deriv (deriv (variationRetractedObjective O a P lambda p teacher teacher)) 0 := by
  obtain ⟨rho,c,hrho,hc,hh⟩ := normalized_teacher_neighborhood_curvature O a pole radius
    teacher hteacher lambda p hlambda hp hZo
  refine ⟨rho,hrho,?_⟩
  intro P hpole hradius hnear hE
  exact (mul_pos hc hE).trans_le (hh P hpole hradius hnear)


/-- The original transverse teacher imbalance itself rules out zero target
transport. This links the hypotheses of the two local results without claiming
that any escaping trajectory enters the resulting teacher neighborhood. -/
theorem imbalanced_teacher_neighborhood_curvature {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (radius : Real)
    (teacher : Measure (UnitSphere d)) (hteacher : TwoCapClass pole radius teacher)
    (e : Weight d) (rvis gamma : Real)
    (himb : TwoSidedTeacherImbalance pole teacher e rvis gamma)
    (lambda p : Real) (hlambda : 0 < lambda) (hp : 2 < p) :
    ∃ rho c : Real, 0 < rho ∧ 0 < c ∧
      ∀ P : SphericalVariation d, P.pole = pole → P.radius = radius →
        sphericalWassersteinSq (P.measure 0) teacher+
          sphericalWassersteinSq (P.measure 1) teacher < rho^2 →
        c*variationEnergy P ≤
          deriv (deriv (variationRetractedObjective O a P lambda p teacher teacher)) 0 :=
  normalized_teacher_neighborhood_curvature O a pole radius teacher hteacher lambda p hlambda hp
    (himb.product_transport_pos radius hteacher)

end PaperFormalization.MatrixFactorization
