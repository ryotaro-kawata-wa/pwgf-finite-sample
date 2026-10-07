import PaperFormalization.MatrixFactorization.TeacherImbalance
import PaperFormalization.MatrixFactorization.SphericalRegularizerFlat

/-! # Original teacher imbalance excludes zero antipodal transport

This consequence is independent of the activation coefficients. It links the
same original teacher measure used by the escape theorem to the positive
teacher-distance hypothesis of the neighborhood curvature theorem.
-/
open MeasureTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Both assigned poles have zero transverse projection. -/
theorem teacherTransverseProjection_assigned {d : Nat} (pole w : UnitSphere d) :
    teacherTransverseProjection pole (assignedPole pole w) = 0 := by
  rcases assignedPole_mem pole w with he | he
  · simp only [he, teacherTransverseProjection, real_inner_self_eq_norm_sq,
      unitSphere_norm, one_pow, one_smul, sub_self]
  · simp only [he, teacherTransverseProjection, reflect_val, inner_neg_right,
      real_inner_self_eq_norm_sq, unitSphere_norm, one_pow, neg_smul,
      one_smul, sub_self]

/-- True zero transport forces every transverse latitude slice to vanish. -/
theorem zeroTransport_slicedTransverseMoment {d : Nat} (pole : UnitSphere d) (r : Real)
    (teacher : Measure (UnitSphere d)) (hcap : TwoCapClass pole r teacher)
    (hz : sphericalWassersteinSq teacher (antipodalMeasure pole) = 0) (E : Set Real) :
    slicedTransverseMoment pole teacher E = 0 := by
  have he := zeroTransport_ae_assigned pole r teacher hcap hz
  have hp : ∀ᵐ w ∂teacher, teacherTransverseProjection pole w = 0 := by
    filter_upwards [he] with w hw
    rw [hw]
    exact teacherTransverseProjection_assigned pole w
  unfold slicedTransverseMoment
  calc
    _ = ∫ _ in (twoSidedLatitude pole) ⁻¹' E, (0 : Weight d) ∂teacher :=
      integral_congr_ae (ae_restrict_of_ae hp)
    _ = 0 := by simp

/-- The source's strict visible slice margin implies positive true transport. -/
theorem TwoSidedTeacherImbalance.transport_pos {d : Nat} {pole : UnitSphere d}
    {teacher : Measure (UnitSphere d)} {e : Weight d} {rvis gamma : Real}
    (himb : TwoSidedTeacherImbalance pole teacher e rvis gamma)
    (r : Real) (hcap : TwoCapClass pole r teacher) :
    0 < sphericalWassersteinSq teacher (antipodalMeasure pole) := by
  letI : IsProbabilityMeasure teacher := hcap.probability
  have hn := sphericalWassersteinSq_nonneg teacher (antipodalMeasure pole)
  apply lt_of_le_of_ne hn
  intro he
  have hv := himb.visible_lower
  rw [zeroTransport_slicedTransverseMoment pole r teacher hcap he.symm, inner_zero_right] at hv
  exact (not_le_of_gt himb.margin_pos) hv

/-- The same-density teacher has strictly positive product target distance. -/
theorem TwoSidedTeacherImbalance.product_transport_pos {d : Nat} {pole : UnitSphere d}
    {teacher : Measure (UnitSphere d)} {e : Weight d} {rvis gamma : Real}
    (himb : TwoSidedTeacherImbalance pole teacher e rvis gamma)
    (r : Real) (hcap : TwoCapClass pole r teacher) :
    0 < productAntipodalTransportSq pole teacher teacher := by
  exact add_pos (himb.transport_pos r hcap) (himb.transport_pos r hcap)

end PaperFormalization.MatrixFactorization
