import PaperFormalization.MatrixFactorization.SphericalObjectiveGradient

/-! # Pairing the actual objective field with the assigned radial direction

The radial direction is measurable and bounded on the original closed support.
No global continuity across the assigned-pole tie set is used. These are static
identities for the original state; a characteristic dissipation statement needs
an additional derivative exchange along the actual solution.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

theorem fitting_radial_pairing_integrable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (r : Real)
    (mu : Fin 2 → Measure (UnitSphere d)) (hcap : ∀ i, TwoCapClass pole r (mu i))
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (i : Fin 2) :
    Integrable (fun w => inner Real
      (sphericalFittingGradient O a (mu 0) (mu 1) teacher1 teacher2 i w)
      (assignedGradient pole w)) (mu i) := by
  letI : IsProbabilityMeasure (mu 0) := (hcap 0).probability
  letI : IsProbabilityMeasure (mu 1) := (hcap 1).probability
  letI : IsProbabilityMeasure (mu i) := (hcap i).probability
  apply Integrable.of_bound
    (((sphericalFittingGradient_continuous O a (mu 0) (mu 1) teacher1 teacher2 i).measurable.inner
      (assignedGradient_measurable pole)).aestronglyMeasurable)
    (fittingCurvatureConstant d O a * r)
  filter_upwards [Measure.support_mem_ae (μ := mu i)] with w hw
  rw [Real.norm_eq_abs]
  apply (abs_real_inner_le_norm _ _).trans
  apply mul_le_mul
    (sphericalFittingGradient_norm_le O a (mu 0) (mu 1) teacher1 teacher2 i w)
  · rw [assignedGradient_norm_on_support pole r (mu i) (hcap i) w hw]
    exact (assignedPole_distance_lt_cap pole r (hcap i).radius_lt ((hcap i).support_subset hw)).le
  · exact norm_nonneg _
  · exact fittingCurvatureConstant_nonneg d O a

theorem metric_radial_pairing_integrable {d : Nat} (pole : UnitSphere d) (r lambda p : Real)
    (mu : Fin 2 → Measure (UnitSphere d)) (hcap : ∀ i, TwoCapClass pole r (mu i)) (i : Fin 2) :
    Integrable (fun w => inner Real (metricGradient pole lambda p (mu 0) (mu 1) w)
      (assignedGradient pole w)) (mu i) := by
  simp only [metricGradient,real_inner_smul_left,real_inner_self_eq_norm_sq]
  exact (assignedGradient_norm_sq_integrable pole r (mu i) (hcap i)).const_mul _

/-- The exact radial metric pairing is the true transport power, including zero cost. -/
theorem metric_radial_pairing {d : Nat} (pole : UnitSphere d) (r lambda p : Real)
    (mu : Fin 2 → Measure (UnitSphere d)) (hcap : ∀ i, TwoCapClass pole r (mu i)) :
    (∑ i : Fin 2, ∫ w, inner Real (metricGradient pole lambda p (mu 0) (mu 1) w)
      (assignedGradient pole w) ∂mu i) =
    lambda * (productAntipodalTransportSq pole (mu 0) (mu 1))^(p/2-1) *
      productAntipodalTransportSq pole (mu 0) (mu 1) := by
  simp only [metricGradient,real_inner_smul_left,real_inner_self_eq_norm_sq,
    integral_const_mul,Fin.sum_univ_two,
    assignedGradient_energy pole r (mu 0) (hcap 0),
    assignedGradient_energy pole r (mu 1) (hcap 1)]
  unfold productAntipodalTransportSq
  ring

theorem objective_radial_pairing {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (r lambda p : Real)
    (mu : Fin 2 → Measure (UnitSphere d)) (hcap : ∀ i, TwoCapClass pole r (mu i))
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    (∑ i : Fin 2, ∫ w, inner Real
      (sphericalObjectiveGradient O a pole lambda p (mu 0) (mu 1) teacher1 teacher2 i w)
      (assignedGradient pole w) ∂mu i) =
    (∑ i : Fin 2, ∫ w, inner Real
      (sphericalFittingGradient O a (mu 0) (mu 1) teacher1 teacher2 i w)
      (assignedGradient pole w) ∂mu i) +
    lambda * (productAntipodalTransportSq pole (mu 0) (mu 1))^(p/2-1) *
      productAntipodalTransportSq pole (mu 0) (mu 1) := by
  rw [← metric_radial_pairing pole r lambda p mu hcap, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [sphericalObjectiveGradient,inner_add_left]
  exact integral_add (fitting_radial_pairing_integrable O a pole r mu hcap teacher1 teacher2 i)
    (metric_radial_pairing_integrable pole r lambda p mu hcap i)

end PaperFormalization.MatrixFactorization
