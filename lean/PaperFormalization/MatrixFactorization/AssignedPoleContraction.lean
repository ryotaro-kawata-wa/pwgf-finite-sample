import PaperFormalization.MatrixFactorization.SphericalContraction
import PaperFormalization.MatrixFactorization.SphericalFeatureGaussian

/-! # Measurable assigned-pole contraction on the original sphere

The nearest-pole distance is at most pi/2 everywhere, so its shortest LOG is
well-defined even at the measurable equatorial tie. No global continuity of
the assignment or radial gradient is asserted. The actual original cap
measures will subsequently supply the source endpoint identities.
-/
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

theorem assignedPole_distance_le_half_pi {d : Nat} (pole w : UnitSphere d) :
    sphericalDistance (assignedPole pole w) w ≤ Real.pi/2 := by
  rw [sphericalDistance_comm, assignedPole_distance, sphericalDistance_reflect_right]
  by_cases h : sphericalDistance w pole ≤ Real.pi/2
  · exact (min_le_left _ _).trans h
  · exact (min_le_right _ _).trans (by linarith)

theorem assignedPole_short {d : Nat} (pole w : UnitSphere d) :
    sphericalDistance (assignedPole pole w) w < Real.pi :=
  (assignedPole_distance_le_half_pi pole w).trans_lt (by linarith [Real.pi_pos])

noncomputable def assignedPoleLog {d : Nat} (pole w : UnitSphere d) : Weight d :=
  sphericalLog (assignedPole pole w) w (assignedPole_short pole w)

theorem assignedPoleLog_measurable {d : Nat} (pole : UnitSphere d) :
    Measurable (assignedPoleLog pole) := by
  have he : assignedPoleLog pole = fun w => -poleGradient w (assignedPole pole w) := by
    funext w
    rw [poleGradient_eq_neg_log w (assignedPole pole w) (assignedPole_short pole w), neg_neg]
    rfl
  rw [he]
  exact ((poleGradient_measurable d).comp (measurable_id.prodMk (assignedPole_measurable pole))).neg

@[simp] theorem assignedPoleLog_norm {d : Nat} (pole w : UnitSphere d) :
    norm (assignedPoleLog pole w) = sphericalDistance (assignedPole pole w) w :=
  sphericalLog_norm _ _ _

theorem assignedPoleLog_tangent {d : Nat} (pole w : UnitSphere d) :
    inner Real (assignedPole pole w).val (assignedPoleLog pole w) = 0 :=
  sphericalLog_tangent _ _ _

noncomputable def assignedContraction {d : Nat} (pole : UnitSphere d) (s : Real)
    (w : UnitSphere d) : UnitSphere d :=
  poleContraction (assignedPole pole w) w (assignedPole_short pole w) s

@[simp] theorem assignedContraction_zero {d : Nat} (pole w : UnitSphere d) :
    assignedContraction pole 0 w = assignedPole pole w := poleContraction_zero _ _ _

@[simp] theorem assignedContraction_one {d : Nat} (pole w : UnitSphere d) :
    assignedContraction pole 1 w = w := poleContraction_one _ _ _

theorem assignedContraction_measurable {d : Nat} (pole : UnitSphere d) :
    Measurable (fun sw : Real × UnitSphere d => assignedContraction pole sw.1 sw.2) := by
  have hy : Measurable (fun sw : Real × UnitSphere d => assignedPole pole sw.2) :=
    (assignedPole_measurable pole).comp measurable_snd
  have hv : Measurable (fun sw : Real × UnitSphere d => assignedPoleLog pole sw.2) :=
    (assignedPoleLog_measurable pole).comp measurable_snd
  have hm := (sphereExpVector_continuous d).measurable.comp
    (hy.prodMk (measurable_fst.smul hv))
  exact hm.subtype_mk

noncomputable def assignedContractionVelocity {d : Nat} (pole : UnitSphere d) (s : Real)
    (w : UnitSphere d) : Weight d :=
  poleContractionVelocity (assignedPole pole w) w (assignedPole_short pole w) s

set_option maxHeartbeats 1000000 in
theorem assignedContractionVelocity_measurable {d : Nat} (pole : UnitSphere d) :
    Measurable (fun sw : Real × UnitSphere d => assignedContractionVelocity pole sw.1 sw.2) := by
  have hc : Continuous (fun p : (UnitSphere d × Weight d) × Real =>
      sphereExpVelocity p.1.1 p.1.2 p.2) := by
    have hv : Continuous (fun p : (UnitSphere d × Weight d) × Real => p.1.2) :=
      continuous_snd.comp continuous_fst
    have ht : Continuous (fun p : (UnitSphere d × Weight d) × Real => p.2*norm p.1.2) :=
      continuous_snd.mul hv.norm
    have hy : Continuous (fun p : (UnitSphere d × Weight d) × Real => p.1.1.val) :=
      continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
    exact ((hv.norm.mul (Real.continuous_sin.comp ht)).neg.smul hy).add
      ((Real.continuous_cos.comp ht).smul hv)
  change Measurable (fun sw : Real × UnitSphere d =>
    sphereExpVelocity (assignedPole pole sw.2) (assignedPoleLog pole sw.2) sw.1)
  exact hc.measurable.comp (f := fun sw : Real × UnitSphere d =>
      ((assignedPole pole sw.2,assignedPoleLog pole sw.2),sw.1))
    ((((assignedPole_measurable pole).comp measurable_snd).prodMk
      ((assignedPoleLog_measurable pole).comp measurable_snd)).prodMk measurable_fst)

@[simp] theorem assignedContractionVelocity_one {d : Nat} (pole w : UnitSphere d) :
    assignedContractionVelocity pole 1 w = assignedGradient pole w :=
  poleContractionVelocity_one _ _ _

theorem assignedContraction_variations {d : Nat} (pole w : UnitSphere d) (s : Real) :
    HasDerivAt (fun t => (assignedContraction pole t w).val)
      (assignedContractionVelocity pole s w) s ∧
    HasDerivAt (fun t => assignedContractionVelocity pole t w)
      (-(sphericalDistance (assignedPole pole w) w)^2 • (assignedContraction pole s w).val) s :=
  ⟨poleContraction_hasDerivAt _ _ _ s, poleContractionVelocity_hasDerivAt _ _ _ s⟩

end PaperFormalization.MatrixFactorization
