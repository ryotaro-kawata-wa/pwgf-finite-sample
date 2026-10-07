import PaperFormalization.MatrixFactorization.SphereFirstVariation
import PaperFormalization.MatrixFactorization.ExactSupportRadius

/-! # MF24: exact assignment after merely measurable bounded perturbations

Verification status and conditional scope: see `MF24_VALIDATION.md`. The new map need not be continuous or invertible. Its
assigned-pole marginal is proved to be the balanced target; a graph plan then
attains the lower bound for EVERY coupling. This is not a definition of the
Wasserstein cost by the desired formula. The original closed-support cap
condition is used to obtain one common short time and frozen pole labels.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def balancedAssignedCoupling {d : Nat} (pole : UnitSphere d)
    (mu : Measure (UnitSphere d))
    (hm : mu.map (assignedPole pole) = antipodalMeasure pole) :
    SphericalCoupling mu (antipodalMeasure pole) where
  measure := (graphSphericalCoupling mu (assignedPole pole) (assignedPole_measurable pole)).measure
  first_marginal := (graphSphericalCoupling mu (assignedPole pole)
    (assignedPole_measurable pole)).first_marginal
  second_marginal := (graphSphericalCoupling mu (assignedPole pole)
    (assignedPole_measurable pole)).second_marginal.trans hm

/-- Balanced nearest-pole mass suffices for exact optimality, even without
asserting continuity of a map that produced mu. -/
theorem balanced_assignment_formula {d : Nat} (pole : UnitSphere d)
    (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    (hm : mu.map (assignedPole pole) = antipodalMeasure pole) :
    sphericalWassersteinSq mu (antipodalMeasure pole) = 2*(∫ w, assignedCost pole w ∂mu) := by
  apply sphericalWassersteinSq_eq_of_attains (balancedAssignedCoupling pole mu hm)
    (2*(∫ w, assignedCost pole w ∂mu))
  · change sphericalTransportCost (graphSphericalCoupling mu (assignedPole pole)
      (assignedPole_measurable pole)) = _
    rw [sphericalTransportCost_graph, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with w
    unfold assignedCost
    ring
  · exact assignedPole_lower_bound pole mu

/-- The exact half masses are transported by an AE label identity on the
original measure, not by an assumed cap class of the new law. -/
theorem assignedPole_mass_of_measurable_map {d : Nat} (pole : UnitSphere d)
    (r : Real) (mu : Measure (UnitSphere d)) (hc : TwoCapClass pole r mu)
    (f : UnitSphere d → UnitSphere d) (hf : Measurable f)
    (he : ∀ᵐ w ∂mu, assignedPole pole (f w) = assignedPole pole w) :
    (mu.map f).map (assignedPole pole) = antipodalMeasure pole := by
  rw [Measure.map_map (assignedPole_measurable pole) hf]
  calc
    _ = mu.map (assignedPole pole) := Measure.map_congr he
    _ = antipodalMeasure pole := assignedPole_pushforward pole r mu hc

/-- A common small time keeps every original label in its OWN cap. The proof
uses compactness of the original support, but not spatial continuity of V. -/
theorem BoundedTangentTest.assigned_near_zero {d : Nat} (V : BoundedTangentTest d)
    (pole : UnitSphere d) (r : Real) (mu : Measure (UnitSphere d)) (hc : TwoCapClass pole r mu) :
    ∀ᶠ t in 𝓝 (0 : Real), ∀ w ∈ mu.support,
      sphericalDistance (V.expMap t w) (assignedPole pole w) < r ∧
      assignedPole pole (V.expMap t w) = assignedPole pole w := by
  let R := sphericalSupportRadius pole mu
  have hR := sphericalSupportRadius_cap_properties pole r mu hc
  have htime : ∀ᶠ t in 𝓝 (0 : Real), |t| * V.bound < r-R := by
    have ht : Continuous (fun t : Real => |t| * V.bound) := continuous_abs.mul continuous_const
    exact ht.continuousAt.eventually (gt_mem_nhds (by simpa using sub_pos.mpr hR.2.1))
  filter_upwards [htime, V.eventually_short] with t ht hshort
  intro w hw
  have hd : sphericalDistance (V.expMap t w) w = |t| * norm (V.field w) := by
    have htan : inner Real w.val (t • V.field w) = 0 := by
      simp only [real_inner_smul_right, V.tangent, mul_zero]
    rw [sphericalDistance_comm]
    change sphericalDistance w (sphericalExp w (t • V.field w) htan) = _
    rw [sphericalDistance_exp w (t • V.field w) htan (hshort w), norm_smul, Real.norm_eq_abs]
  have htri := sphericalDistance_triangle (V.expMap t w) w (assignedPole pole w)
  have hrw := hR.2.2.1 w hw
  have hspeed := mul_le_mul_of_nonneg_left (V.norm_le w) (abs_nonneg t)
  have hdist : sphericalDistance (V.expMap t w) (assignedPole pole w) < r := by
    rw [hd] at htri
    change sphericalDistance w (assignedPole pole w) ≤ R at hrw
    linarith
  refine ⟨hdist, ?_⟩
  rcases assignedPole_mem pole w with hp | hn
  · rw [hp] at hdist ⊢
    exact assignedPole_positive pole r hc.radius_lt hdist
  · rw [hn] at hdist ⊢
    exact assignedPole_negative pole r hc.radius_lt hdist

/-- Exact original-measure value formula for the actual perturbed infimum. -/
theorem BoundedTangentTest.halfTransport_frozen_near_zero {d : Nat} (V : BoundedTangentTest d)
    (pole : UnitSphere d) (r : Real) (mu : Measure (UnitSphere d)) (hc : TwoCapClass pole r mu) :
    ∀ᶠ t in 𝓝 (0 : Real),
      halfTransportFunctional (antipodalMeasure pole) (V.push mu t) =
        ∫ w, poleCost (assignedPole pole w) (V.expMap t w) ∂mu := by
  letI : IsProbabilityMeasure mu := hc.probability
  filter_upwards [V.assigned_near_zero pole r mu hc] with t ht
  letI : IsProbabilityMeasure (V.push mu t) := V.push_probability mu t
  have hlabel : ∀ᵐ w ∂mu, assignedPole pole (V.expMap t w) = assignedPole pole w := by
    filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
    exact (ht w hw).2
  have hm := assignedPole_mass_of_measurable_map pole r mu hc (V.expMap t)
    (V.expMap_measurable t) hlabel
  have he := balanced_assignment_formula pole (V.push mu t) hm
  have hv : halfTransportFunctional (antipodalMeasure pole) (V.push mu t) =
      ∫ w, assignedCost pole w ∂V.push mu t := by
    unfold halfTransportFunctional
    rw [he]
    ring
  rw [hv, BoundedTangentTest.push,
    integral_map (V.expMap_measurable t).aemeasurable (assignedCost_continuous pole).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hlabel] with w hw
  simp only [assignedCost, poleCost, hw]

end PaperFormalization.MatrixFactorization
