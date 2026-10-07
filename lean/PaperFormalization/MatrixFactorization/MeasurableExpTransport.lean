import PaperFormalization.MatrixFactorization.OneSidedDerivativeBounds

/-! # MF24: the actual transport variation for bounded measurable tangents

Verification status and conditional scope: see `MF24_VALIDATION.md`. The map is the existing spherical EXP, now with a Borel
bounded field instead of a globally continuous field. Uniform short times
come from the stated bound on the test, not from cap confinement. The law is
its literal pushforward, and the transport cost remains the infimum over all
couplings. A derivative, when used below, is an explicit first-variation input.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable def BoundedTangentTest.expMap {d : Nat} (V : BoundedTangentTest d)
    (t : Real) : UnitSphere d → UnitSphere d :=
  sphericalExpFamily V.field V.tangent t

@[simp] theorem BoundedTangentTest.expMap_zero {d : Nat} (V : BoundedTangentTest d)
    (w : UnitSphere d) : V.expMap 0 w = w := sphericalExpFamily_zero V.field V.tangent w

theorem BoundedTangentTest.expMap_measurable {d : Nat} (V : BoundedTangentTest d)
    (t : Real) : Measurable (V.expMap t) := by
  have hv : Measurable (fun w : UnitSphere d => t • V.field w) :=
    V.measurable_field.const_smul t
  have hpair : Measurable (fun w : UnitSphere d => (w, t • V.field w)) :=
    measurable_id.prodMk hv
  have hm := (sphereExpVector_continuous d).measurable.comp hpair
  exact hm.subtype_mk

theorem BoundedTangentTest.expMap_time_continuous {d : Nat} (V : BoundedTangentTest d)
    (w : UnitSphere d) : Continuous (fun t : Real => V.expMap t w) := by
  exact geodesicPoint_continuous w (V.field w) (V.tangent w)

/-- A single neighborhood works for all labels, with no continuity in the label. -/
theorem BoundedTangentTest.eventually_short {d : Nat} (V : BoundedTangentTest d) :
    ∀ᶠ t in 𝓝 (0 : Real), ∀ w, norm (t • V.field w) < Real.pi := by
  have hc : Continuous (fun t : Real => |t| * V.bound) := continuous_abs.mul continuous_const
  have he : ∀ᶠ t in 𝓝 (0 : Real), |t| * V.bound < Real.pi :=
    hc.continuousAt.eventually (gt_mem_nhds (by simpa using Real.pi_pos))
  filter_upwards [he] with t ht
  intro w
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (V.norm_le w) (abs_nonneg t)).trans_lt ht

noncomputable def BoundedTangentTest.push {d : Nat} (V : BoundedTangentTest d)
    (mu : Measure (UnitSphere d)) (t : Real) : Measure (UnitSphere d) := mu.map (V.expMap t)

@[simp] theorem BoundedTangentTest.push_zero {d : Nat} (V : BoundedTangentTest d)
    (mu : Measure (UnitSphere d)) : V.push mu 0 = mu := by
  have he : V.expMap 0 = id := funext (V.expMap_zero)
  simp only [BoundedTangentTest.push, he, Measure.map_id]

theorem BoundedTangentTest.push_probability {d : Nat} (V : BoundedTangentTest d)
    (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] (t : Real) :
    IsProbabilityMeasure (V.push mu t) :=
  Measure.isProbabilityMeasure_map (V.expMap_measurable t).aemeasurable

/-- This equality is on the original law, for both signs of time and v=0. -/
theorem BoundedTangentTest.displacement_near_zero {d : Nat} (V : BoundedTangentTest d)
    (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu] :
    ∀ᶠ t in 𝓝 (0 : Real),
      sphericalMapDisplacement mu (V.expMap t) = |t| * (∫ w, norm (V.field w) ∂mu) := by
  have hi := V.norm_integrable mu
  filter_upwards [V.eventually_short] with t ht
  unfold sphericalMapDisplacement
  calc
    _ = ∫ w, |t| * norm (V.field w) ∂mu := by
      apply integral_congr_ae
      filter_upwards with w
      have htan : inner Real w.val (t • V.field w) = 0 := by
        simp only [real_inner_smul_right, V.tangent, mul_zero]
      change sphericalDistance (V.expMap t w) w = |t| * norm (V.field w)
      rw [sphericalDistance_comm]
      change sphericalDistance w (sphericalExp w (t • V.field w) htan) = _
      rw [sphericalDistance_exp w (t • V.field w) htan (ht w), norm_smul, Real.norm_eq_abs]
    _ = _ := integral_const_mul _ _

theorem BoundedTangentTest.transport_upper_near_zero {d : Nat} (V : BoundedTangentTest d)
    (mu nu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    ∀ᶠ t in 𝓝 (0 : Real),
      sphericalWassersteinSq (V.push mu t) nu ≤ sphericalWassersteinSq mu nu +
        (2*Real.pi*(∫ w, norm (V.field w) ∂mu))*|t| := by
  filter_upwards [V.displacement_near_zero mu] with t ht
  have hh := sphericalWassersteinSq_map_le mu nu (V.expMap t) (V.expMap_measurable t)
  rw [ht] at hh
  simpa only [BoundedTangentTest.push, mul_assoc, mul_comm, mul_left_comm] using hh

/-- An existing variational derivative is L1-bounded without a classical potential. -/
theorem BoundedTangentTest.transport_derivative_bound {d : Nat} (V : BoundedTangentTest d)
    (mu nu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (D : Real)
    (hd : HasDerivAt (fun t => sphericalWassersteinSq (V.push mu t) nu) D 0) :
    |D| ≤ 2*Real.pi*(∫ w, norm (V.field w) ∂mu) := by
  apply derivative_abs_le_of_upper_cone hd
  simpa only [V.push_zero] using V.transport_upper_near_zero mu nu

end PaperFormalization.MatrixFactorization
