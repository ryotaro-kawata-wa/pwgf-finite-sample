import PaperFormalization.MatrixFactorization.AntipodalPotentialGeometry
import PaperFormalization.MatrixFactorization.FixedAssignment

/-! # MF23: dual lower bounds and exact contact for the original transport

Execution records: `MF23_VALIDATION.md`.

Weak duality is proved against every admissible coupling.
Optimality is an equality with the existing infimum, not a replacement cost.
An optimal scalar dual weight is not asserted to exist for arbitrary input
laws in this file. On the original cap class, b=0 is proved optimal, and any
optimal potential contacts the assigned cost on the entire closed support.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable def antipodalOffset {d : Nat} (a : UnitSphere d) (b : Real)
    (y : UnitSphere d) : Real := if y = a then b else -b

theorem antipodalOffset_measurable {d : Nat} (a : UnitSphere d) (b : Real) :
    Measurable (antipodalOffset a b) := by
  exact Measurable.ite (measurableSet_singleton a) measurable_const measurable_const

theorem antipodalOffset_abs {d : Nat} (a y : UnitSphere d) (b : Real) :
    |antipodalOffset a b y| = |b| := by
  unfold antipodalOffset
  split_ifs <;> simp

theorem antipodalOffset_integrable {d : Nat} (a : UnitSphere d) (b : Real)
    (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu] :
    Integrable (antipodalOffset a b) mu := by
  apply Integrable.of_bound (antipodalOffset_measurable a b).aestronglyMeasurable |b|
  exact Eventually.of_forall (fun y => by simp [Real.norm_eq_abs, antipodalOffset_abs])

/-- The gauge is centered for the exact half/half target, not a new mass convention. -/
theorem antipodalOffset_target_integral {d : Nat} (a : UnitSphere d) (b : Real) :
    (integral (antipodalMeasure a) (antipodalOffset a b)) = 0 := by
  have h0 := (antipodalOffset_integrable a b (Measure.dirac a)).smul_measure
    (show (1/2 : ENNReal) ≠ ⊤ by norm_num)
  have h1 := (antipodalOffset_integrable a b (Measure.dirac (reflect a))).smul_measure
    (show (1/2 : ENNReal) ≠ ⊤ by norm_num)
  change integral (((1/2 : ENNReal) • Measure.dirac a) +
    ((1/2 : ENNReal) • Measure.dirac (reflect a))) (antipodalOffset a b) = 0
  rw [integral_add_measure h0 h1]
  simp [antipodalOffset, (unitSphere_ne_reflect a).symm]

/-- Pointwise dual feasibility is needed only at the two target atoms. -/
theorem antipodalPotential_feasible {d : Nat} (a w y : UnitSphere d) (b : Real)
    (hy : y = a ∨ y = reflect a) :
    antipodalPotential a b w + antipodalOffset a b y <= poleCost y w := by
  rcases hy with hy | hy
  · subst y
    have h := antipodalPotential_le_positive a w b
    simp only [antipodalOffset, ite_true]
    linarith
  · subst y
    have h := antipodalPotential_le_negative a w b
    simp only [antipodalOffset, if_neg (unitSphere_ne_reflect a).symm]
    linarith

/-- Weak duality for every joint measure with the original marginals. -/
theorem antipodalPotential_le_coupling_cost {d : Nat} (a : UnitSphere d) (b : Real)
    (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    (gamma : SphericalCoupling mu (antipodalMeasure a)) :
    integral mu (antipodalPotential a b) <= sphericalTransportCost gamma / 2 := by
  have hm : StronglyMeasurable (antipodalPotential a b) :=
    (antipodalPotential_continuous a b).stronglyMeasurable
  have hs : StronglyMeasurable (antipodalOffset a b) :=
    (antipodalOffset_measurable a b).stronglyMeasurable
  have hleft : Integrable (fun z : UnitSphere d × UnitSphere d => antipodalPotential a b z.1)
      gamma.measure := by
    apply (integrable_map_measure hm.aestronglyMeasurable measurable_fst.aemeasurable).mp
    rw [gamma.first_marginal]
    exact antipodalPotential_integrable a b mu
  have hright : Integrable (fun z : UnitSphere d × UnitSphere d => antipodalOffset a b z.2)
      gamma.measure := by
    apply (integrable_map_measure hs.aestronglyMeasurable measurable_snd.aemeasurable).mp
    rw [gamma.second_marginal]
    exact antipodalOffset_integrable a b (antipodalMeasure a)
  have heleft : (integral gamma.measure (fun z => antipodalPotential a b z.1)) =
      integral mu (antipodalPotential a b) := by
    simpa only [gamma.first_marginal] using
      (integral_map (μ := gamma.measure) measurable_fst.aemeasurable hm.aestronglyMeasurable).symm
  have heright : (integral gamma.measure (fun z => antipodalOffset a b z.2)) = 0 := by
    rw [<- integral_map measurable_snd.aemeasurable hs.aestronglyMeasurable, gamma.second_marginal]
    exact antipodalOffset_target_integral a b
  have hi := integral_mono_ae (hleft.add hright)
    ((sphericalTransportCost_integrable gamma).div_const 2) (by
      filter_upwards [sphericalCoupling_ae_target_poles a gamma] with z hz
      exact antipodalPotential_feasible a z.1 z.2 b hz)
  simp only [Pi.add_apply] at hi
  rw [integral_add hleft hright, heleft, heright, add_zero, integral_div] at hi
  exact hi

/-- This lower bound is for the genuine infimum over all couplings. -/
theorem antipodalPotential_le_transport {d : Nat} (a : UnitSphere d) (b : Real)
    (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] :
    2 * integral mu (antipodalPotential a b) <=
      sphericalWassersteinSq mu (antipodalMeasure a) := by
  apply le_csInf (sphericalTransportValues_nonempty mu (antipodalMeasure a))
  rintro _ ⟨gamma, rfl⟩
  linarith [antipodalPotential_le_coupling_cost a b mu gamma]

/-- A source-compatible certificate of scalar dual attainment. -/
def AntipodalPotentialOptimal {d : Nat} (a : UnitSphere d)
    (mu : Measure (UnitSphere d)) (b : Real) : Prop :=
  2 * integral mu (antipodalPotential a b) = sphericalWassersteinSq mu (antipodalMeasure a)

/-- The original fixed-assignment theorem supplies an actual optimal potential. -/
theorem antipodalPotential_zero_optimal {d : Nat} (a : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (hc : TwoCapClass a r mu) :
    AntipodalPotentialOptimal a mu 0 := by
  unfold AntipodalPotentialOptimal
  have he : antipodalPotential a 0 = assignedCost a :=
    funext (antipodalPotential_zero a)
  rw [he]
  exact (sphericalWassersteinSq_antipodal a r mu hc).symm

/-- A locally continuous representative vanishing almost everywhere vanishes
at every support point at which that continuity is available. -/
theorem support_value_zero_of_ae_zero {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] (mu : Measure X) (f : X -> Real)
    {x : X} (hx : x ∈ mu.support) (hf : ContinuousAt f x)
    (hae : f =ᵐ[mu] 0) : f x = 0 := by
  by_contra hne
  have hnhds : {y | f y ≠ 0} ∈ nhds x :=
    hf.preimage_mem_nhds (isOpen_ne.mem_nhds hne)
  have hp := (Measure.mem_support_iff_forall x).mp hx _ hnhds
  have hz : mu {y | f y ≠ 0} = 0 := by
    change (∀ᵐ y ∂mu, f y = 0) at hae
    exact ae_iff.mp hae
  exact (ne_of_gt hp) hz

/-- The discrete assignment is locally constant at every point of either cap. -/
theorem assignedPole_eventually_constant_in_caps {d : Nat} (a w : UnitSphere d)
    (r : Real) (hr : r < Real.pi/2)
    (hw : w ∈ sphericalCap a r ∪ sphericalCap (reflect a) r) :
    ∀ᶠ y in nhds w, assignedPole a y = assignedPole a w := by
  rcases hw with hw | hw
  · filter_upwards [(sphericalCap_isOpen a r).mem_nhds hw] with y hy
    rw [assignedPole_positive a r hr hy, assignedPole_positive a r hr hw]
  · filter_upwards [(sphericalCap_isOpen (reflect a) r).mem_nhds hw] with y hy
    rw [assignedPole_negative a r hr hy, assignedPole_negative a r hr hw]

/-- Complementary slackness for any optimal dual weight and the known assigned plan.
The statement is first derived AE and then extended to the entire closed support. -/
theorem antipodalPotential_contact_on_support {d : Nat} (a : UnitSphere d) (r b : Real)
    (mu : Measure (UnitSphere d)) (hc : TwoCapClass a r mu)
    (ho : AntipodalPotentialOptimal a mu b) {w : UnitSphere d} (hw : w ∈ mu.support) :
    antipodalPotential a b w = poleCost (assignedPole a w) w -
      antipodalOffset a b (assignedPole a w) := by
  letI : IsProbabilityMeasure mu := hc.probability
  let gap := fun x => assignedCost a x - antipodalOffset a b (assignedPole a x) -
    antipodalPotential a b x
  have hoff : Integrable (fun x => antipodalOffset a b (assignedPole a x)) mu := by
    apply Integrable.of_bound
      ((antipodalOffset_measurable a b).comp (assignedPole_measurable a)).aestronglyMeasurable |b|
    exact Eventually.of_forall (fun x => by simp [Real.norm_eq_abs, antipodalOffset_abs])
  have hioff : (integral mu (fun x => antipodalOffset a b (assignedPole a x))) = 0 := by
    rw [<- integral_map (assignedPole_measurable a).aemeasurable
      (antipodalOffset_measurable a b).aestronglyMeasurable,
      assignedPole_pushforward a r mu hc]
    exact antipodalOffset_target_integral a b
  have hgap : Integrable gap mu :=
    ((assignedCost_integrable a mu).sub hoff).sub (antipodalPotential_integrable a b mu)
  have hnonneg : ∀ x, 0 <= gap x := by
    intro x
    have h := antipodalPotential_feasible a x (assignedPole a x) b (assignedPole_mem a x)
    change 0 <= assignedCost a x - _ - _
    change antipodalPotential a b x + antipodalOffset a b (assignedPole a x) <= assignedCost a x at h
    linarith
  have hint : integral mu gap = 0 := by
    dsimp only [gap]
    have hsub := integral_sub ((assignedCost_integrable a mu).sub hoff)
      (antipodalPotential_integrable a b mu)
    simp only [Pi.sub_apply] at hsub
    rw [hsub, integral_sub (assignedCost_integrable a mu) hoff, hioff]
    have hv := sphericalWassersteinSq_antipodal a r mu hc
    unfold AntipodalPotentialOptimal at ho
    linarith
  have hae : gap =ᵐ[mu] 0 := (integral_eq_zero_iff_of_nonneg hnonneg hgap).mp hint
  have he : gap =ᶠ[nhds w] (fun x => poleCost (assignedPole a w) x -
      antipodalOffset a b (assignedPole a w) - antipodalPotential a b x) := by
    filter_upwards [assignedPole_eventually_constant_in_caps a w r hc.radius_lt
      (hc.support_subset hw)] with x hx
    simp only [gap, assignedCost, poleCost, hx]
  have hcont : ContinuousAt gap w := (continuousAt_congr he).mpr
    ((((poleCost_continuous (assignedPole a w)).sub continuous_const).sub
      (antipodalPotential_continuous a b)).continuousAt)
  have hz := support_value_zero_of_ae_zero mu gap hw hcont hae
  change assignedCost a w - _ - _ = 0 at hz
  change antipodalPotential a b w = assignedCost a w - _
  linarith

end PaperFormalization.MatrixFactorization
