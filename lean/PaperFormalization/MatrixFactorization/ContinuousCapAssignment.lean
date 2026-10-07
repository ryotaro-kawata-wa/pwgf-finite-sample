import PaperFormalization.MatrixFactorization.CapPushforward

/-! # Cap labels along continuous paths before a cap exit

A path in the union of two separated open caps remains in its initial cap.
This is a connectedness consequence, not an assumed label equation. Applied
on the original closed support, it yields the existing cap-assignment
predicate and exact half masses for measurable pushforwards. No joint or
global spatial continuity is assumed, and no global flow is constructed.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- A continuous path in the separated cap union retains both initial cap labels. -/
theorem continuous_cap_path_preserves {d : Nat} (pole : UnitSphere d) (r T : Real)
    (w : Real → UnitSphere d) (hr : r < Real.pi/2) (hT : 0 ≤ T)
    (hc : ContinuousOn w (Icc 0 T))
    (hcap : ∀ t ∈ Icc 0 T, w t ∈ sphericalCap pole r ∪ sphericalCap (reflect pole) r)
    (t : Real) (ht : t ∈ Icc 0 T) :
    (w 0 ∈ sphericalCap pole r → w t ∈ sphericalCap pole r) ∧
      (w 0 ∈ sphericalCap (reflect pole) r → w t ∈ sphericalCap (reflect pole) r) := by
  have hi : w '' Icc (0 : Real) T ⊆ sphericalCap pole r ∪ sphericalCap (reflect pole) r := by
    rintro _ ⟨s,hs,rfl⟩
    exact hcap s hs
  have hd := Set.disjoint_left.mp (sphericalCap_disjoint pole r hr)
  have hn := (isPreconnected_Icc.image w hc).subset_or_subset
    (sphericalCap_isOpen pole r) (sphericalCap_isOpen (reflect pole) r)
    (sphericalCap_disjoint pole r hr) hi
  rcases hn with hp | hm
  · have h0 := hp (mem_image_of_mem w ⟨le_rfl,hT⟩)
    have hnow := hp (mem_image_of_mem w ht)
    exact ⟨fun _ => hnow,fun hh => (hd h0 hh).elim⟩
  · have h0 := hm (mem_image_of_mem w ⟨le_rfl,hT⟩)
    have hnow := hm (mem_image_of_mem w ht)
    exact ⟨fun hh => (hd hh h0).elim,fun _ => hnow⟩

/-- The literal selected pole is constant on the whole given interval. -/
theorem continuous_cap_path_assignedPole {d : Nat} (pole : UnitSphere d) (r T : Real)
    (w : Real → UnitSphere d) (hr : r < Real.pi/2) (hT : 0 ≤ T)
    (hc : ContinuousOn w (Icc 0 T))
    (hcap : ∀ t ∈ Icc 0 T, w t ∈ sphericalCap pole r ∪ sphericalCap (reflect pole) r)
    (t : Real) (ht : t ∈ Icc 0 T) : assignedPole pole (w t) = assignedPole pole (w 0) := by
  have hp := continuous_cap_path_preserves pole r T w hr hT hc hcap t ht
  rcases hcap 0 ⟨le_rfl,hT⟩ with h0 | h0
  · rw [assignedPole_positive pole r hr (hp.1 h0),assignedPole_positive pole r hr h0]
  · rw [assignedPole_negative pole r hr (hp.2 h0),assignedPole_negative pole r hr h0]

/-- Cap assignment on the original support follows from the original time
curves, their initial identity, and membership in the two-cap union. -/
theorem TwoCapClass.preserves_of_continuous_paths {d : Nat} {pole : UnitSphere d} {r : Real}
    {mu : Measure (UnitSphere d)} (hcap : TwoCapClass pole r mu)
    (Phi : Real → UnitSphere d → UnitSphere d) (T : Real) (hT : 0 ≤ T)
    (hzero : ∀ w ∈ mu.support, Phi 0 w = w)
    (hc : ∀ w ∈ mu.support, ContinuousOn (fun t => Phi t w) (Icc 0 T))
    (hinside : ∀ w ∈ mu.support, ∀ t ∈ Icc 0 T,
      Phi t w ∈ sphericalCap pole r ∪ sphericalCap (reflect pole) r)
    (t : Real) (ht : t ∈ Icc 0 T) : PreservesCapAssignment pole r mu (Phi t) := by
  intro w hw
  simpa only [hzero w hw] using
    continuous_cap_path_preserves pole r T (fun s => Phi s w) hcap.radius_lt hT
      (hc w hw) (hinside w hw) t ht

/-- The two exact half masses follow for the original pushed measure using
only measurability of the current map. A closed-support cap statement is not
inferred from measurability alone. -/
theorem TwoCapClass.map_half_masses_of_continuous_paths {d : Nat} {pole : UnitSphere d} {r : Real}
    {mu : Measure (UnitSphere d)} (hcap : TwoCapClass pole r mu)
    (Phi : Real → UnitSphere d → UnitSphere d) (T : Real) (hT : 0 ≤ T)
    (hzero : ∀ w ∈ mu.support, Phi 0 w = w)
    (hc : ∀ w ∈ mu.support, ContinuousOn (fun t => Phi t w) (Icc 0 T))
    (hinside : ∀ w ∈ mu.support, ∀ t ∈ Icc 0 T,
      Phi t w ∈ sphericalCap pole r ∪ sphericalCap (reflect pole) r)
    (t : Real) (ht : t ∈ Icc 0 T) (hm : Measurable (Phi t)) :
    (mu.map (Phi t)) (sphericalCap pole r) = (1/2 : ENNReal) ∧
      (mu.map (Phi t)) (sphericalCap (reflect pole) r) = (1/2 : ENNReal) := by
  have hp := hcap.preserves_of_continuous_paths Phi T hT hzero hc hinside t ht
  have hd := Set.disjoint_left.mp (sphericalCap_disjoint pole r hcap.radius_lt)
  have hpos : Phi t ⁻¹' sphericalCap pole r =ᵐ[mu] sphericalCap pole r := by
    filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
    apply propext
    change Phi t w ∈ sphericalCap pole r ↔ w ∈ sphericalCap pole r
    rcases hcap.support_subset hw with hwpos | hwneg
    · have hfw := (hp w hw).1 hwpos
      simp only [hwpos,hfw]
    · have hfw := (hp w hw).2 hwneg
      have hnw : w ∉ sphericalCap pole r := fun he => hd he hwneg
      have hnf : Phi t w ∉ sphericalCap pole r := fun he => hd he hfw
      simp only [hnw,hnf]
  have hneg : Phi t ⁻¹' sphericalCap (reflect pole) r =ᵐ[mu] sphericalCap (reflect pole) r := by
    filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
    apply propext
    change Phi t w ∈ sphericalCap (reflect pole) r ↔ w ∈ sphericalCap (reflect pole) r
    rcases hcap.support_subset hw with hwpos | hwneg
    · have hfw := (hp w hw).1 hwpos
      have hnw : w ∉ sphericalCap (reflect pole) r := fun he => hd hwpos he
      have hnf : Phi t w ∉ sphericalCap (reflect pole) r := fun he => hd hfw he
      simp only [hnw,hnf]
    · have hfw := (hp w hw).2 hwneg
      simp only [hwneg,hfw]
  constructor
  · rw [Measure.map_apply hm (sphericalCap_isOpen pole r).measurableSet,measure_congr hpos]
    exact hcap.positive_mass
  · rw [Measure.map_apply hm (sphericalCap_isOpen (reflect pole) r).measurableSet,measure_congr hneg]
    exact hcap.negative_mass

/-- Continuity on the original closed support is enough to make its image
compact and to contain the complete support of the measurable pushforward. -/
theorem sphere_support_map_subset_image_of_continuousOn {d : Nat}
    (mu : Measure (UnitSphere d)) (f : UnitSphere d → UnitSphere d)
    (hm : Measurable f) (hc : ContinuousOn f mu.support) :
    (mu.map f).support ⊆ f '' mu.support := by
  have hcompact : IsCompact (f '' mu.support) :=
    (Measure.isClosed_support (μ := mu)).isCompact.image_of_continuousOn hc
  have hae : ∀ᵐ y ∂mu.map f, y ∈ f '' mu.support := by
    apply (ae_map_iff hm.aemeasurable hcompact.measurableSet).2
    filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
    exact ⟨w,hw,rfl⟩
  exact Measure.support_subset_of_isClosed hcompact.isClosed hae

/-- The full original cap class is preserved using continuity only on its
original support. Cap assignment may be supplied by the preceding path theorem. -/
theorem TwoCapClass.map_on_support {d : Nat} {pole : UnitSphere d} {r : Real}
    {mu : Measure (UnitSphere d)} (hcap : TwoCapClass pole r mu)
    (f : UnitSphere d → UnitSphere d) (hm : Measurable f)
    (hc : ContinuousOn f mu.support) (hp : PreservesCapAssignment pole r mu f) :
    TwoCapClass pole r (mu.map f) := by
  letI : IsProbabilityMeasure mu := hcap.probability
  have hd := Set.disjoint_left.mp (sphericalCap_disjoint pole r hcap.radius_lt)
  have hpos : f ⁻¹' sphericalCap pole r =ᵐ[mu] sphericalCap pole r := by
    filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
    apply propext
    change f w ∈ sphericalCap pole r ↔ w ∈ sphericalCap pole r
    rcases hcap.support_subset hw with hwpos | hwneg
    · have hfw := (hp w hw).1 hwpos
      simp only [hwpos,hfw]
    · have hfw := (hp w hw).2 hwneg
      have hnw : w ∉ sphericalCap pole r := fun he => hd he hwneg
      have hnf : f w ∉ sphericalCap pole r := fun he => hd he hfw
      simp only [hnw,hnf]
  have hneg : f ⁻¹' sphericalCap (reflect pole) r =ᵐ[mu] sphericalCap (reflect pole) r := by
    filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
    apply propext
    change f w ∈ sphericalCap (reflect pole) r ↔ w ∈ sphericalCap (reflect pole) r
    rcases hcap.support_subset hw with hwpos | hwneg
    · have hfw := (hp w hw).1 hwpos
      have hnw : w ∉ sphericalCap (reflect pole) r := fun he => hd hwpos he
      have hnf : f w ∉ sphericalCap (reflect pole) r := fun he => hd hfw he
      simp only [hnw,hnf]
    · have hfw := (hp w hw).2 hwneg
      simp only [hwneg,hfw]
  refine ⟨hcap.radius_pos,hcap.radius_lt,
    Measure.isProbabilityMeasure_map hm.aemeasurable,?_,?_,?_⟩
  · intro y hy
    obtain ⟨w,hw,rfl⟩ := sphere_support_map_subset_image_of_continuousOn mu f hm hc hy
    rcases hcap.support_subset hw with hwpos | hwneg
    · exact Or.inl ((hp w hw).1 hwpos)
    · exact Or.inr ((hp w hw).2 hwneg)
  · rw [Measure.map_apply hm (sphericalCap_isOpen pole r).measurableSet,measure_congr hpos]
    exact hcap.positive_mass
  · rw [Measure.map_apply hm (sphericalCap_isOpen (reflect pole) r).measurableSet,measure_congr hneg]
    exact hcap.negative_mass

/-- The complete current cap class follows from original-support path and
spatial continuity, without assuming a cap condition on the current measure. -/
theorem TwoCapClass.map_of_continuous_paths {d : Nat} {pole : UnitSphere d} {r : Real}
    {mu : Measure (UnitSphere d)} (hcap : TwoCapClass pole r mu)
    (Phi : Real → UnitSphere d → UnitSphere d) (T : Real) (hT : 0 ≤ T)
    (hzero : ∀ w ∈ mu.support, Phi 0 w = w)
    (hc : ∀ w ∈ mu.support, ContinuousOn (fun t => Phi t w) (Icc 0 T))
    (hinside : ∀ w ∈ mu.support, ∀ t ∈ Icc 0 T,
      Phi t w ∈ sphericalCap pole r ∪ sphericalCap (reflect pole) r)
    (t : Real) (ht : t ∈ Icc 0 T) (hm : Measurable (Phi t))
    (hs : ContinuousOn (Phi t) mu.support) :
    TwoCapClass pole r (mu.map (Phi t)) :=
  hcap.map_on_support (Phi t) hm hs
    (hcap.preserves_of_continuous_paths Phi T hT hzero hc hinside t ht)

/-- The actual infimum over all couplings equals the assigned cost after this
supported continuous transport. Neither current half masses nor an optimality
formula are inputs, and continuity outside the original support is unnecessary. -/
theorem fixed_assignment_of_continuous_paths {d : Nat} {pole : UnitSphere d} {r : Real}
    {mu : Measure (UnitSphere d)} (hcap : TwoCapClass pole r mu)
    (Phi : Real → UnitSphere d → UnitSphere d) (T : Real) (hT : 0 ≤ T)
    (hzero : ∀ w ∈ mu.support, Phi 0 w = w)
    (hc : ∀ w ∈ mu.support, ContinuousOn (fun t => Phi t w) (Icc 0 T))
    (hinside : ∀ w ∈ mu.support, ∀ t ∈ Icc 0 T,
      Phi t w ∈ sphericalCap pole r ∪ sphericalCap (reflect pole) r)
    (t : Real) (ht : t ∈ Icc 0 T) (hm : Measurable (Phi t))
    (hs : ContinuousOn (Phi t) mu.support) :
    sphericalWassersteinSq (mu.map (Phi t)) (antipodalMeasure pole) =
      2*∫ w, assignedCost pole (Phi t w) ∂mu := by
  have hnew := hcap.map_of_continuous_paths Phi T hT hzero hc hinside t ht hm hs
  rw [sphericalWassersteinSq_antipodal pole r (mu.map (Phi t)) hnew,
    integral_map hm.aemeasurable (assignedCost_continuous pole).aestronglyMeasurable]

end PaperFormalization.MatrixFactorization
