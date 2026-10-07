import PaperFormalization.MatrixFactorization.FixedAssignment

/-! # MF02e: stability under small spherical pushforwards

The final local statement does NOT assume that sufficiently small perturbations
preserve caps. It derives that property from joint continuity, the identity at
parameter zero, compact original support, and the separated open caps.
The same source measure is retained when the cost is pulled back for variation.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Pointwise cap preservation only needs to hold on the ORIGINAL closed support. -/
def PreservesCapAssignment {d : Nat} (a : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (f : UnitSphere d → UnitSphere d) : Prop :=
  ∀ w ∈ mu.support,
    (w ∈ sphericalCap a r → f w ∈ sphericalCap a r) ∧
    (w ∈ sphericalCap (reflect a) r → f w ∈ sphericalCap (reflect a) r)

/-- On a compact domain, the mapped support lies in the actual compact support image. -/
theorem sphere_support_map_subset {d : Nat} (mu : Measure (UnitSphere d))
    (f : UnitSphere d → UnitSphere d) (hf : Continuous f) :
    (mu.map f).support ⊆ f '' mu.support := by
  have hc : IsCompact (f '' mu.support) :=
    (Measure.isClosed_support (μ := mu)).isCompact.image hf
  have hae : ∀ᵐ y ∂mu.map f, y ∈ f '' mu.support := by
    apply (ae_map_iff hf.measurable.aemeasurable
      (p := fun y => y ∈ f '' mu.support) hc.measurableSet).2
    filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
    exact ⟨w, hw, rfl⟩
  exact Measure.support_subset_of_isClosed hc.isClosed hae

/-- Neither the closed-support condition nor the exact half masses are dropped. -/
theorem TwoCapClass.map {d : Nat} {a : UnitSphere d} {r : Real}
    {mu : Measure (UnitSphere d)} (h : TwoCapClass a r mu)
    (f : UnitSphere d → UnitSphere d) (hf : Continuous f)
    (hp : PreservesCapAssignment a r mu f) : TwoCapClass a r (mu.map f) := by
  letI : IsProbabilityMeasure mu := h.probability
  have hd := Set.disjoint_left.mp (sphericalCap_disjoint a r h.radius_lt)
  have hpos : f ⁻¹' sphericalCap a r =ᵐ[mu] sphericalCap a r := by
    filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
    apply propext
    change f w ∈ sphericalCap a r ↔ w ∈ sphericalCap a r
    rcases h.support_subset hw with hwpos | hwneg
    · have hfw := (hp w hw).1 hwpos
      simp [hwpos, hfw]
    · have hfw := (hp w hw).2 hwneg
      have hnw : w ∉ sphericalCap a r := fun he => hd he hwneg
      have hnf : f w ∉ sphericalCap a r := fun he => hd he hfw
      simp [hnw, hnf]
  have hneg : f ⁻¹' sphericalCap (reflect a) r =ᵐ[mu] sphericalCap (reflect a) r := by
    filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
    apply propext
    change f w ∈ sphericalCap (reflect a) r ↔ w ∈ sphericalCap (reflect a) r
    rcases h.support_subset hw with hwpos | hwneg
    · have hfw := (hp w hw).1 hwpos
      have hnw : w ∉ sphericalCap (reflect a) r := fun he => hd hwpos he
      have hnf : f w ∉ sphericalCap (reflect a) r := fun he => hd hfw he
      simp [hnw, hnf]
    · have hfw := (hp w hw).2 hwneg
      simp [hwneg, hfw]
  refine ⟨h.radius_pos, h.radius_lt,
    Measure.isProbabilityMeasure_map hf.measurable.aemeasurable, ?_, ?_, ?_⟩
  · intro y hy
    rcases sphere_support_map_subset mu f hf hy with ⟨w, hw, rfl⟩
    rcases h.support_subset hw with hwp | hwn
    · exact Or.inl ((hp w hw).1 hwp)
    · exact Or.inr ((hp w hw).2 hwn)
  · rw [Measure.map_apply hf.measurable (sphericalCap_isOpen a r).measurableSet,
      measure_congr hpos]
    exact h.positive_mass
  · rw [Measure.map_apply hf.measurable (sphericalCap_isOpen (reflect a) r).measurableSet,
      measure_congr hneg]
    exact h.negative_mass

/-- Exact cost after a cap-preserving pushforward, expressed on the original measure. -/
theorem fixed_assignment_pushforward {d : Nat} (a : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (h : TwoCapClass a r mu)
    (f : UnitSphere d → UnitSphere d) (hf : Continuous f)
    (hp : PreservesCapAssignment a r mu f) :
    Integrable (fun w => assignedCost a (f w)) mu ∧
    sphericalWassersteinSq (mu.map f) (antipodalMeasure a) =
      2 * ∫ w, assignedCost a (f w) ∂mu := by
  letI : IsProbabilityMeasure mu := h.probability
  have hm := h.map f hf hp
  refine ⟨sphere_integrable mu _ ((assignedCost_continuous a).comp hf), ?_⟩
  rw [sphericalWassersteinSq_antipodal a r (mu.map f) hm,
    integral_map hf.measurable.aemeasurable (assignedCost_continuous a).aestronglyMeasurable]

/-- A single neighborhood works for the entire compact support, not a point-dependent one. -/
theorem TwoCapClass.eventually_preserves {d : Nat} {a : UnitSphere d} {r : Real}
    {mu : Measure (UnitSphere d)} (h : TwoCapClass a r mu)
    (f : Real → UnitSphere d → UnitSphere d)
    (hf : Continuous (fun z : Real × UnitSphere d => f z.1 z.2))
    (hzero : ∀ w, f 0 w = w) :
    ∀ᶠ t in 𝓝 (0 : Real), PreservesCapAssignment a r mu (f t) := by
  have hd := Set.disjoint_left.mp (sphericalCap_disjoint a r h.radius_lt)
  change ∀ᶠ t in 𝓝 (0 : Real), ∀ w ∈ mu.support,
    (w ∈ sphericalCap a r → f t w ∈ sphericalCap a r) ∧
    (w ∈ sphericalCap (reflect a) r → f t w ∈ sphericalCap (reflect a) r)
  apply (Measure.isClosed_support (μ := mu)).isCompact.eventually_forall_of_forall_eventually
  intro w hw
  rcases h.support_subset hw with hwp | hwn
  · have hwnear : ∀ᶠ z : Real × UnitSphere d in 𝓝 (0, w), z.2 ∈ sphericalCap a r :=
      continuous_snd.tendsto (0, w) ((sphericalCap_isOpen a r).mem_nhds hwp)
    have hfnear : ∀ᶠ z : Real × UnitSphere d in 𝓝 (0, w), f z.1 z.2 ∈ sphericalCap a r :=
      hf.tendsto (0, w) ((sphericalCap_isOpen a r).mem_nhds (by simpa [hzero] using hwp))
    filter_upwards [hwnear, hfnear] with z hzw hzf
    exact ⟨fun _ => hzf, fun hn => (hd hzw hn).elim⟩
  · have hwnear : ∀ᶠ z : Real × UnitSphere d in 𝓝 (0, w), z.2 ∈ sphericalCap (reflect a) r :=
      continuous_snd.tendsto (0, w) ((sphericalCap_isOpen (reflect a) r).mem_nhds hwn)
    have hfnear : ∀ᶠ z : Real × UnitSphere d in 𝓝 (0, w), f z.1 z.2 ∈ sphericalCap (reflect a) r :=
      hf.tendsto (0, w) ((sphericalCap_isOpen (reflect a) r).mem_nhds (by simpa [hzero] using hwn))
    filter_upwards [hwnear, hfnear] with z hzw hzf
    exact ⟨fun hp => (hd hp hzw).elim, fun _ => hzf⟩

/-- The source's final local-pushforward sentence follows from continuity at the identity. -/
theorem fixed_assignment_local_pushforward {d : Nat} (a : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (h : TwoCapClass a r mu)
    (f : Real → UnitSphere d → UnitSphere d)
    (hf : Continuous (fun z : Real × UnitSphere d => f z.1 z.2))
    (hzero : ∀ w, f 0 w = w) :
    ∀ᶠ t in 𝓝 (0 : Real),
      TwoCapClass a r (mu.map (f t)) ∧
      Integrable (fun w => assignedCost a (f t w)) mu ∧
      sphericalWassersteinSq (mu.map (f t)) (antipodalMeasure a) =
        2 * ∫ w, assignedCost a (f t w) ∂mu := by
  filter_upwards [h.eventually_preserves f hf hzero] with t ht
  have hft : Continuous (f t) := hf.comp (continuous_const.prodMk continuous_id)
  exact ⟨h.map (f t) hft ht, fixed_assignment_pushforward a r mu h (f t) hft ht⟩

end PaperFormalization.MatrixFactorization
