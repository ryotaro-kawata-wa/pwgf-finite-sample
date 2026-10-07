import PaperFormalization.MatrixFactorization.SphericalDistance

/-! # MF02b: the original cap class and the assigned-pole marginal

The closed support condition is retained literally. Its AE consequence is
DERIVED from mathlib Measure.support_mem_ae on the second-countable sphere;
AE cap membership is not silently substituted for the source support condition.
-/
open MeasureTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Exactly the source probability/cap/half-mass restrictions. -/
structure TwoCapClass {d : Nat} (a : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) : Prop where
  radius_pos : 0 < r
  radius_lt : r < Real.pi / 2
  probability : IsProbabilityMeasure mu
  support_subset : mu.support ⊆ sphericalCap a r ∪ sphericalCap (reflect a) r
  positive_mass : mu (sphericalCap a r) = (1/2 : ENNReal)
  negative_mass : mu (sphericalCap (reflect a) r) = (1/2 : ENNReal)

theorem TwoCapClass.ae_caps {d : Nat} {a : UnitSphere d} {r : Real}
    {mu : Measure (UnitSphere d)} (h : TwoCapClass a r mu) :
    ∀ᵐ w ∂mu, w ∈ sphericalCap a r ∪ sphericalCap (reflect a) r := by
  filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
  exact h.support_subset hw

/-- Reflection equivariance is restricted to the separated caps, not the equator. -/
theorem assignedPole_reflect_on_caps {d : Nat} (a : UnitSphere d) (r : Real)
    (hr : r < Real.pi / 2) {w : UnitSphere d}
    (hw : w ∈ sphericalCap a r ∪ sphericalCap (reflect a) r) :
    assignedPole a (reflect w) = reflect (assignedPole a w) := by
  rcases hw with hp | hn
  · have hrw := (sphericalCap_reflect_mem a w r).2 hp
    rw [assignedPole_negative a r hr hrw, assignedPole_positive a r hr hp]
  · have hrw : reflect w ∈ sphericalCap a r := by
      simpa using (sphericalCap_reflect_mem (reflect a) w r).2 hn
    rw [assignedPole_positive a r hr hrw, assignedPole_negative a r hr hn, reflect_reflect]

theorem assignedPole_distance_lt_cap {d : Nat} (a : UnitSphere d) (r : Real)
    (hr : r < Real.pi / 2) {w : UnitSphere d}
    (hw : w ∈ sphericalCap a r ∪ sphericalCap (reflect a) r) :
    sphericalDistance w (assignedPole a w) < r := by
  rcases hw with hp | hn
  · rw [assignedPole_positive a r hr hp]
    exact hp
  · rw [assignedPole_negative a r hr hn]
    exact hn

/-- The target marginal is proved for every measurable set, not just at the atoms. -/
theorem assignedPole_pushforward {d : Nat} (a : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (h : TwoCapClass a r mu) :
    mu.map (assignedPole a) = antipodalMeasure a := by
  classical
  letI : IsProbabilityMeasure mu := h.probability
  have hdis := Set.disjoint_left.mp (sphericalCap_disjoint a r h.radius_lt)
  ext s hs
  rw [Measure.map_apply (assignedPole_measurable a) hs]
  by_cases hp : a ∈ s
  · by_cases hn : reflect a ∈ s
    · have he : assignedPole a ⁻¹' s = Set.univ := by
        ext w
        simp only [Set.mem_preimage, Set.mem_univ, iff_true]
        rcases assignedPole_mem a w with he | he
        · simpa [he] using hp
        · simpa [he] using hn
      rw [he, measure_univ]
      norm_num [antipodalMeasure, Measure.add_apply, Measure.smul_apply, hs, hp, hn,
        ENNReal.inv_two_add_inv_two]
    · have he : assignedPole a ⁻¹' s =ᵐ[mu] sphericalCap a r := by
        filter_upwards [h.ae_caps] with w hw
        apply propext
        change assignedPole a w ∈ s ↔ w ∈ sphericalCap a r
        rcases hw with hw | hw
        · have hew := assignedPole_positive a r h.radius_lt hw
          simp [hew, hp, hw]
        · have hew := assignedPole_negative a r h.radius_lt hw
          have hnot : w ∉ sphericalCap a r := fun hpw => hdis hpw hw
          simp [hew, hn, hnot]
      rw [measure_congr he, h.positive_mass]
      norm_num [antipodalMeasure, Measure.add_apply, Measure.smul_apply, hs, hp, hn]
  · by_cases hn : reflect a ∈ s
    · have he : assignedPole a ⁻¹' s =ᵐ[mu] sphericalCap (reflect a) r := by
        filter_upwards [h.ae_caps] with w hw
        apply propext
        change assignedPole a w ∈ s ↔ w ∈ sphericalCap (reflect a) r
        rcases hw with hw | hw
        · have hew := assignedPole_positive a r h.radius_lt hw
          have hnot : w ∉ sphericalCap (reflect a) r := fun hnw => hdis hw hnw
          simp [hew, hp, hnot]
        · have hew := assignedPole_negative a r h.radius_lt hw
          simp [hew, hn, hw]
      rw [measure_congr he, h.negative_mass]
      norm_num [antipodalMeasure, Measure.add_apply, Measure.smul_apply, hs, hp, hn]
    · have he : assignedPole a ⁻¹' s = ∅ := by
        ext w
        simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
        rcases assignedPole_mem a w with he | he
        · simpa [he] using hp
        · simpa [he] using hn
      rw [he, measure_empty]
      norm_num [antipodalMeasure, Measure.add_apply, Measure.smul_apply, hs, hp, hn]

/-- The second marginal of any coupling will therefore be carried by two poles. -/
theorem antipodalMeasure_ae_poles {d : Nat} (a : UnitSphere d) :
    ∀ᵐ y ∂antipodalMeasure a, y = a ∨ y = reflect a := by
  rw [ae_iff]
  simp [antipodalMeasure, Measure.add_apply, Measure.smul_apply]

/-- Boundedness is available before the transport infimum is introduced. -/
theorem TwoCapClass.assignedCost_bound {d : Nat} {a : UnitSphere d} {r : Real}
    {mu : Measure (UnitSphere d)} (h : TwoCapClass a r mu) :
    ∀ᵐ w ∂mu, 2 * assignedCost a w ≤ r^2 := by
  filter_upwards [h.ae_caps] with w hw
  have hd := assignedPole_distance_lt_cap a r h.radius_lt hw
  have hn := sphericalDistance_nonneg w (assignedPole a w)
  have hh := mul_pos (sub_pos.mpr hd)
    (show 0 < r + sphericalDistance w (assignedPole a w) by linarith [h.radius_pos])
  dsimp only [assignedCost]
  nlinarith

end PaperFormalization.MatrixFactorization
