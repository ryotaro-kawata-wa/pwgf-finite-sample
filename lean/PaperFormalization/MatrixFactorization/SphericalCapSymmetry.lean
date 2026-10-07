import PaperFormalization.MatrixFactorization.CapPushforward

/-! # Reflected cap states and conjugated spherical pushforwards

Reflection exchanges the original two strict caps. Both the closed support
condition and the exact half masses are retained. The pushforward identity is
an equality of original measures, suitable for reflecting characteristics
once their existence and uniqueness have been established elsewhere.
-/
open MeasureTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

theorem sphericalCap_reflected_preimage {d : Nat} (pole : UnitSphere d) (r : Real) :
    reflect ⁻¹' sphericalCap pole r = sphericalCap (reflect pole) r := by
  ext w
  simpa only [mem_preimage, reflect_reflect] using sphericalCap_reflect_mem (reflect pole) w r

/-- Reflection preserves the source cap class while exchanging its half masses. -/
theorem TwoCapClass.reflected {d : Nat} {pole : UnitSphere d} {r : Real}
    {mu : Measure (UnitSphere d)} (hcap : TwoCapClass pole r mu) :
    TwoCapClass pole r (reflectedMeasure mu) := by
  letI : IsProbabilityMeasure mu := hcap.probability
  refine ⟨hcap.radius_pos,hcap.radius_lt,inferInstance,?_,?_,?_⟩
  · intro y hy
    obtain ⟨w,hw,rfl⟩ := sphere_support_map_subset mu reflect (reflect_continuous d) hy
    rcases hcap.support_subset hw with hp | hn
    · exact Or.inr ((sphericalCap_reflect_mem pole w r).mpr hp)
    · exact Or.inl (by simpa only [reflect_reflect] using
        (sphericalCap_reflect_mem (reflect pole) w r).mpr hn)
  · change (mu.map reflect) (sphericalCap pole r) = _
    rw [Measure.map_apply (reflect_measurable d) (sphericalCap_isOpen pole r).measurableSet,
      sphericalCap_reflected_preimage]
    exact hcap.negative_mass
  · change (mu.map reflect) (sphericalCap (reflect pole) r) = _
    rw [Measure.map_apply (reflect_measurable d) (sphericalCap_isOpen (reflect pole) r).measurableSet,
      sphericalCap_reflected_preimage,reflect_reflect]
    exact hcap.positive_mass

/-- Conjugating the particle map reflects its original pushed measure exactly. -/
theorem reflectedMeasure_map_conjugate {d : Nat} (mu : Measure (UnitSphere d))
    (f : UnitSphere d → UnitSphere d) (hf : Measurable f) :
    (reflectedMeasure mu).map (fun w => reflect (f (reflect w))) =
      reflectedMeasure (mu.map f) := by
  have hg : Measurable (fun w => reflect (f (reflect w))) :=
    (reflect_measurable d).comp (hf.comp (reflect_measurable d))
  unfold reflectedMeasure
  rw [Measure.map_map hg (reflect_measurable d), Measure.map_map (reflect_measurable d) hf]
  congr 1
  funext w
  simp only [Function.comp_apply,reflect_reflect]

end PaperFormalization.MatrixFactorization
