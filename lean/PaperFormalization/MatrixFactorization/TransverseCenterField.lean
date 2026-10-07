import PaperFormalization.MatrixFactorization.SphericalObjectiveAnnulus
/-! # MF07: the original half-projected transverse field at the antipodal center

The factor one-half is exactly the source normalization. The antipodal measure
is proved to satisfy the original closed-support and half-cap-mass conditions.
Both marginals of the constructed variation use the actual continuous tangent
field; no desired feature derivative or visibility conclusion is a field premise.
-/
open MeasureTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

theorem antipodalMeasure_twoCap {d : Nat} (a : UnitSphere d) {r : Real}
    (hr : 0 < r) (hrpi : r < Real.pi/2) : TwoCapClass a r (antipodalMeasure a) := by
  have hpos := sphericalCap_pole_mem a r hr
  have hneg := sphericalCap_pole_mem (reflect a) r hr
  have hd := Set.disjoint_left.mp (sphericalCap_disjoint a r hrpi)
  have hnpos : reflect a ∉ sphericalCap a r := fun hw => hd hw hneg
  have hpneg : a ∉ sphericalCap (reflect a) r := fun hw => hd hpos hw
  refine ⟨hr, hrpi, inferInstance, ?_, ?_, ?_⟩
  · have hs : (antipodalMeasure a).support ⊆ ({a, reflect a} : Set (UnitSphere d)) :=
      Measure.support_subset_of_isClosed (Set.toFinite ({a, reflect a} : Set (UnitSphere d))).isClosed
        (by
          change ∀ᵐ w ∂antipodalMeasure a, w ∈ ({a, reflect a} : Set (UnitSphere d))
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using antipodalMeasure_ae_poles a)
    intro w hw
    have hp := hs hw
    rcases hp with hp | hp
    · exact Or.inl (hp ▸ hpos)
    · have he : w = reflect a := hp
      exact Or.inr (he ▸ hneg)
  · norm_num [antipodalMeasure, Measure.add_apply, Measure.smul_apply,
      (sphericalCap_isOpen a r).measurableSet, hpos, hnpos]
  · norm_num [antipodalMeasure, Measure.add_apply, Measure.smul_apply,
      (sphericalCap_isOpen (reflect a) r).measurableSet, hneg, hpneg]

theorem integral_antipodalMeasure {d : Nat} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] [CompleteSpace E] (a : UnitSphere d)
    (f : UnitSphere d → E) (hf : Continuous f) :
    ∫ w, f w ∂antipodalMeasure a = (1/2 : Real) • f a + (1/2 : Real) • f (reflect a) := by
  have hi (w : UnitSphere d) : Integrable f ((1/2 : ENNReal) • Measure.dirac w) :=
    (sphere_integrable (Measure.dirac w) f hf).smul_measure (by norm_num)
  rw [antipodalMeasure, integral_add_measure (hi a) (hi (reflect a))]
  norm_num [integral_smul_measure]

noncomputable def transverseHalfField {d : Nat} (s : Weight d) (w : UnitSphere d) : Weight d :=
  (1/2 : Real) • (s - inner Real w.val s • w.val)

theorem transverseHalfField_tangent {d : Nat} (s : Weight d) (w : UnitSphere d) :
    inner Real w.val (transverseHalfField s w) = 0 := by
  simp [transverseHalfField, inner_smul_right, inner_sub_right ]

theorem transverseHalfField_continuous {d : Nat} (s : Weight d) : Continuous (transverseHalfField s) := by
  unfold transverseHalfField
  fun_prop

theorem transverseHalfField_reflect {d : Nat} (s : Weight d) (w : UnitSphere d) :
    transverseHalfField s (reflect w) = transverseHalfField s w := by
  simp [transverseHalfField]

theorem transverseHalfField_at_pole {d : Nat} (a : UnitSphere d) (s : Weight d)
    (hs : inner Real a.val s = 0) :
    transverseHalfField s a = (1/2 : Real) • s ∧
    transverseHalfField s (reflect a) = (1/2 : Real) • s := by
  simp [transverseHalfField, hs]

noncomputable def transverseCenterVariation {d : Nat} (a : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (s : Weight d) : SphericalVariation d where
  pole := a
  radius := r
  measure := fun _ => antipodalMeasure a
  cap := fun _ => antipodalMeasure_twoCap a hr hrpi
  velocity := fun _ => transverseHalfField s
  tangent := fun _ => transverseHalfField_tangent s
  continuous_velocity := fun _ => transverseHalfField_continuous s

end PaperFormalization.MatrixFactorization
