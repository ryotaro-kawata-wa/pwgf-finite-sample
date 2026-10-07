import PaperFormalization.MatrixFactorization.ContinuousCapAssignment

/-! MF18 boundary diagnostics for original-support cap assignment. No example
assumes current half masses or continuity outside the original support. -/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization.MF18Checks
open PaperFormalization.MatrixFactorization
set_option autoImplicit false

-- 1. A zero-length interval requires no derivative and no continuity away from its sole point.
example {d : Nat} (pole : UnitSphere d) (r : Real) (w : Real → UnitSphere d)
    (hr : r < Real.pi/2)
    (h0 : w 0 ∈ sphericalCap pole r ∪ sphericalCap (reflect pole) r)
    (t : Real) (ht : t ∈ Icc (0 : Real) 0) : assignedPole pole (w t) = assignedPole pole (w 0) := by
  apply continuous_cap_path_assignedPole pole r 0 w hr le_rfl
  · simpa only [Icc_self] using continuousOn_singleton w (0 : Real)
  · intro s hs
    have he : s = 0 := le_antisymm hs.2 hs.1
    simpa only [he] using h0
  · exact ht

-- 2. Starting at the negative pole retains the negative cap label at every interval time.
example {d : Nat} (pole : UnitSphere d) (r T : Real) (w : Real → UnitSphere d)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (hT : 0 ≤ T)
    (hc : ContinuousOn w (Icc 0 T))
    (hi : ∀ t ∈ Icc 0 T, w t ∈ sphericalCap pole r ∪ sphericalCap (reflect pole) r)
    (h0 : w 0 = reflect pole) (t : Real) (ht : t ∈ Icc 0 T) :
    w t ∈ sphericalCap (reflect pole) r := by
  apply (continuous_cap_path_preserves pole r T w hrpi hT hc hi t ht).2
  rw [h0]
  exact sphericalCap_pole_mem (reflect pole) r hr

-- 3. The actual assigned pole equals that of the original starting weight.
example {d : Nat} (pole x : UnitSphere d) (r T : Real) (w : Real → UnitSphere d)
    (hrpi : r < Real.pi/2) (hT : 0 ≤ T) (hc : ContinuousOn w (Icc 0 T))
    (hi : ∀ t ∈ Icc 0 T, w t ∈ sphericalCap pole r ∪ sphericalCap (reflect pole) r)
    (h0 : w 0 = x) (t : Real) (ht : t ∈ Icc 0 T) :
    assignedPole pole (w t) = assignedPole pole x := by
  simpa only [h0] using continuous_cap_path_assignedPole pole r T w hrpi hT hc hi t ht

-- 4. Merely measurable current maps acquire both exact half masses from original paths in the union.
example {d : Nat} {pole : UnitSphere d} {r : Real} {mu : Measure (UnitSphere d)}
    (hcap : TwoCapClass pole r mu) (Phi : Real → UnitSphere d → UnitSphere d)
    (T : Real) (hT : 0 ≤ T) (h0 : ∀ w ∈ mu.support, Phi 0 w = w)
    (hc : ∀ w ∈ mu.support, ContinuousOn (fun t => Phi t w) (Icc 0 T))
    (hi : ∀ w ∈ mu.support, ∀ t ∈ Icc 0 T,
      Phi t w ∈ sphericalCap pole r ∪ sphericalCap (reflect pole) r)
    (t : Real) (ht : t ∈ Icc 0 T) (hm : Measurable (Phi t)) :
    (mu.map (Phi t)) (sphericalCap pole r) = (1/2 : ENNReal) ∧
      (mu.map (Phi t)) (sphericalCap (reflect pole) r) = (1/2 : ENNReal) :=
  hcap.map_half_masses_of_continuous_paths Phi T hT h0 hc hi t ht hm

-- 5. Every point of the pushed closed support has an original supported preimage;
-- continuity is required only on that original support.
example {d : Nat} (mu : Measure (UnitSphere d)) (f : UnitSphere d → UnitSphere d)
    (hm : Measurable f) (hc : ContinuousOn f mu.support) (y : UnitSphere d)
    (hy : y ∈ (mu.map f).support) : ∃ w ∈ mu.support, f w = y :=
  sphere_support_map_subset_image_of_continuousOn mu f hm hc hy

-- 6. Arbitrary unsupported values do not change the original law or its full cap class.
example {d : Nat} {pole : UnitSphere d} {r : Real} {mu : Measure (UnitSphere d)}
    (hcap : TwoCapClass pole r mu) (f : UnitSphere d → UnitSphere d) (hm : Measurable f)
    (hid : ∀ w ∈ mu.support, f w = w) : mu.map f = mu ∧ TwoCapClass pole r (mu.map f) := by
  have hc : ContinuousOn f mu.support := by
    apply continuousOn_id.congr
    intro w hw
    exact hid w hw
  have hp : PreservesCapAssignment pole r mu f := by
    intro w hw
    rw [hid w hw]
    exact ⟨id,id⟩
  refine ⟨?_,hcap.map_on_support f hm hc hp⟩
  calc
    mu.map f = mu.map id := by
      apply Measure.map_congr
      filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
      exact hid w hw
    _ = mu := Measure.map_id

section DerivedCurrentLaw
variable {d : Nat} {pole : UnitSphere d} {r : Real} {mu : Measure (UnitSphere d)}
  (hcap : TwoCapClass pole r mu) (Phi : Real → UnitSphere d → UnitSphere d)
  (T : Real) (hT : 0 ≤ T) (h0 : ∀ w ∈ mu.support, Phi 0 w = w)
  (hc : ∀ w ∈ mu.support, ContinuousOn (fun t => Phi t w) (Icc 0 T))
  (hi : ∀ w ∈ mu.support, ∀ t ∈ Icc 0 T,
    Phi t w ∈ sphericalCap pole r ∪ sphericalCap (reflect pole) r)
  (t : Real) (ht : t ∈ Icc 0 T) (hm : Measurable (Phi t))
  (hs : ContinuousOn (Phi t) mu.support)

-- 7. The target marginal of the assigned coupling is derived from the original path data.
example : (mu.map (Phi t)).map (assignedPole pole) = antipodalMeasure pole :=
  assignedPole_pushforward pole r _
    (hcap.map_of_continuous_paths Phi T hT h0 hc hi t ht hm hs)

-- 8. The current infimum over all transport plans equals an original-measure integral.
example : sphericalWassersteinSq (mu.map (Phi t)) (antipodalMeasure pole) =
    2*∫ w, assignedCost pole (Phi t w) ∂mu :=
  fixed_assignment_of_continuous_paths hcap Phi T hT h0 hc hi t ht hm hs
end DerivedCurrentLaw

end PaperFormalization.MatrixFactorization.MF18Checks
