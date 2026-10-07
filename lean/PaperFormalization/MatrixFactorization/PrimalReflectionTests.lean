import PaperFormalization.MatrixFactorization.SphereFirstVariation
import PaperFormalization.MatrixFactorization.SphericalCharacteristicSymmetry

/-! # MF27: reflection of the actual bounded primal tests

Verification status and conditional scope: see `MF27_VALIDATION.md`. Reflection changes the point AND the tangent
vector. The perturbation is the existing spherical EXP, for both signs of time.
No cap, density, transport optimizer, or potential differential is needed.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Transfer an original-law conull predicate through the actual involution.
The predicate need not have a separately assumed measurable representative. -/
theorem ae_reflected_of_ae {d : Nat} (mu : Measure (UnitSphere d))
    {P : UnitSphere d → Prop} (hP : ∀ᵐ w ∂mu, P w) :
    ∀ᵐ w ∂reflectedMeasure mu, P (reflect w) := by
  apply ae_of_ae_map (reflect_measurable d).aemeasurable
  change ∀ᵐ w ∂reflectedMeasure (reflectedMeasure mu), P w
  simpa only [reflectedMeasure_involutive] using hP

noncomputable def BoundedTangentTest.reflected {d : Nat}
    (V : BoundedTangentTest d) : BoundedTangentTest d where
  field := fun w => -V.field (reflect w)
  measurable_field := (V.measurable_field.comp (reflect_measurable d)).neg
  tangent := by
    intro w
    simpa only [reflect_val, inner_neg_left, inner_neg_right] using V.tangent (reflect w)
  bound := V.bound
  bound_nonneg := V.bound_nonneg
  norm_le := by intro w; simpa only [norm_neg] using V.norm_le (reflect w)

@[simp] theorem BoundedTangentTest.reflected_field {d : Nat}
    (V : BoundedTangentTest d) (w : UnitSphere d) :
    V.reflected.field w = -V.field (reflect w) := rfl

@[simp] theorem BoundedTangentTest.reflected_twice_field {d : Nat}
    (V : BoundedTangentTest d) (w : UnitSphere d) :
    V.reflected.reflected.field w = V.field w := by
  simp only [BoundedTangentTest.reflected_field, reflect_reflect, neg_neg]

/-- Conjugating the genuine exponential perturbation reflects its velocity. -/
theorem BoundedTangentTest.reflected_expMap {d : Nat}
    (V : BoundedTangentTest d) (t : Real) (w : UnitSphere d) :
    V.reflected.expMap t w = reflect (V.expMap t (reflect w)) := by
  change geodesicPoint w (-V.field (reflect w)) (V.reflected.tangent w) t =
    reflect (geodesicPoint (reflect w) (V.field (reflect w)) (V.tangent (reflect w)) t)
  simpa only [reflect_reflect] using
    geodesicPoint_reflected (reflect w) (V.field (reflect w)) (V.tangent (reflect w)) t

/-- Equality of measures, not merely equality of moments or finite tests. -/
theorem BoundedTangentTest.reflected_push {d : Nat}
    (V : BoundedTangentTest d) (mu : Measure (UnitSphere d)) (t : Real) :
    V.reflected.push (reflectedMeasure mu) t = reflectedMeasure (V.push mu t) := by
  change (reflectedMeasure mu).map (V.reflected.expMap t) = _
  rw [show V.reflected.expMap t =
    (fun w => reflect (V.expMap t (reflect w))) from funext (V.reflected_expMap t)]
  exact reflectedMeasure_map_conjugate mu (V.expMap t) (V.expMap_measurable t)

/-- The inverse conjugacy is the form used to transform a primal derivative. -/
theorem BoundedTangentTest.push_reflected_inverse {d : Nat}
    (V : BoundedTangentTest d) (mu : Measure (UnitSphere d)) (t : Real) :
    reflectedMeasure (V.push (reflectedMeasure mu) t) = V.reflected.push mu t := by
  have h := V.reflected_push (reflectedMeasure mu) t
  simpa only [reflectedMeasure_involutive] using h.symm

/-- The reflected pairing is a true integrable pairing on the reflected law. -/
theorem BoundedTangentTest.reflected_pairing_integrable {d : Nat}
    (V : BoundedTangentTest d) (mu : Measure (UnitSphere d))
    (g : UnitSphere d → Weight d) (hg : Measurable g) (hi : Integrable g mu) :
    Integrable (fun w => inner Real (-g (reflect w)) (V.field w)) (reflectedMeasure mu) := by
  have hm := ((hg.comp (reflect_measurable d)).neg).inner (𝕜 := Real) V.measurable_field
  apply (integrable_map_measure hm.aestronglyMeasurable
    (reflect_measurable d).aemeasurable).mpr
  simpa only [Function.comp_def, Pi.neg_apply, reflect_reflect, inner_neg_left,
    BoundedTangentTest.reflected_field, inner_neg_right] using V.reflected.pairing_integrable mu g hi

/-- Change of variables preserves the source tangent pairing, including its sign. -/
theorem BoundedTangentTest.reflected_pairing {d : Nat}
    (V : BoundedTangentTest d) (mu : Measure (UnitSphere d))
    (g : UnitSphere d → Weight d) (hg : Measurable g) (hi : Integrable g mu) :
    (∫ w, inner Real (-g (reflect w)) (V.field w) ∂reflectedMeasure mu) =
      ∫ w, inner Real (g w) (V.reflected.field w) ∂mu := by
  have hint := V.reflected_pairing_integrable mu g hg hi
  rw [reflectedMeasure, integral_map (reflect_measurable d).aemeasurable
    hint.aestronglyMeasurable]
  simp only [reflect_reflect, BoundedTangentTest.reflected_field,
    inner_neg_left, inner_neg_right]

end PaperFormalization.MatrixFactorization
