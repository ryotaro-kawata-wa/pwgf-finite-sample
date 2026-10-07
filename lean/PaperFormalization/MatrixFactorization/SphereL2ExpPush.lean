import PaperFormalization.MatrixFactorization.SphereTangentL2

/-! # MF28: actual spherical EXP pushforwards of L2 tangent classes

The law below is an actual pushforward, not a formal tangent symbol. Changes
of representative are handled on the original law before taking the map.
No pointwise identity of arbitrary L2 representatives is used. Both signs of
time and the zero direction are included. See `MF28_WORKLOG.md` for status.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def sphereL2ExpMap {d : Nat} {mu : Measure (UnitSphere d)}
    (v : sphereTangentL2 mu) (t : Real) : UnitSphere d → UnitSphere d :=
  sphericalExpFamily (sphereL2Representative v) (sphereL2Representative_tangent v) t

theorem sphereL2ExpMap_measurable {d : Nat} {mu : Measure (UnitSphere d)}
    (v : sphereTangentL2 mu) (t : Real) : Measurable (sphereL2ExpMap v t) := by
  have hv := (sphereL2Representative_measurable v).const_smul t
  exact ((sphereExpVector_continuous d).measurable.comp
    (measurable_id.prodMk hv)).subtype_mk

noncomputable def sphereL2ExpPush {d : Nat} (mu : Measure (UnitSphere d))
    (v : sphereTangentL2 mu) (t : Real) : Measure (UnitSphere d) :=
  mu.map (sphereL2ExpMap v t)

theorem sphereL2ExpPush_probability {d : Nat} (mu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] (v : sphereTangentL2 mu) (t : Real) :
    IsProbabilityMeasure (sphereL2ExpPush mu v t) :=
  Measure.isProbabilityMeasure_map (sphereL2ExpMap_measurable v t).aemeasurable

@[simp] theorem sphereL2ExpPush_zero_time {d : Nat} (mu : Measure (UnitSphere d))
    (v : sphereTangentL2 mu) : sphereL2ExpPush mu v 0 = mu := by
  have he : sphereL2ExpMap v 0 = id := by
    funext w
    exact sphericalExpFamily_zero _ _ w
  simp only [sphereL2ExpPush, he, Measure.map_id]

/-- Any everywhere-tangent representative of the same class gives the same
law. The representative need not agree at null support points. -/
theorem sphereL2ExpPush_eq_of_representative {d : Nat}
    (mu : Measure (UnitSphere d)) (v : sphereTangentL2 mu)
    (f : UnitSphere d → Weight d) (ht : ∀ w, inner Real w.val (f w) = 0)
    (he : sphereL2Representative v =ᵐ[mu] f) (t : Real) :
    sphereL2ExpPush mu v t = mu.map (sphericalExpFamily f ht t) := by
  apply Measure.map_congr
  filter_upwards [he] with w hw
  apply Subtype.ext
  simp only [sphereL2ExpMap, sphericalExpFamily, sphericalExp_val, hw]

theorem BoundedTangentTest.toSphereL2_push {d : Nat} (V : BoundedTangentTest d)
    (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu] (t : Real) :
    sphereL2ExpPush mu (V.toSphereL2 mu) t = V.push mu t :=
  sphereL2ExpPush_eq_of_representative mu (V.toSphereL2 mu)
    V.field V.tangent (V.toSphereL2_ae_eq mu) t

theorem sphereL2Representative_smul_ae {d : Nat} {mu : Measure (UnitSphere d)}
    (v : sphereTangentL2 mu) (c : Real) :
    sphereL2Representative (c • v) =ᵐ[mu] fun w => c • sphereL2Representative v w := by
  filter_upwards [sphereL2Representative_ae_eq (c • v),
    Lp.coeFn_smul c (v : Lp (Weight d) 2 mu), sphereL2Representative_ae_eq v] with w hcv hc hv
  rw [hcv, hv]
  exact hc

theorem sphereL2ExpPush_smul {d : Nat} (mu : Measure (UnitSphere d))
    (v : sphereTangentL2 mu) (c t : Real) :
    sphereL2ExpPush mu (c • v) t = sphereL2ExpPush mu v (t*c) := by
  apply Measure.map_congr
  filter_upwards [sphereL2Representative_smul_ae v c] with w hw
  apply Subtype.ext
  simp only [sphereL2ExpMap, sphericalExpFamily, sphericalExp_val, hw, smul_smul]

@[simp] theorem sphereL2ExpPush_zero_direction {d : Nat}
    (mu : Measure (UnitSphere d)) (t : Real) :
    sphereL2ExpPush mu (0 : sphereTangentL2 mu) t = mu := by
  have he := sphereL2ExpPush_smul mu (0 : sphereTangentL2 mu) 0 t
  simpa only [zero_smul, mul_zero, sphereL2ExpPush_zero_time] using he

/-- The L2 chart on scalar multiples is exactly the old bounded-test path. -/
theorem BoundedTangentTest.toSphereL2_chart {d : Nat} (V : BoundedTangentTest d)
    (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu] (t : Real) :
    sphereL2ExpPush mu (t • V.toSphereL2 mu) 1 = V.push mu t := by
  rw [sphereL2ExpPush_smul, one_mul, V.toSphereL2_push]

end PaperFormalization.MatrixFactorization
