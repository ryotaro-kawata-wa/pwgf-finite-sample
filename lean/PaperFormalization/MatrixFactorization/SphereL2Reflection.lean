import PaperFormalization.MatrixFactorization.SphereL2FirstVariation
import PaperFormalization.MatrixFactorization.PrimalFirstVariationSymmetry

/-! # MF30: reflection acts on the genuine spherical tangent L2 spaces

Both the base law and tangent vector are reflected. Statements involving
representatives are AE statements; the EXP conjugacy is an exact equality
of pushed probability laws, including for unbounded L2 tangent directions.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

theorem sphereL2_reflected_memLp {d : Nat} {mu : Measure (UnitSphere d)}
    (v : sphereTangentL2 mu) :
    MemLp (fun w => -sphereL2Representative v (reflect w)) 2 (reflectedMeasure mu) := by
  have hm := ((sphereL2Representative_measurable v).comp (reflect_measurable d)).neg
  apply (memLp_map_measure_iff hm.aestronglyMeasurable (reflect_measurable d).aemeasurable).mpr
  convert (sphereL2Representative_memLp v).neg using 1 <;>
    first | rfl | simp only [Function.comp_def, reflect_reflect, Pi.neg_def]

/-- Reflect a source tangent class, using its representative only to construct
the new quotient class. The resulting representative is identified AE below. -/
noncomputable def sphereL2Reflected {d : Nat} {mu : Measure (UnitSphere d)}
    (v : sphereTangentL2 mu) : sphereTangentL2 (reflectedMeasure mu) :=
  ⟨(sphereL2_reflected_memLp v).toLp _, by
    filter_upwards [(sphereL2_reflected_memLp v).coeFn_toLp] with w hw
    rw [hw]
    simpa only [reflect_val, inner_neg_left, inner_neg_right] using
      sphereL2Representative_tangent v (reflect w)⟩

theorem sphereL2Reflected_rep {d : Nat} {mu : Measure (UnitSphere d)}
    (v : sphereTangentL2 mu) :
    sphereL2Representative (sphereL2Reflected v) =ᵐ[reflectedMeasure mu]
      fun w => -sphereL2Representative v (reflect w) :=
  (sphereL2Representative_ae_eq (sphereL2Reflected v)).trans
    (sphereL2_reflected_memLp v).coeFn_toLp

/-- Exact EXP covariance for every L2 tangent direction and every real time. -/
theorem sphereL2Reflected_push {d : Nat} (mu : Measure (UnitSphere d))
    (v : sphereTangentL2 mu) (t : Real) :
    sphereL2ExpPush (reflectedMeasure mu) (sphereL2Reflected v) t =
      reflectedMeasure (sphereL2ExpPush mu v t) := by
  have ht : ∀ w : UnitSphere d, inner Real w.val (-sphereL2Representative v (reflect w)) = 0 := by
    intro w
    simpa only [reflect_val, inner_neg_left, inner_neg_right] using
      sphereL2Representative_tangent v (reflect w)
  rw [sphereL2ExpPush_eq_of_representative _ _ _ ht (sphereL2Reflected_rep v)]
  have hmap : sphericalExpFamily (fun w => -sphereL2Representative v (reflect w)) ht t =
      fun w => reflect (sphereL2ExpMap v t (reflect w)) := by
    funext w
    change geodesicPoint w (-sphereL2Representative v (reflect w)) (ht w) t =
      reflect (geodesicPoint (reflect w) (sphereL2Representative v (reflect w))
        (sphereL2Representative_tangent v (reflect w)) t)
    simpa only [reflect_reflect] using geodesicPoint_reflected (reflect w)
      (sphereL2Representative v (reflect w)) (sphereL2Representative_tangent v (reflect w)) t
  rw [hmap]
  exact reflectedMeasure_map_conjugate mu (sphereL2ExpMap v t) (sphereL2ExpMap_measurable v t)

/-- Reflection preserves the exact Hilbert pairing, not only a norm bound. -/
theorem sphereL2Reflected_inner {d : Nat} {mu : Measure (UnitSphere d)}
    (u v : sphereTangentL2 mu) :
    inner Real (sphereL2Reflected u) (sphereL2Reflected v) = inner Real u v := by
  rw [sphereL2Representative_inner, sphereL2Representative_inner]
  have hchange : (∫ w, inner Real (sphereL2Representative (sphereL2Reflected u) w)
      (sphereL2Representative (sphereL2Reflected v) w) ∂reflectedMeasure mu) =
      ∫ w, inner Real (-sphereL2Representative u (reflect w))
        (-sphereL2Representative v (reflect w)) ∂reflectedMeasure mu := by
    apply integral_congr_ae
    filter_upwards [sphereL2Reflected_rep u, sphereL2Reflected_rep v] with w hu hv
    rw [hu, hv]
  rw [hchange]
  have hm := (((sphereL2Representative_measurable u).comp (reflect_measurable d)).neg).inner
    (𝕜 := Real) (((sphereL2Representative_measurable v).comp (reflect_measurable d)).neg)
  have hh := integral_map (reflect_measurable d).aemeasurable (μ := mu) hm.aestronglyMeasurable
  convert hh using 1 <;>
    (try simp only [Function.comp_def, Pi.neg_apply, reflect_reflect, inner_neg_neg]) <;> rfl

end PaperFormalization.MatrixFactorization
