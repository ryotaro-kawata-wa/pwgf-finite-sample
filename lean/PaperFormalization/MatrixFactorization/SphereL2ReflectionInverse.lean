import PaperFormalization.MatrixFactorization.SphereL2Reflection

/-! # MF30: every reflected L2 test comes from an original L2 test

The inverse is constructed at the original law, avoiding an implicit
identification of different quotient spaces. This supplies reflection of
the complete intrinsic first-variation predicate, not just bounded tests.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

theorem sphereL2_unreflected_memLp {d : Nat} (mu : Measure (UnitSphere d))
    (v : sphereTangentL2 (reflectedMeasure mu)) :
    MemLp (fun w => -sphereL2Representative v (reflect w)) 2 mu := by
  have hv := (sphereL2Representative_memLp v).comp_of_map (reflect_measurable d).aemeasurable
  convert hv.neg using 1 <;> rfl

noncomputable def sphereL2Unreflected {d : Nat} (mu : Measure (UnitSphere d))
    (v : sphereTangentL2 (reflectedMeasure mu)) : sphereTangentL2 mu :=
  ⟨(sphereL2_unreflected_memLp mu v).toLp _, by
    filter_upwards [(sphereL2_unreflected_memLp mu v).coeFn_toLp] with w hw
    rw [hw]
    simpa only [reflect_val, inner_neg_left, inner_neg_right] using
      sphereL2Representative_tangent v (reflect w)⟩

theorem sphereL2Unreflected_rep {d : Nat} (mu : Measure (UnitSphere d))
    (v : sphereTangentL2 (reflectedMeasure mu)) :
    sphereL2Representative (sphereL2Unreflected mu v) =ᵐ[mu]
      fun w => -sphereL2Representative v (reflect w) :=
  (sphereL2Representative_ae_eq (sphereL2Unreflected mu v)).trans
    (sphereL2_unreflected_memLp mu v).coeFn_toLp

/-- Surjectivity is an equality of the actual tangent L2 quotient classes. -/
theorem sphereL2Reflected_unreflected {d : Nat} (mu : Measure (UnitSphere d))
    (v : sphereTangentL2 (reflectedMeasure mu)) :
    sphereL2Reflected (sphereL2Unreflected mu v) = v := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [sphereL2Representative_ae_eq (sphereL2Reflected (sphereL2Unreflected mu v)),
    sphereL2Reflected_rep (sphereL2Unreflected mu v),
    ae_reflected_of_ae mu (sphereL2Unreflected_rep mu v),
    sphereL2Representative_ae_eq v] with w hclass href hunref hv
  rw [← hclass, href, hunref, reflect_reflect, neg_neg, hv]

theorem sphereL2Unreflected_push {d : Nat} (mu : Measure (UnitSphere d))
    (v : sphereTangentL2 (reflectedMeasure mu)) (t : Real) :
    reflectedMeasure (sphereL2ExpPush (reflectedMeasure mu) v t) =
      sphereL2ExpPush mu (sphereL2Unreflected mu v) t := by
  have he := sphereL2Reflected_push mu (sphereL2Unreflected mu v) t
  rw [sphereL2Reflected_unreflected] at he
  rw [he, reflectedMeasure_involutive]

theorem sphereL2Reflected_cross_inner {d : Nat} (mu : Measure (UnitSphere d))
    (g : sphereTangentL2 mu) (v : sphereTangentL2 (reflectedMeasure mu)) :
    inner Real (sphereL2Reflected g) v = inner Real g (sphereL2Unreflected mu v) := by
  have hi := sphereL2Reflected_inner g (sphereL2Unreflected mu v)
  simpa only [sphereL2Reflected_unreflected] using hi

/-- All L2 directions, including unbounded ones, are covered by reflection. -/
theorem HasSphereL2FirstVariation.reflected {d : Nat}
    {mu : Measure (UnitSphere d)} {J : Measure (UnitSphere d) → Real}
    {g : sphereTangentL2 mu} (H : HasSphereL2FirstVariation mu J g) :
    HasSphereL2FirstVariation (reflectedMeasure mu) (fun nu => J (reflectedMeasure nu))
      (sphereL2Reflected g) := by
  intro v
  simpa only [sphereL2Unreflected_push, sphereL2Reflected_cross_inner] using
    H (sphereL2Unreflected mu v)

/-- The objective is compared only on its actual probability domain. -/
theorem HasSphereL2FirstVariation.congr_on_probability {d : Nat}
    {mu : Measure (UnitSphere d)} [IsProbabilityMeasure mu]
    {J K : Measure (UnitSphere d) → Real} {g : sphereTangentL2 mu}
    (H : HasSphereL2FirstVariation mu J g)
    (he : ∀ nu : Measure (UnitSphere d), IsProbabilityMeasure nu → J nu = K nu) :
    HasSphereL2FirstVariation mu K g := by
  intro v
  have hfun : (fun t => K (sphereL2ExpPush mu v t)) =
      (fun t => J (sphereL2ExpPush mu v t)) := by
    funext t
    exact (he _ (sphereL2ExpPush_probability mu v t)).symm
  rw [hfun]
  exact H v

/-- Intrinsic covariance of both actual source partial objectives. -/
theorem source_l2_firstVariation_reflection_exchange {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (lambda p : Real) (mu : Fin 2 → Measure (UnitSphere d))
    (hmu : ∀ i, IsProbabilityMeasure (mu i)) (teacher : Measure (UnitSphere d))
    (g : ∀ i, sphereTangentL2 (mu i))
    (H : ∀ i, HasSphereL2FirstVariation (mu i)
      (sourcePartialObjective O a pole lambda p mu teacher i) (g i)) :
    ∀ i, HasSphereL2FirstVariation (reflectionExchangePair mu i)
      (sourcePartialObjective O a pole lambda p (reflectionExchangePair mu) teacher i)
      (sphereL2Reflected (g i.rev)) := by
  intro i
  letI := hmu i.rev
  apply (H i.rev).reflected.congr_on_probability
  intro nu hnu
  letI := hnu
  exact sourcePartialObjective_reflection_conjugate O a hO pole lambda p mu hmu teacher i nu

end PaperFormalization.MatrixFactorization
