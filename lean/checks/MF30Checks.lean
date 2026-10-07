import PaperFormalization.MatrixFactorization.IntrinsicIntegralSource
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

-- 01: L2 reflection includes singular atomic laws.
example (w : UnitSphere d) (v : sphereTangentL2 (Measure.dirac w)) :
    MemLp (fun x => -sphereL2Representative v (reflect x)) 2 (reflectedMeasure (Measure.dirac w)) :=
  sphereL2_reflected_memLp v

-- 02: representative identity is AE, including at null support points.
example (mu : Measure (UnitSphere d)) (v : sphereTangentL2 mu) :
    sphereL2Representative (sphereL2Reflected v) =ᵐ[reflectedMeasure mu]
      fun w => -sphereL2Representative v (reflect w) := sphereL2Reflected_rep v

-- 03: reflection covariance agrees at time zero.
example (mu : Measure (UnitSphere d)) (v : sphereTangentL2 mu) :
    sphereL2ExpPush (reflectedMeasure mu) (sphereL2Reflected v) 0 = reflectedMeasure mu := by simp

-- 04: negative times and unbounded L2 directions are retained.
example (mu : Measure (UnitSphere d)) (v : sphereTangentL2 mu) (t : Real) :
    sphereL2ExpPush (reflectedMeasure mu) (sphereL2Reflected v) (-t) =
      reflectedMeasure (sphereL2ExpPush mu v (-t)) := sphereL2Reflected_push mu v (-t)

-- 05: the exact Hilbert norm energy is preserved.
example (mu : Measure (UnitSphere d)) (v : sphereTangentL2 mu) :
    norm (sphereL2Reflected v)^2 = norm v^2 := by
  simpa only [real_inner_self_eq_norm_sq] using sphereL2Reflected_inner v v

-- 06: every reflected L2 test is covered by the inverse.
example (mu : Measure (UnitSphere d)) (v : sphereTangentL2 (reflectedMeasure mu)) :
    sphereL2Reflected (sphereL2Unreflected mu v) = v := sphereL2Reflected_unreflected mu v

-- 07: inverse conjugacy is an equality of measures.
example (mu : Measure (UnitSphere d)) (v : sphereTangentL2 (reflectedMeasure mu)) (t : Real) :
    reflectedMeasure (sphereL2ExpPush (reflectedMeasure mu) v t) =
      sphereL2ExpPush mu (sphereL2Unreflected mu v) t := sphereL2Unreflected_push mu v t

-- 08: gradient-test pairing has the correct reflection sign.
example (mu : Measure (UnitSphere d)) (g : sphereTangentL2 mu)
    (v : sphereTangentL2 (reflectedMeasure mu)) :
    inner Real (sphereL2Reflected g) v = inner Real g (sphereL2Unreflected mu v) :=
  sphereL2Reflected_cross_inner mu g v

-- 09: full intrinsic reflection does not impose a boundedness premise.
example (mu : Measure (UnitSphere d)) (J : Measure (UnitSphere d) → Real)
    (g : sphereTangentL2 mu) (H : HasSphereL2FirstVariation mu J g) :
    HasSphereL2FirstVariation (reflectedMeasure mu) (fun nu => J (reflectedMeasure nu))
      (sphereL2Reflected g) := H.reflected

-- 10: functional congruence is needed only on probability laws.
example (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    (J K : Measure (UnitSphere d) → Real) (g : sphereTangentL2 mu)
    (H : HasSphereL2FirstVariation mu J g)
    (he : ∀ nu : Measure (UnitSphere d), IsProbabilityMeasure nu → J nu = K nu) :
    HasSphereL2FirstVariation mu K g := H.congr_on_probability he

-- 11: the actual whole reflected trajectory remains in the intrinsic subclass.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (H : X.HasSourceL2FirstVariation) (hO : ∀ n ∈ O, Odd n) :
    (X.reflectionExchange hO).HasSourceL2FirstVariation := H.reflectionExchange hO

-- 12: supported path uniqueness supplies law uniqueness in precisely that class.
example (hu : SourceL2ACPathUnique O a pole lambda p teacher initial) :
    SourceL2ACLawUnique O a pole lambda p teacher initial := hu.law_unique

-- 13: future branch identity is derived from source-class uniqueness alone.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (hX : X.HasSourceL2FirstVariation) (hO : ∀ n ∈ O, Odd n)
    (hu : SourceL2ACLawUnique O a pole lambda p teacher initial)
    (hi : initial 1 = reflectedMeasure (initial 0)) (t : Real) (ht : 0 ≤ t) :
    X.measure 1 t = reflectedMeasure (X.measure 0 t) :=
  X.antibranch_of_source_unique hX hO hu hi t ht

-- 14: the stronger old uniqueness implies the new restricted one; no converse is used.
example (hu : PrimalACLawUnique O a pole lambda p teacher initial) :
    SourceL2ACLawUnique O a pole lambda p teacher initial := by
  intro X Y _ _ i t ht
  exact hu X Y i t ht

-- 15: both competitors must possess the intrinsic source property.
example (hu : SourceL2ACLawUnique O a pole lambda p teacher initial)
    (X Y : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (hX : X.HasSourceL2FirstVariation) (hY : Y.HasSourceL2FirstVariation)
    (i : Fin 2) (t : Real) (ht : 0 ≤ t) : X.measure i t = Y.measure i t :=
  source_l2_ac_law_unique_of_initial_eq hu X hX Y hY rfl i t ht

-- 16: a constant functional has the zero intrinsic gradient on every L2 direction.
example (mu : Measure (UnitSphere d)) (c : Real) :
    HasSphereL2FirstVariation mu (fun _ => c) 0 := by
  intro v
  simpa only [inner_zero_left] using hasDerivAt_const (0 : Real) c

end PaperFormalization.MatrixFactorization
