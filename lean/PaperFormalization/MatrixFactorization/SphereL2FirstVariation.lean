import PaperFormalization.MatrixFactorization.SphereL2ExpPush
import PaperFormalization.MatrixFactorization.SphereFirstVariationAlgebra

/-! # MF28: from the intrinsic source L2 identity to bounded Borel tests

The derivative is taken along the literal EXP pushforward of each tangent
L2 class. The source gradient is an L2 vector, so its Borel representative,
tangency and true square integrability are constructed rather than assumed
again. The conversion does not assert existence of a first variation at every
law, or joint measurability of a time-indexed choice. See `MF28_WORKLOG.md`.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The intrinsic L2 directional first-variation identity. This is a
statewise formulation of the source pairing; it is not a new flow class. -/
def HasSphereL2FirstVariation {d : Nat} (mu : Measure (UnitSphere d))
    (J : Measure (UnitSphere d) → Real) (g : sphereTangentL2 mu) : Prop :=
  ∀ v : sphereTangentL2 mu,
    HasDerivAt (fun t => J (sphereL2ExpPush mu v t)) (inner Real g v) 0

/-- The source L2 identity supplies every field of the existing primal
predicate, including the actual derivative on discontinuous bounded tests. -/
theorem HasSphereL2FirstVariation.to_primal {d : Nat} {mu : Measure (UnitSphere d)}
    [IsFiniteMeasure mu] {J : Measure (UnitSphere d) → Real}
    {g : sphereTangentL2 mu} (H : HasSphereL2FirstVariation mu J g) :
    HasSphereFirstVariation mu J (sphereL2Representative g) := by
  refine ⟨sphereL2Representative_measurable g,
    Eventually.of_forall (sphereL2Representative_tangent g),
    sphereL2Representative_norm_sq_integrable g, ?_⟩
  intro V
  simpa only [V.toSphereL2_push mu, V.toSphereL2_pairing mu g] using H (V.toSphereL2 mu)

/-- A supplied jointly measurable velocity representative can be kept when
it represents the same L2 gradient; it need not be replaced pointwise. -/
theorem HasSphereL2FirstVariation.to_primal_of_ae {d : Nat}
    {mu : Measure (UnitSphere d)} [IsFiniteMeasure mu]
    {J : Measure (UnitSphere d) → Real} {g : sphereTangentL2 mu}
    (H : HasSphereL2FirstVariation mu J g) (k : UnitSphere d → Weight d)
    (hk : Measurable k) (he : sphereL2Representative g =ᵐ[mu] k) :
    HasSphereFirstVariation mu J k := H.to_primal.congr_gradient_ae hk he

/-- Source L2 energy and the actual representative's integral coincide. -/
theorem sphereL2Representative_energy {d : Nat} {mu : Measure (UnitSphere d)}
    (g : sphereTangentL2 mu) :
    (∫ w, norm (sphereL2Representative g w)^2 ∂mu) = norm g^2 := by
  simpa only [real_inner_self_eq_norm_sq] using (sphereL2Representative_inner g g).symm

/-- The gradient is unique as an L2 class, including for atomic laws. -/
theorem HasSphereL2FirstVariation.unique {d : Nat} {mu : Measure (UnitSphere d)}
    [IsFiniteMeasure mu] {J : Measure (UnitSphere d) → Real}
    {g k : sphereTangentL2 mu}
    (H : HasSphereL2FirstVariation mu J g) (K : HasSphereL2FirstVariation mu J k) : g = k := by
  apply Subtype.ext
  apply Lp.ext
  exact (sphereL2Representative_ae_eq g).symm.trans
    ((H.to_primal.unique_ae K.to_primal).trans (sphereL2Representative_ae_eq k))

/-- A Frechet derivative of the actual L2 EXP lift is a sufficient condition,
not an extra premise attached to the manuscript's directional formulation. -/
theorem sphereL2FirstVariation_of_hasFDerivAt {d : Nat}
    (mu : Measure (UnitSphere d)) (J : Measure (UnitSphere d) → Real)
    (g : sphereTangentL2 mu)
    (H : HasFDerivAt (fun v : sphereTangentL2 mu => J (sphereL2ExpPush mu v 1))
      (innerSL Real g) 0) : HasSphereL2FirstVariation mu J g := by
  intro v
  have hline : HasDerivAt (fun t : Real => t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : Real)).smul_const v
  have hbase : HasFDerivAt (fun u : sphereTangentL2 mu => J (sphereL2ExpPush mu u 1))
      (innerSL Real g) ((fun t : Real => t • v) 0) := by
    simpa only [zero_smul] using H
  have hd := hbase.comp_hasDerivAt 0 hline
  change HasDerivAt (fun t : Real => J (sphereL2ExpPush mu (t • v) 1)) (inner Real g v) 0 at hd
  simpa only [sphereL2ExpPush_smul, one_mul] using hd

end PaperFormalization.MatrixFactorization
