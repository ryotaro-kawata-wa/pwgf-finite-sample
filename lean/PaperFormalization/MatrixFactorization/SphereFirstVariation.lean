import PaperFormalization.MatrixFactorization.IntegralTangentTesting

/-! # MF24: the primal first-variation identity on bounded L2 tangent tests

Verification status and conditional scope: see `MF24_VALIDATION.md`. This predicate states the source gradient identity on a
specified subclass of its L2 tests; it does not assert the identity exists for
every law. It requires neither a dual optimizer nor pointwise differentiability
of any potential. Norm bounds and representative uniqueness are conclusions.
All statements refer to the original measure, including singular/atomic laws.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- A measurable representative of the spherical first variation of J at mu.
The square integral is the source L2 condition; tests are proved L2 upstream. -/
structure HasSphereFirstVariation {d : Nat} (mu : Measure (UnitSphere d))
    (J : Measure (UnitSphere d) → Real) (g : UnitSphere d → Weight d) : Prop where
  measurable_gradient : Measurable g
  tangent_ae : ∀ᵐ w ∂mu, inner Real w.val (g w) = 0
  norm_sq_integrable : Integrable (fun w => norm (g w)^2) mu
  derivative : ∀ V : BoundedTangentTest d,
    HasDerivAt (fun t => J (V.push mu t)) (∫ w, inner Real (g w) (V.field w) ∂mu) 0

theorem HasSphereFirstVariation.integrable {d : Nat} {mu : Measure (UnitSphere d)}
    [IsFiniteMeasure mu] {J : Measure (UnitSphere d) → Real}
    {g : UnitSphere d → Weight d} (H : HasSphereFirstVariation mu J g) :
    Integrable g mu :=
  sphere_integrable_of_norm_sq mu g H.measurable_gradient H.norm_sq_integrable

theorem HasSphereFirstVariation.unique_ae {d : Nat} {mu : Measure (UnitSphere d)}
    [IsFiniteMeasure mu] {J : Measure (UnitSphere d) → Real}
    {g k : UnitSphere d → Weight d}
    (H : HasSphereFirstVariation mu J g) (K : HasSphereFirstVariation mu J k) :
    g =ᵐ[mu] k := by
  apply ae_eq_of_bounded_tangent_pairings mu g k H.measurable_gradient K.measurable_gradient
    H.integrable K.integrable H.tangent_ae K.tangent_ae
  intro V
  exact (H.derivative V).unique (K.derivative V)

/-- All actual perturbation upper bounds are supplied separately. This general
adapter never places the desired speed estimate into the first-variation definition. -/
theorem HasSphereFirstVariation.norm_le_of_upper {d : Nat} {mu : Measure (UnitSphere d)}
    [IsFiniteMeasure mu] {J : Measure (UnitSphere d) → Real}
    {g : UnitSphere d → Weight d} (H : HasSphereFirstVariation mu J g)
    (C : Real) (hC : 0 ≤ C)
    (hupper : ∀ V : BoundedTangentTest d, ∀ᶠ t in 𝓝 (0 : Real),
      J (V.push mu t) ≤ J mu + (C*(∫ w, norm (V.field w) ∂mu))*|t|) :
    ∀ᵐ w ∂mu, norm (g w) ≤ C := by
  apply ae_norm_le_of_bounded_tangent_tests mu g H.measurable_gradient H.integrable
    H.tangent_ae C hC
  intro V
  have hb := derivative_abs_le_of_upper_cone (H.derivative V)
    (by simpa only [V.push_zero] using hupper V)
  exact (le_abs_self _).trans hb

/-- The actual half squared cost, with its existing all-coupling infimum. -/
noncomputable def halfTransportFunctional {d : Nat} (nu mu : Measure (UnitSphere d)) : Real :=
  sphericalWassersteinSq mu nu / 2

/-- A primal transport first variation has norm at most pi almost everywhere.
This result needs NO cap class, no optimizer and no classical dual gradient. -/
theorem halfTransport_firstVariation_norm_le {d : Nat}
    (mu nu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (g : UnitSphere d → Weight d)
    (H : HasSphereFirstVariation mu (halfTransportFunctional nu) g) :
    ∀ᵐ w ∂mu, norm (g w) ≤ Real.pi := by
  apply H.norm_le_of_upper Real.pi Real.pi_pos.le
  intro V
  filter_upwards [V.transport_upper_near_zero mu nu] with t ht
  unfold halfTransportFunctional
  linarith

/-- The L2 energy bound is derived after genuine integrability, on the same law. -/
theorem halfTransport_firstVariation_energy_le {d : Nat}
    (mu nu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (g : UnitSphere d → Weight d)
    (H : HasSphereFirstVariation mu (halfTransportFunctional nu) g) :
    (∫ w, norm (g w)^2 ∂mu) ≤ Real.pi^2 := by
  have hb := halfTransport_firstVariation_norm_le mu nu g H
  have hi := integral_mono_ae H.norm_sq_integrable (integrable_const (Real.pi^2)) (by
    filter_upwards [hb] with w hw
    exact pow_le_pow_left₀ (norm_nonneg _) hw 2)
  simpa using hi

end PaperFormalization.MatrixFactorization
