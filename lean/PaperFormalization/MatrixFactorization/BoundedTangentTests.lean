import PaperFormalization.MatrixFactorization.SphericalTransportPerturbation
import PaperFormalization.MatrixFactorization.SphericalMetricGradient

/-! # MF24: measurable bounded tangent tests, not classical dual gradients

Verification status and conditional scope: see `MF24_VALIDATION.md`.
A bounded Borel tangent field is an admissible
L2 direction for every probability on the sphere. No continuity across an
assignment boundary, density of a source law, or dual differential is assumed.
The projection below only chooses a pointwise-tangent representative of an
already almost-everywhere tangent field; it does not alter that L2 field.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

structure BoundedTangentTest (d : Nat) where
  field : UnitSphere d → Weight d
  measurable_field : Measurable field
  tangent : ∀ w, inner Real w.val (field w) = 0
  bound : Real
  bound_nonneg : 0 ≤ bound
  norm_le : ∀ w, norm (field w) ≤ bound

noncomputable def BoundedTangentTest.zero (d : Nat) : BoundedTangentTest d where
  field := fun _ => 0
  measurable_field := measurable_const
  tangent := by intro w; simp
  bound := 0
  bound_nonneg := le_rfl
  norm_le := by intro w; simp

noncomputable def BoundedTangentTest.neg {d : Nat} (V : BoundedTangentTest d) :
    BoundedTangentTest d where
  field := fun w => -V.field w
  measurable_field := V.measurable_field.neg
  tangent := by intro w; simp only [inner_neg_right, V.tangent, neg_zero]
  bound := V.bound
  bound_nonneg := V.bound_nonneg
  norm_le := by intro w; simpa only [norm_neg] using V.norm_le w

theorem BoundedTangentTest.integrable {d : Nat} (V : BoundedTangentTest d)
    (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu] : Integrable V.field mu :=
  Integrable.of_bound V.measurable_field.aestronglyMeasurable V.bound
    (Eventually.of_forall V.norm_le)

theorem BoundedTangentTest.norm_integrable {d : Nat} (V : BoundedTangentTest d)
    (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu] :
    Integrable (fun w => norm (V.field w)) mu := (V.integrable mu).norm

theorem BoundedTangentTest.norm_sq_integrable {d : Nat} (V : BoundedTangentTest d)
    (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu] :
    Integrable (fun w => norm (V.field w)^2) mu := by
  apply Integrable.of_bound ((V.measurable_field.norm.pow_const 2).aestronglyMeasurable)
    (V.bound^2)
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (V.norm_le w) 2

/-- The first-variation pairing is a genuine integral before it is used. -/
theorem BoundedTangentTest.pairing_integrable {d : Nat} (V : BoundedTangentTest d)
    (mu : Measure (UnitSphere d)) (g : UnitSphere d → Weight d)
    (hg : Integrable g mu) :
    Integrable (fun w => inner Real (g w) (V.field w)) mu := by
  apply (hg.norm.mul_const V.bound).mono'
    (hg.aestronglyMeasurable.inner (𝕜 := Real)
      V.measurable_field.aestronglyMeasurable)
  filter_upwards with w
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left (V.norm_le w) (norm_nonneg _))

/-- Finite-measure L2 data supply L1; no totalized nonintegrable integral is used. -/
theorem sphere_integrable_of_norm_sq {d : Nat} (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (g : UnitSphere d → Weight d)
    (hg : Measurable g) (h2 : Integrable (fun w => norm (g w)^2) mu) :
    Integrable g mu := by
  apply ((h2.add (integrable_const (1 : Real))).div_const 2).mono'
    hg.aestronglyMeasurable
  filter_upwards with w
  change norm (g w) ≤ (norm (g w)^2 + 1) / 2
  nlinarith [sq_nonneg (norm (g w)-1)]

noncomputable def tangentVersion {d : Nat} (g : UnitSphere d → Weight d)
    (w : UnitSphere d) : Weight d :=
  g w - (inner Real w.val (g w)) • w.val

theorem tangentVersion_measurable {d : Nat} (g : UnitSphere d → Weight d)
    (hg : Measurable g) : Measurable (tangentVersion g) := by
  exact hg.sub (((continuous_subtype_val.measurable).inner (𝕜 := Real) hg).smul
    continuous_subtype_val.measurable)

theorem tangentVersion_tangent {d : Nat} (g : UnitSphere d → Weight d)
    (w : UnitSphere d) : inner Real w.val (tangentVersion g w) = 0 := by
  simp only [tangentVersion, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, unitSphere_norm, one_pow, mul_one, sub_self]

theorem tangentVersion_ae_eq {d : Nat} (mu : Measure (UnitSphere d))
    (g : UnitSphere d → Weight d)
    (ht : ∀ᵐ w ∂mu, inner Real w.val (g w) = 0) :
    tangentVersion g =ᵐ[mu] g := by
  filter_upwards [ht] with w hw
  simp only [tangentVersion, hw, zero_smul, sub_zero]

theorem tangentVersion_integrable {d : Nat} (mu : Measure (UnitSphere d))
    (g : UnitSphere d → Weight d) (hg : Integrable g mu)
    (ht : ∀ᵐ w ∂mu, inner Real w.val (g w) = 0) :
    Integrable (tangentVersion g) mu := hg.congr (tangentVersion_ae_eq mu g ht).symm

end PaperFormalization.MatrixFactorization
