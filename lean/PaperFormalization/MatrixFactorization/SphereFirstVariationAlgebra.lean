import PaperFormalization.MatrixFactorization.SphereFirstVariation

/-! # MF24: algebra of genuine primal first variations

Verification status and conditional scope: see `MF24_VALIDATION.md`. In particular, subtracting the proved fitting derivative
from the source full derivative supplies the regularizer derivative. Its
existence is not made a second independent model assumption. The L2 and L1
integrability obligations are retained before splitting either pairing.
-/
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

theorem firstVariation_norm_sq_add_integrable {d : Nat} (mu : Measure (UnitSphere d))
    (g k : UnitSphere d → Weight d) (hg : Measurable g) (hk : Measurable k)
    (h2g : Integrable (fun w => norm (g w)^2) mu)
    (h2k : Integrable (fun w => norm (k w)^2) mu) :
    Integrable (fun w => norm (g w+k w)^2) mu := by
  apply ((h2g.add h2k).const_mul 2).mono' ((hg.add hk).norm.pow_const 2).aestronglyMeasurable
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change norm (g w + k w)^2 ≤ 2 * (norm (g w)^2 + norm (k w)^2)
  have hs := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (g w) (k w)) 2
  nlinarith [sq_nonneg (norm (g w)-norm (k w))]

theorem firstVariation_norm_sq_sub_integrable {d : Nat} (mu : Measure (UnitSphere d))
    (g k : UnitSphere d → Weight d) (hg : Measurable g) (hk : Measurable k)
    (h2g : Integrable (fun w => norm (g w)^2) mu)
    (h2k : Integrable (fun w => norm (k w)^2) mu) :
    Integrable (fun w => norm (g w-k w)^2) mu := by
  simpa only [sub_eq_add_neg, norm_neg] using
    firstVariation_norm_sq_add_integrable mu g (fun w => -k w) hg hk.neg h2g
      (by simpa only [norm_neg] using h2k)

theorem HasSphereFirstVariation.congr_function {d : Nat} {mu : Measure (UnitSphere d)}
    {J K : Measure (UnitSphere d) → Real} {g : UnitSphere d → Weight d}
    (H : HasSphereFirstVariation mu J g) (he : ∀ nu, J nu = K nu) :
    HasSphereFirstVariation mu K g := by
  have hfun : J = K := funext he
  exact hfun ▸ H

/-- Changing a measurable representative on a null set preserves every test
identity and the source L2/tangency conditions. Pointwise values on that null
set are deliberately not asserted to have any canonical meaning. -/
theorem HasSphereFirstVariation.congr_gradient_ae {d : Nat} {mu : Measure (UnitSphere d)}
    {J : Measure (UnitSphere d) → Real} {g k : UnitSphere d → Weight d}
    (H : HasSphereFirstVariation mu J g) (hk : Measurable k) (he : g =ᵐ[mu] k) :
    HasSphereFirstVariation mu J k := by
  refine ⟨hk, ?_, ?_, ?_⟩
  · filter_upwards [H.tangent_ae, he] with w hw hew
    simpa only [hew] using hw
  · exact H.norm_sq_integrable.congr (he.mono (fun w hw => congrArg (fun v => norm v^2) hw))
  · intro V
    apply (H.derivative V).congr_deriv
    apply integral_congr_ae
    filter_upwards [he] with w hw
    rw [hw]

theorem HasSphereFirstVariation.add {d : Nat} {mu : Measure (UnitSphere d)}
    [IsFiniteMeasure mu] {J K : Measure (UnitSphere d) → Real}
    {g k : UnitSphere d → Weight d}
    (H : HasSphereFirstVariation mu J g) (G : HasSphereFirstVariation mu K k) :
    HasSphereFirstVariation mu (fun nu => J nu+K nu) (fun w => g w+k w) := by
  refine ⟨H.measurable_gradient.add G.measurable_gradient, ?_,
    firstVariation_norm_sq_add_integrable mu g k H.measurable_gradient G.measurable_gradient
      H.norm_sq_integrable G.norm_sq_integrable, ?_⟩
  · filter_upwards [H.tangent_ae, G.tangent_ae] with w hw hk'
    simp only [inner_add_right, hw, hk', add_zero]
  · intro V
    apply ((H.derivative V).add (G.derivative V)).congr_deriv
    simp only [inner_add_left]
    exact (integral_add (V.pairing_integrable mu g H.integrable)
      (V.pairing_integrable mu k G.integrable)).symm

theorem HasSphereFirstVariation.sub {d : Nat} {mu : Measure (UnitSphere d)}
    [IsFiniteMeasure mu] {J K : Measure (UnitSphere d) → Real}
    {g k : UnitSphere d → Weight d}
    (H : HasSphereFirstVariation mu J g) (G : HasSphereFirstVariation mu K k) :
    HasSphereFirstVariation mu (fun nu => J nu-K nu) (fun w => g w-k w) := by
  refine ⟨H.measurable_gradient.sub G.measurable_gradient, ?_,
    firstVariation_norm_sq_sub_integrable mu g k H.measurable_gradient G.measurable_gradient
      H.norm_sq_integrable G.norm_sq_integrable, ?_⟩
  · filter_upwards [H.tangent_ae, G.tangent_ae] with w hw hk'
    simp only [inner_sub_right, hw, hk', sub_self]
  · intro V
    apply ((H.derivative V).sub (G.derivative V)).congr_deriv
    simp only [inner_sub_left]
    exact (integral_sub (V.pairing_integrable mu g H.integrable)
      (V.pairing_integrable mu k G.integrable)).symm

end PaperFormalization.MatrixFactorization
