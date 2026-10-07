import PaperFormalization.MatrixFactorization.SphericalContraction

/-! # MF03: source-facing first variation and complete regularizer endpoint

MF03 checkpoint candidate; see MF03_VALIDATION.md for execution status.
This file applies the pointwise and integral results to
one original product model. Source conditions alone supply every derivative
and genuine integrability fact. This is the regularization term ONLY, not a
claim that the fitting term or the four local MF statements are finished.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def regularizerGradient {d : Nat} (P : SphericalVariation d)
    (lambda p : Real) (w : UnitSphere d) : Weight d :=
  (lambda*(variationTransport P 0)^(p/2-1)) • assignedGradient P.pole w

/-- Genuine integrability is retained before the first-variation pairing is used. -/
theorem regularizerGradient_pairing_integrable {d : Nat} (P : SphericalVariation d)
    (lambda p : Real) (i : Fin 2) :
    Integrable (fun w => inner Real (regularizerGradient P lambda p w) (P.velocity i w))
      (P.measure i) := by
  simpa only [regularizerGradient,real_inner_smul_left] using
    (variation_integrable P i).1.const_mul (lambda*(variationTransport P 0)^(p/2-1))

theorem regularizerGradient_pairing {d : Nat} (P : SphericalVariation d)
    (lambda p : Real) :
    (∑ i : Fin 2, ∫ w, inner Real (regularizerGradient P lambda p w) (P.velocity i w) ∂P.measure i) =
      lambda*(variationTransport P 0)^(p/2-1)*variationFirst P := by
  have hi := regularizerGradient_pairing_integrable P lambda p
  simp only [regularizerGradient,real_inner_smul_left,integral_const_mul,
    variationFirst,marginalCostFirst,Finset.mul_sum]

/-- The first derivative is represented by the original spherical gradient in
both factors, including zero target transport and all real p>2. -/
theorem metricRegularizer_first_variation {d : Nat} (P : SphericalVariation d)
    (lambda p : Real) (hlambda : 0 < lambda) (hp : 2 < p) :
    HasDerivAt (variationRegularizer P lambda p)
      (∑ i : Fin 2, ∫ w, inner Real (regularizerGradient P lambda p w) (P.velocity i w) ∂P.measure i) 0 := by
  rw [regularizerGradient_pairing]
  rcases eq_or_lt_of_le (variationTransport_initial_nonneg P) with hz | hz
  · have hzero := (metricRegularizer_zero_variations P lambda p hp hz.symm).1
    simpa only [hz.symm,Real.zero_rpow (show p/2-1 ≠ 0 by linarith),mul_zero,zero_mul] using hzero
  · exact (metricRegularizer_positive_variations P lambda p hlambda hp hz).1

/-- A nonzero L2 tangent direction has positive regularizer curvature away from
the target. No conclusion about fitting-plus-regularizer curvature is implied. -/
theorem metricRegularizer_second_strictly_positive {d : Nat} (P : SphericalVariation d)
    (lambda p : Real) (hlambda : 0 < lambda) (hp : 2 < p)
    (hZ : 0 < variationTransport P 0) (hE : 0 < variationEnergy P) :
    0 < deriv (deriv (variationRegularizer P lambda p)) 0 := by
  have hb : 0 < sphericalRadialWeight P.radius :=
    sphericalRadialWeight_pos (P.cap 0).radius_pos.le (P.cap 0).radius_lt
  have hc : 0 < lambda*(variationTransport P 0)^(p/2-1)*sphericalRadialWeight P.radius*variationEnergy P :=
    mul_pos (mul_pos (mul_pos hlambda (Real.rpow_pos_of_pos hZ _)) hb) hE
  exact hc.trans_le (metricRegularizer_second_lower_bound P lambda p hlambda hp hZ)

/-- Source endpoint: the exact underlying functional, all required integrals,
its first variation, positive-distance second variation and zero-target flatness.
The scalar derivative and radius domination premises are all discharged inside
this construction. The remaining MF fitting/flow geometry is explicitly separate. -/
theorem spherical_regularizer_source_variations {d : Nat} (P : SphericalVariation d)
    (lambda p : Real) (hlambda : 0 < lambda) (hp : 2 < p) :
    (∀ i : Fin 2,
      Integrable (fun w => inner Real (regularizerGradient P lambda p w) (P.velocity i w)) (P.measure i) ∧
      Integrable (fun w => assignedHessian P.pole w (P.velocity i w)) (P.measure i) ∧
      Integrable (fun w => (norm (P.velocity i w))^2) (P.measure i)) ∧
    HasDerivAt (variationRegularizer P lambda p)
      (∑ i : Fin 2, ∫ w, inner Real (regularizerGradient P lambda p w) (P.velocity i w) ∂P.measure i) 0 ∧
    (variationTransport P 0 = 0 →
      (∀ i, P.measure i = antipodalMeasure P.pole) ∧
      (variationRegularizer P lambda p =ᶠ[𝓝 (0 : Real)]
        (fun t => (lambda/p*(variationEnergy P)^(p/2))*|t|^p)) ∧
      HasDerivAt (deriv (variationRegularizer P lambda p)) 0 0) ∧
    (0 < variationTransport P 0 →
      HasDerivAt (deriv (variationRegularizer P lambda p))
        (lambda*(variationTransport P 0)^(p/2-1)*variationSecond P +
          lambda*(p-2)*(variationTransport P 0)^(p/2-2)*(variationFirst P)^2) 0 ∧
      lambda*(variationTransport P 0)^(p/2-1)*sphericalRadialWeight P.radius*variationEnergy P ≤
        deriv (deriv (variationRegularizer P lambda p)) 0) := by
  refine ⟨?_,metricRegularizer_first_variation P lambda p hlambda hp,?_,?_⟩
  · intro i
    exact ⟨regularizerGradient_pairing_integrable P lambda p i,
      (variation_integrable P i).2.1,(variation_integrable P i).2.2⟩
  · intro hz
    exact ⟨zeroVariation_original_laws P hz,variationRegularizer_zero_formula P lambda p hz,
      (metricRegularizer_zero_variations P lambda p hp hz).2⟩
  · intro hz
    exact ⟨(metricRegularizer_positive_variations P lambda p hlambda hp hz).2,
      metricRegularizer_second_lower_bound P lambda p hlambda hp hz⟩

end PaperFormalization.MatrixFactorization
