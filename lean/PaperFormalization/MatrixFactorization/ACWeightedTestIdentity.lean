import PaperFormalization.MatrixFactorization.IntegralCharacteristicRegularity
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # MF31: time-weighted AC test identity

This is a scalar integration-by-parts step with true integrability, derived
from AC and its prescribed AE derivative. It includes signed endpoints.
-/
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

theorem ac_weighted_test_identity (m j eta : Real → Real) (s t : Real)
    (hm : AbsolutelyContinuousOnInterval m s t)
    (hj : IntervalIntegrable j volume s t)
    (hd : ∀ᵐ r : Real, r ∈ uIcc s t → HasDerivAt m (-j r) r)
    (heta : ContDiff Real 1 eta) :
    IntervalIntegrable (fun r => deriv eta r * m r - eta r * j r) volume s t ∧
    (∫ r in s..t, (deriv eta r * m r - eta r * j r)) = eta t * m t - eta s * m s := by
  have hprod : AbsolutelyContinuousOnInterval (fun r => eta r * m r) s t :=
    heta.contDiffOn.absolutelyContinuousOnInterval.mul hm
  have hint : IntervalIntegrable (fun r => deriv eta r * m r - eta r * j r) volume s t :=
    ((heta.continuous_deriv_one.continuousOn.mul hm.continuousOn).intervalIntegrable).sub
      (hj.continuousOn_mul heta.continuous.continuousOn)
  refine ⟨hint, integral_eq_sub_of_ac_ae_velocity hprod hint ?_⟩
  filter_upwards [hd] with r hr hmem
  have hh := ((heta.differentiable (by decide)) r).hasDerivAt.mul (hr hmem)
  convert hh using 1 <;>
    first | rfl | simp only [mul_neg, sub_eq_add_neg]

end PaperFormalization.MatrixFactorization
