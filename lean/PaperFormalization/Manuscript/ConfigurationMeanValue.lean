import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-! # The actual configuration-field mean-value identity

A derivative along the particle interpolation and integrability of its action
suffice. The theorem derives the vector integral identity rather than assuming
it. Continuity of the derivative action is an optional stronger sufficient input.
-/

open MeasureTheory Set

namespace PaperFormalization.Manuscript

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Fundamental theorem of calculus on the literal affine configuration segment. -/
theorem configuration_mean_value (V : E → F) (D : ℝ → E →L[ℝ] F) (x y : E)
    (hD : ∀ s ∈ Icc (0 : ℝ) 1, HasFDerivAt V (D s) (y + s • (x - y)))
    (hint : IntervalIntegrable (fun s => D s (x - y)) volume 0 1) :
    V x - V y = ∫ s in (0 : ℝ)..1, D s (x - y) := by
  have hpath : ∀ s : ℝ, HasDerivAt (fun u : ℝ => y + u • (x - y)) (x - y) s := by
    intro s
    simpa only [one_smul, id_eq] using ((hasDerivAt_id s).smul_const (x - y)).const_add y
  have hcomp : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun u : ℝ => V (y + u • (x - y))) (D s (x - y)) s := by
    intro s hs
    exact (hD s (by simpa using hs)).comp_hasDerivAt s (hpath s)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hcomp hint
  simpa only [one_smul, zero_smul, add_zero, add_sub_cancel] using h.symm

/-- Continuous derivative action supplies the required Bochner integrability. -/
theorem configuration_mean_value_of_continuousOn (V : E → F)
    (D : ℝ → E →L[ℝ] F) (x y : E)
    (hD : ∀ s ∈ Icc (0 : ℝ) 1, HasFDerivAt V (D s) (y + s • (x - y)))
    (hcont : ContinuousOn (fun s => D s (x - y)) (Icc (0 : ℝ) 1)) :
    V x - V y = ∫ s in (0 : ℝ)..1, D s (x - y) :=
  configuration_mean_value V D x y hD (by
    apply ContinuousOn.intervalIntegrable
    simpa using hcont)

/-- For the negative-gradient field, the derived mean-value identity has the
source's minus sign in front of its Hessian action integral. -/
theorem configuration_difference_eq_neg_hessian_integral (V : E → F)
    (H : ℝ → E →L[ℝ] F) (x y : E)
    (hH : ∀ s ∈ Icc (0 : ℝ) 1, HasFDerivAt V (-H s) (y + s • (x - y)))
    (hint : IntervalIntegrable (fun s => H s (x - y)) volume 0 1) :
    V x - V y = -(∫ s in (0 : ℝ)..1, H s (x - y)) := by
  have h := configuration_mean_value V (fun s => -H s) x y hH hint.neg
  simpa only [neg_apply, intervalIntegral.integral_neg] using h

end PaperFormalization.Manuscript
