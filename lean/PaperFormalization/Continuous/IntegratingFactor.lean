import PaperFormalization.Continuous.Propagator
import PaperFormalization.Continuous.AbsoluteContinuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-! # The integrating factor for an interval-integrable real coefficient -/

open MeasureTheory Set Filter

namespace PaperFormalization.Continuous

/-- The positive integrating factor based at `s`. -/
noncomputable def integratingFactor (beta : ℝ → ℝ) (s u : ℝ) : ℝ :=
  Real.exp (∫ v in s..u, beta v)

theorem integratingFactor_pos (beta : ℝ → ℝ) (s u : ℝ) :
    0 < integratingFactor beta s u := Real.exp_pos _

@[simp] theorem integratingFactor_self (beta : ℝ → ℝ) (s : ℝ) :
    integratingFactor beta s s = 1 := by simp [integratingFactor]

/-- Reversing the propagator endpoints yields the integrating factor. -/
theorem integratingFactor_eq_propagator (beta : ℝ → ℝ) (s u : ℝ) :
    integratingFactor beta s u = propagator beta s u := by
  unfold integratingFactor propagator
  rw [intervalIntegral.integral_symm s u, neg_neg]

/-- Interval integrability is enough for absolute continuity of the integrating factor. -/
theorem integratingFactor_ac (beta : ℝ → ℝ) (s t : ℝ)
    (hbeta : IntervalIntegrable beta volume s t) :
    AbsolutelyContinuousOnInterval (integratingFactor beta s) s t := by
  exact ac_exp (fun u => ∫ v in s..u, beta v) s t
    (hbeta.absolutelyContinuousOnInterval_intervalIntegral (by simp))

/-- The integrating factor has derivative `w * beta` almost everywhere on the interval. -/
theorem integratingFactor_ae_hasDerivAt (beta : ℝ → ℝ) (s t : ℝ)
    (hbeta : IntervalIntegrable beta volume s t) :
    ∀ᵐ u ∂volume, u ∈ uIcc s t →
      HasDerivAt (integratingFactor beta s) (integratingFactor beta s u * beta u) u := by
  filter_upwards [hbeta.ae_hasDerivAt_integral] with u hu
  intro humem
  exact (hu humem s (by simp)).exp

/-- The propagator cancels the integrating factor at the terminal endpoint. -/
theorem propagator_mul_integratingFactor_self (beta : ℝ → ℝ) (s t : ℝ) :
    propagator beta t s * integratingFactor beta s t = 1 := by
  simp [propagator, integratingFactor, ← Real.exp_add]

/-- The same rescaling converts the weighted forcing to the propagator kernel. -/
theorem propagator_mul_integratingFactor (beta : ℝ → ℝ) (s u t : ℝ)
    (hsu : IntervalIntegrable beta volume s u)
    (hst : IntervalIntegrable beta volume s t) :
    propagator beta t s * integratingFactor beta s u = propagator beta t u := by
  rw [integratingFactor_eq_propagator]
  exact propagator_mul beta u s t hsu.symm hst

end PaperFormalization.Continuous
