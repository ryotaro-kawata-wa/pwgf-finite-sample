import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Scalar propagator for the time-dependent comparison coefficient

For a real coefficient `beta`, the argument order is `(t, s)` and the integral
runs from `s` to `t` with respect to Lebesgue measure. This is the propagator in
Steps 1 and 2 of `lem:piecewise-gronwall-forced-jumps`.

Lean's interval integral is a total definition, even for nonintegrable inputs.
Positivity and the value at equal endpoints hold for this raw definition.
Integral additivity, and hence the semigroup law, require the explicit interval
integrability hypotheses stated in the later declarations. The application to
the manuscript must discharge those hypotheses separately.
-/

open MeasureTheory

namespace PaperFormalization.Continuous

/-- The coefficient propagator from the starting time `s` to the terminal time `t`. -/
noncomputable def propagator (beta : ℝ → ℝ) (t s : ℝ) : ℝ :=
  Real.exp (-(∫ u in s..t, beta u))

/-- The real exponential gives a strictly positive propagator. -/
theorem propagator_pos (beta : ℝ → ℝ) (t s : ℝ) :
    0 < propagator beta t s :=
  Real.exp_pos _

/-- Nonnegativity is the sign condition needed for the finite affine comparison. -/
theorem propagator_nonneg (beta : ℝ → ℝ) (t s : ℝ) :
    0 ≤ propagator beta t s :=
  (propagator_pos beta t s).le

/-- A zero-length interval has unit propagator, including degenerate final branches. -/
@[simp] theorem propagator_self (beta : ℝ → ℝ) (t : ℝ) :
    propagator beta t t = 1 := by
  simp [propagator]

/-- Composition across two interval-integrable branches. Oriented integrals make
this identity valid without any ordering assumption on the three endpoints. -/
theorem propagator_mul (beta : ℝ → ℝ) (s u t : ℝ)
    (hleft : IntervalIntegrable beta volume s u)
    (hright : IntervalIntegrable beta volume u t) :
    propagator beta t u * propagator beta u s = propagator beta t s := by
  have hadd : (∫ v in u..t, beta v) + (∫ v in s..u, beta v) =
      ∫ v in s..t, beta v := by
    calc
      (∫ v in u..t, beta v) + (∫ v in s..u, beta v) =
          (∫ v in s..u, beta v) + (∫ v in u..t, beta v) := add_comm _ _
      _ = ∫ v in s..t, beta v :=
        intervalIntegral.integral_add_adjacent_intervals hleft hright
  unfold propagator
  rw [← Real.exp_add, ← neg_add, hadd]

/-- For ordered times, integrability on the containing interval supplies both
local hypotheses. No continuity or sign assumption on `beta` is required. -/
theorem propagator_mul_of_intervalIntegrable (beta : ℝ → ℝ) (s u t : ℝ)
    (hsu : s ≤ u) (hut : u ≤ t)
    (hbeta : IntervalIntegrable beta volume s t) :
    propagator beta t u * propagator beta u s = propagator beta t s := by
  apply propagator_mul beta s u t
  · apply hbeta.mono_set
    rw [Set.uIcc_of_le hsu, Set.uIcc_of_le (le_trans hsu hut)]
    intro v hv
    exact ⟨hv.1, le_trans hv.2 hut⟩
  · apply hbeta.mono_set
    rw [Set.uIcc_of_le hut, Set.uIcc_of_le (le_trans hsu hut)]
    intro v hv
    exact ⟨le_trans hsu hv.1, hv.2⟩

end PaperFormalization.Continuous
