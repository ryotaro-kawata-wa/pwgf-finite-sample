import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-! # Regularity of uniformly controlled scalar series

This is an abstract bridge for weighted moment residuals. The norm majorant
ensures that `tsum` denotes a convergent series at every point of the branch;
the summable Lipschitz constants control differences of that sum. These are
separate hypotheses: continuity in the manuscript's weighted Hilbert norm alone
would not establish regularity of its weighted l1 residual.

The particle-model instantiation still has to derive both majorants from the
feature growth, conditional population moments, and particle-path estimates.
No conditional-law, spectral, or particle-model theorem is asserted here.
-/

open MeasureTheory Set
open scoped NNReal

namespace PaperFormalization.Continuous

/-- A uniform summable norm envelope gives pointwise summability on the given set. -/
theorem weighted_series_summable (f : ℕ → ℝ → ℝ) (majorant : ℕ → ℝ) (s : Set ℝ)
    (hmajorant : Summable majorant)
    (hbound : ∀ n x, x ∈ s → ‖f n x‖ ≤ majorant n)
    (x : ℝ) (hx : x ∈ s) : Summable (fun n => f n x) :=
  hmajorant.of_norm_bounded (fun n => hbound n x hx)

/-- The sum has Lipschitz constant equal to the sum of the individual constants. -/
theorem weighted_series_lipschitzOn (f : ℕ → ℝ → ℝ) (majorant : ℕ → ℝ)
    (K : ℕ → ℝ≥0) (s : Set ℝ) (hmajorant : Summable majorant)
    (hbound : ∀ n x, x ∈ s → ‖f n x‖ ≤ majorant n)
    (hK : Summable K) (hLip : ∀ n, LipschitzOnWith (K n) (f n) s) :
    LipschitzOnWith (∑' n, K n) (fun x => ∑' n, f n x) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hxsum := weighted_series_summable f majorant s hmajorant hbound x hx
  have hysum := weighted_series_summable f majorant s hmajorant hbound y hy
  have hKreal : Summable (fun n => (K n : ℝ)) := NNReal.summable_coe.mpr hK
  rw [dist_eq_norm, ← hxsum.tsum_sub hysum, NNReal.coe_tsum]
  apply tsum_of_norm_bounded (HasSum.mul_right (dist x y) hKreal.hasSum)
  intro n
  simpa only [dist_eq_norm] using (hLip n).dist_le_mul x hx y hy

/-- On a closed branch the uniformly controlled series is absolutely continuous. -/
theorem weighted_series_ac (f : ℕ → ℝ → ℝ) (majorant : ℕ → ℝ)
    (K : ℕ → ℝ≥0) (a b : ℝ) (hmajorant : Summable majorant)
    (hbound : ∀ n x, x ∈ uIcc a b → ‖f n x‖ ≤ majorant n)
    (hK : Summable K) (hLip : ∀ n, LipschitzOnWith (K n) (f n) (uIcc a b)) :
    AbsolutelyContinuousOnInterval (fun x => ∑' n, f n x) a b :=
  (weighted_series_lipschitzOn f majorant K (uIcc a b)
    hmajorant hbound hK hLip).absolutelyContinuousOnInterval

/-- The same branch sum is interval-integrable; no order of the endpoints is needed. -/
theorem weighted_series_intervalIntegrable (f : ℕ → ℝ → ℝ) (majorant : ℕ → ℝ)
    (K : ℕ → ℝ≥0) (a b : ℝ) (hmajorant : Summable majorant)
    (hbound : ∀ n x, x ∈ uIcc a b → ‖f n x‖ ≤ majorant n)
    (hK : Summable K) (hLip : ∀ n, LipschitzOnWith (K n) (f n) (uIcc a b)) :
    IntervalIntegrable (fun x => ∑' n, f n x) volume a b :=
  (weighted_series_ac f majorant K a b hmajorant hbound hK hLip).continuousOn.intervalIntegrable

end PaperFormalization.Continuous
