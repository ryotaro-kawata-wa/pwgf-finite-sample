import PaperFormalization.Continuous.WeightedSeries
import Mathlib.Analysis.Normed.Group.Uniform

/-! # The literal weighted norm residual of empirical and population moment paths

The coordinate spaces may depend on the feature index. They need only be normed
additive commutative groups for this analytic bridge. `E` and `P` are supplied
moment paths; their conditional-law/empirical definitions, feature bounds, and
coordinate Lipschitz bounds remain model-specific inputs. Both the value series
and its rate series have explicit, separate summability hypotheses.

For the source's indexing by `m >= 1`, instantiate coordinate `n` with feature
`m = n + 1`, `w n = L_D * a_(n+1)`, `E` with its empirical moment, and `P` with
its conditional population moment. No equality with a conditional expectation
is assumed or proved by naming the abstract input `P`. The remaining obligations
are the coordinate amplitude and Lipschitz estimates and the two summability
inputs, under the original population-field conditioning and feature hypotheses.
The resulting rate is the explicit sum of `w n * (KE n + KP n)`: dependence on
particle radius, dimension, moments, and drift bound is retained in these inputs.
-/

open MeasureTheory Set
open scoped NNReal

namespace PaperFormalization.Manuscript

open Continuous

variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]

/-- One weighted norm discrepancy between the supplied moment paths. -/
noncomputable def momentResidualTerm (w : ℕ → ℝ≥0)
    (E P : ∀ n, ℝ → H n) (n : ℕ) (t : ℝ) : ℝ :=
  (w n : ℝ) * ‖E n t - P n t‖

/-- The countable weighted l1 moment residual, with its convergence proved below. -/
noncomputable def momentResidual (w : ℕ → ℝ≥0)
    (E P : ∀ n, ℝ → H n) (t : ℝ) : ℝ :=
  ∑' n, momentResidualTerm w E P n t

/-- Every residual term is nonnegative because its weight and norm are nonnegative. -/
theorem momentResidualTerm_nonneg (w : ℕ → ℝ≥0)
    (E P : ∀ n, ℝ → H n) (n : ℕ) (t : ℝ) :
    0 ≤ momentResidualTerm w E P n t :=
  mul_nonneg (w n).coe_nonneg (norm_nonneg _)

/-- Separate coordinate amplitude bounds give the required scalar norm majorant. -/
theorem momentResidualTerm_norm_le (w : ℕ → ℝ≥0)
    (E P : ∀ n, ℝ → H n) (AE AP : ℕ → ℝ) (n : ℕ) (t : ℝ)
    (hE : ‖E n t‖ ≤ AE n) (hP : ‖P n t‖ ≤ AP n) :
    ‖momentResidualTerm w E P n t‖ ≤ (w n : ℝ) * (AE n + AP n) := by
  rw [Real.norm_of_nonneg (momentResidualTerm_nonneg w E P n t)]
  exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hE hP))
    (w n).coe_nonneg

/-- Summability of the amplitude envelope proves convergence of the literal residual series. -/
theorem momentResidual_summable (w : ℕ → ℝ≥0)
    (E P : ∀ n, ℝ → H n) (AE AP : ℕ → ℝ) (s : Set ℝ)
    (hA : Summable (fun n => (w n : ℝ) * (AE n + AP n)))
    (hE : ∀ n t, t ∈ s → ‖E n t‖ ≤ AE n)
    (hP : ∀ n t, t ∈ s → ‖P n t‖ ≤ AP n)
    (t : ℝ) (ht : t ∈ s) : Summable (fun n => momentResidualTerm w E P n t) :=
  weighted_series_summable (momentResidualTerm w E P)
    (fun n => (w n : ℝ) * (AE n + AP n)) s hA
    (fun n t ht => momentResidualTerm_norm_le w E P AE AP n t
      (hE n t ht) (hP n t ht)) t ht

/-- The total residual is nonnegative. -/
theorem momentResidual_nonneg (w : ℕ → ℝ≥0)
    (E P : ∀ n, ℝ → H n) (t : ℝ) : 0 ≤ momentResidual w E P t :=
  tsum_nonneg (fun n => momentResidualTerm_nonneg w E P n t)

/-- The convergent amplitude envelope bounds the total residual. -/
theorem momentResidual_le_tsum_majorant (w : ℕ → ℝ≥0)
    (E P : ∀ n, ℝ → H n) (AE AP : ℕ → ℝ) (s : Set ℝ)
    (hA : Summable (fun n => (w n : ℝ) * (AE n + AP n)))
    (hE : ∀ n t, t ∈ s → ‖E n t‖ ≤ AE n)
    (hP : ∀ n t, t ∈ s → ‖P n t‖ ≤ AP n)
    (t : ℝ) (ht : t ∈ s) :
    momentResidual w E P t ≤ ∑' n, (w n : ℝ) * (AE n + AP n) := by
  apply (momentResidual_summable w E P AE AP s hA hE hP t ht).tsum_le_tsum _ hA
  intro n
  simpa only [Real.norm_of_nonneg (momentResidualTerm_nonneg w E P n t)] using
    momentResidualTerm_norm_le w E P AE AP n t (hE n t ht) (hP n t ht)

/-- Subtraction, norm, and nonnegative scalar multiplication give each term's rate. -/
theorem momentResidualTerm_lipschitzOn (w : ℕ → ℝ≥0)
    (E P : ∀ n, ℝ → H n) (KE KP : ℕ → ℝ≥0) (s : Set ℝ) (n : ℕ)
    (hE : LipschitzOnWith (KE n) (E n) s)
    (hP : LipschitzOnWith (KP n) (P n) s) :
    LipschitzOnWith (w n * (KE n + KP n)) (momentResidualTerm w E P n) s := by
  have hnorm : LipschitzOnWith (KE n + KP n) (fun t => ‖E n t - P n t‖) s := by
    simpa only [one_mul, Function.comp_def] using
      lipschitzWith_one_norm.comp_lipschitzOnWith (hE.sub hP)
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht u hu
  calc
    dist (momentResidualTerm w E P n t) (momentResidualTerm w E P n u) =
        (w n : ℝ) * dist ‖E n t - P n t‖ ‖E n u - P n u‖ := by
      simp only [momentResidualTerm, Real.dist_eq, ← mul_sub, abs_mul,
        abs_of_nonneg (w n).coe_nonneg]
    _ ≤ (w n : ℝ) * ((KE n + KP n : ℝ≥0) * dist t u) :=
      mul_le_mul_of_nonneg_left (hnorm.dist_le_mul t ht u hu) (w n).coe_nonneg
    _ = (w n * (KE n + KP n) : ℝ≥0) * dist t u := by
      rw [NNReal.coe_mul, mul_assoc]

/-- The literal weighted residual is Lipschitz under the two separate summable envelopes. -/
theorem momentResidual_lipschitzOn (w : ℕ → ℝ≥0)
    (E P : ∀ n, ℝ → H n) (AE AP : ℕ → ℝ) (KE KP : ℕ → ℝ≥0) (s : Set ℝ)
    (hA : Summable (fun n => (w n : ℝ) * (AE n + AP n)))
    (hE : ∀ n t, t ∈ s → ‖E n t‖ ≤ AE n)
    (hP : ∀ n t, t ∈ s → ‖P n t‖ ≤ AP n)
    (hK : Summable (fun n => (w n : ℝ) * ((KE n : ℝ) + (KP n : ℝ))))
    (hLE : ∀ n, LipschitzOnWith (KE n) (E n) s)
    (hLP : ∀ n, LipschitzOnWith (KP n) (P n) s) :
    LipschitzOnWith (∑' n, w n * (KE n + KP n)) (momentResidual w E P) s := by
  have hKnn : Summable (fun n => w n * (KE n + KP n)) := by
    apply NNReal.summable_coe.mp
    simpa only [NNReal.coe_mul, NNReal.coe_add] using hK
  exact weighted_series_lipschitzOn (momentResidualTerm w E P)
    (fun n => (w n : ℝ) * (AE n + AP n)) (fun n => w n * (KE n + KP n)) s hA
    (fun n t ht => momentResidualTerm_norm_le w E P AE AP n t
      (hE n t ht) (hP n t ht)) hKnn
    (fun n => momentResidualTerm_lipschitzOn w E P KE KP s n (hLE n) (hLP n))

/-- The actual weighted norm residual is absolutely continuous on a closed branch. -/
theorem momentResidual_ac (w : ℕ → ℝ≥0)
    (E P : ∀ n, ℝ → H n) (AE AP : ℕ → ℝ) (KE KP : ℕ → ℝ≥0) (a b : ℝ)
    (hA : Summable (fun n => (w n : ℝ) * (AE n + AP n)))
    (hE : ∀ n t, t ∈ uIcc a b → ‖E n t‖ ≤ AE n)
    (hP : ∀ n t, t ∈ uIcc a b → ‖P n t‖ ≤ AP n)
    (hK : Summable (fun n => (w n : ℝ) * ((KE n : ℝ) + (KP n : ℝ))))
    (hLE : ∀ n, LipschitzOnWith (KE n) (E n) (uIcc a b))
    (hLP : ∀ n, LipschitzOnWith (KP n) (P n) (uIcc a b)) :
    AbsolutelyContinuousOnInterval (momentResidual w E P) a b :=
  (momentResidual_lipschitzOn w E P AE AP KE KP (uIcc a b)
    hA hE hP hK hLE hLP).absolutelyContinuousOnInterval

/-- The literal residual is interval-integrable on the branch, in either endpoint order. -/
theorem momentResidual_intervalIntegrable (w : ℕ → ℝ≥0)
    (E P : ∀ n, ℝ → H n) (AE AP : ℕ → ℝ) (KE KP : ℕ → ℝ≥0) (a b : ℝ)
    (hA : Summable (fun n => (w n : ℝ) * (AE n + AP n)))
    (hE : ∀ n t, t ∈ uIcc a b → ‖E n t‖ ≤ AE n)
    (hP : ∀ n t, t ∈ uIcc a b → ‖P n t‖ ≤ AP n)
    (hK : Summable (fun n => (w n : ℝ) * ((KE n : ℝ) + (KP n : ℝ))))
    (hLE : ∀ n, LipschitzOnWith (KE n) (E n) (uIcc a b))
    (hLP : ∀ n, LipschitzOnWith (KP n) (P n) (uIcc a b)) :
    IntervalIntegrable (momentResidual w E P) volume a b :=
  (momentResidual_ac w E P AE AP KE KP a b hA hE hP hK hLE hLP).continuousOn.intervalIntegrable

end PaperFormalization.Manuscript
