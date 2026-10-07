import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Absolute continuity needed for the integrating factor

Composition uses a Lipschitz bound only on the image of the trajectory.
The exponential has such a bound because an absolutely continuous real
trajectory has bounded image on a compact interval. No C1 assumption on the
trajectory is introduced.
-/

open MeasureTheory Set Filter
open scoped Topology BigOperators NNReal

namespace PaperFormalization.Continuous

/-- A Lipschitz outer map preserves absolute continuity of a real trajectory. -/
theorem ac_comp_lipschitzOn (f g : ℝ → ℝ) (a b : ℝ) (K : ℝ≥0)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : LipschitzOnWith K g (f '' uIcc a b)) :
    AbsolutelyContinuousOnInterval (fun x => g (f x)) a b := by
  unfold AbsolutelyContinuousOnInterval at hf ⊢
  apply squeeze_zero' ?_ ?_ (by simpa using hf.const_mul (K : ℝ))
  · exact Filter.Eventually.of_forall fun _ =>
      Finset.sum_nonneg (fun _ _ => dist_nonneg)
  · rw [eventually_inf_principal]
    filter_upwards with E hE
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    exact hg.dist_le_mul _ ⟨_, (hE.left i hi).left, rfl⟩
      _ ⟨_, (hE.left i hi).right, rfl⟩

/-- Exponentiating an absolutely continuous real trajectory preserves absolute continuity. -/
theorem ac_exp (f : ℝ → ℝ) (a b : ℝ)
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => Real.exp (f x)) a b := by
  obtain ⟨C, hC⟩ := hf.exists_bound
  have hImage : f '' uIcc a b ⊆ Icc (-C) C := by
    rintro y ⟨x, hx, rfl⟩
    simpa only [Real.norm_eq_abs, abs_le, Set.mem_Icc] using hC x hx
  have hexp : ContDiffOn ℝ 1 Real.exp (Icc (-C) C) := Real.contDiff_exp.contDiffOn
  obtain ⟨K, hK⟩ := hexp.exists_lipschitzOnWith (by decide) (convex_Icc _ _) isCompact_Icc
  exact ac_comp_lipschitzOn f Real.exp a b K hf (hK.mono hImage)

/-- Every function is absolutely continuous on a one-point interval. -/
theorem ac_singleton (f : ℝ → ℝ) (t : ℝ) : AbsolutelyContinuousOnInterval f t t := by
  have hLip : LipschitzOnWith 0 f (uIcc t t) := by
    intro x hx y hy
    have hx' : x = t := by simpa using hx
    have hy' : y = t := by simpa using hy
    subst x
    subst y
    simp
  exact hLip.absolutelyContinuousOnInterval

end PaperFormalization.Continuous
