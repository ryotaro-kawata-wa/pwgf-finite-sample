import PaperFormalization.Manuscript.FeatureWeights
import PaperFormalization.Manuscript.UniformFeatureWeights

/-! # Uniform logarithmic scale and lower-order growth bounds

The scale is the literal manuscript chi. Bounds for the lower-order terms
are chosen before localization and population scales K,D are introduced.
-/

open Filter Asymptotics
open scoped Topology BigOperators

namespace PaperFormalization.Manuscript

/-- The source logarithmic scale, with e represented by exp 1. -/
noncomputable def featureScaleChi (p u : ℝ) : ℝ :=
  (Real.log (Real.exp 1 + u)) ^ (p / (p - 1))

/-- The logarithm underlying chi is at least one on the source domain. -/
theorem one_le_featureScaleLog (u : ℝ) (hu : 0 ≤ u) :
    1 ≤ Real.log (Real.exp 1 + u) := by
  calc
    1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ _ := Real.log_le_log (Real.exp_pos 1) (by linarith)

/-- Chi is at least one, so fixed additive exponent constants can be absorbed. -/
theorem one_le_featureScaleChi (p u : ℝ) (hp : 1 < p) (hu : 0 ≤ u) :
    1 ≤ featureScaleChi p u := by
  exact Real.one_le_rpow (one_le_featureScaleLog u hu) (by positivity)

/-- Exact source scale comparison, with an explicit constant depending only
on the fixed multiplier and decay exponent. -/
theorem featureScaleChi_scale_le (p c u : ℝ)
    (hp : 1 < p) (hc : 0 < c) (hu : 0 ≤ u) :
    featureScaleChi p (c * (1 + u) + 1) ≤
      (1 + Real.log (c + 2)) ^ (p / (p - 1)) * featureScaleChi p u := by
  have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
  have hl := one_le_featureScaleLog u hu
  have hc2 : 0 < c + 2 := by linarith
  have hlogc : 0 ≤ Real.log (c + 2) := Real.log_nonneg (by linarith)
  have hprod : Real.exp 1 + c * (1 + u) + 1 ≤ (c + 2) * (Real.exp 1 + u) := by
    nlinarith
  have hlog : Real.log (Real.exp 1 + (c * (1 + u) + 1)) ≤
      (1 + Real.log (c + 2)) * Real.log (Real.exp 1 + u) := by
    calc
      _ ≤ Real.log ((c + 2) * (Real.exp 1 + u)) :=
        Real.log_le_log (by positivity) (by linarith)
      _ = Real.log (c + 2) + Real.log (Real.exp 1 + u) :=
        Real.log_mul hc2.ne' (by positivity)
      _ ≤ _ := by nlinarith
  unfold featureScaleChi
  calc
    _ ≤ ((1 + Real.log (c + 2)) * Real.log (Real.exp 1 + u)) ^ (p / (p - 1)) :=
      Real.rpow_le_rpow (by linarith [one_le_featureScaleLog (c * (1 + u) + 1) (by positivity)]) hlog (by positivity)
    _ = _ := Real.mul_rpow (by positivity) (by linarith)

/-- Little-o absorption made uniform over every positive integer. The finite
prefix contributes one constant independent of any future K,D scales. -/
theorem exists_uniform_feature_growth_bound (p q A B C D epsilon : ℝ)
    (hp : 1 < p) (hq : q < p) (hepsilon : 0 < epsilon) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
      A * ((n + 1 : ℕ) : ℝ) ^ q +
        B * (((n + 1 : ℕ) : ℝ) * Real.log (n + 1)) + C * (n + 1) + D * Real.log (n + 1) ≤
      epsilon * ((n + 1 : ℕ) : ℝ) ^ p + M := by
  let f : ℕ → ℝ := fun n => A * ((n + 1 : ℕ) : ℝ) ^ q +
    B * (((n + 1 : ℕ) : ℝ) * Real.log (n + 1)) + C * (n + 1) + D * Real.log (n + 1)
  have hlimit : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hsmall := hlimit.eventually ((growth_isLittleO p q A B C D hp hq).bound hepsilon)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  let M : ℝ := ∑ n ∈ Finset.range N, ‖f n‖
  have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨M, hM, ?_⟩
  intro n
  change f n ≤ epsilon * ((n + 1 : ℕ) : ℝ) ^ p + M
  by_cases hn : N ≤ n
  · have h := hN n hn
    have hm : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have hf : f n ≤ epsilon * ((n + 1 : ℕ) : ℝ) ^ p := by
      apply (le_abs_self (f n)).trans
      simp only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hm p)] at h
      simpa only [f, Nat.cast_add, Nat.cast_one] using h
    linarith
  · have hf : ‖f n‖ ≤ M := Finset.single_le_sum (fun _ _ => norm_nonneg _)
      (Finset.mem_range.mpr (by omega))
    have hpow : 0 ≤ epsilon * ((n + 1 : ℕ) : ℝ) ^ p := by positivity
    rw [Real.norm_eq_abs] at hf
    exact (le_abs_self (f n)).trans (hf.trans (by linarith))

/-- Uniform exponential absorption with the exact remaining c/4 decay. The
constant is chosen before the scale u and the positive integer index. -/
theorem exists_uniform_feature_exponent_bound (c g p q alpha : ℝ)
    (hc : 0 < c) (hp : 1 < p) (hq : q < p) :
    ∃ M : ℝ, 0 < M ∧ ∀ u : ℝ, 0 ≤ u → ∀ n : ℕ,
      -c * ((n + 1 : ℕ) : ℝ) ^ p + g * ((n + 1 : ℕ) : ℝ) ^ q +
        (1 / alpha) * (((n + 1 : ℕ) : ℝ) * Real.log (n + 1)) + Real.log (n + 1) +
        ((n + 1 : ℕ) : ℝ) * Real.log (Real.exp 1 + u) ≤
      M * featureScaleChi p u - (c / 4) * ((n + 1 : ℕ) : ℝ) ^ p := by
  obtain ⟨A, hA, hbound⟩ := exists_uniform_feature_growth_bound p q g (1 / alpha) 0 1 (c / 2)
    hp hq (by positivity)
  let B := featureYoungCoefficient (c / 4) p
  have hB : 0 < B := featureYoungCoefficient_pos (c / 4) p (by positivity) hp
  refine ⟨A + B, by positivity, ?_⟩
  intro u hu n
  have hlog : 0 ≤ Real.log (Real.exp 1 + u) := (by norm_num : (0 : ℝ) ≤ 1).trans
    (one_le_featureScaleLog u hu)
  have hY := feature_weighted_young (c / 4) p ((n + 1 : ℕ) : ℝ)
    (Real.log (Real.exp 1 + u)) (by positivity) hp (by positivity) hlog
  have hlow := hbound n
  simp only [zero_mul, add_zero, one_mul] at hlow
  have hchi := one_le_featureScaleChi p u hp hu
  have hAchi : A ≤ A * featureScaleChi p u := by nlinarith
  change _ ≤ (c / 4) * ((n + 1 : ℕ) : ℝ) ^ p + B * featureScaleChi p u at hY
  linarith

end PaperFormalization.Manuscript
