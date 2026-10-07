import PaperFormalization.Manuscript.WeightedFeatureDerivatives

/-! # Spatial differences of actual weighted feature derivatives

The first derivative's local Lipschitz bound uses coordinate C2 and the given
second derivative growth. The second derivative's local Lipschitz bound uses
existence of the coordinate third derivative and its original growth bound.
Continuity of that third derivative is not assumed. The exact source common
coefficient is retained: sum_m a_m L_m (1+D^m), without an extra factor.
-/

open scoped BigOperators

set_option maxSynthPendingDepth 8

namespace PaperFormalization.Manuscript

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)]

/-- Transfer summable coordinate operator bounds to the actual Hilbert-valued operator. -/
theorem norm_hilbertOperator_le_of_weighted_coordinate_bounds
    (L : E →L[ℝ] lp H 2) (d : ∀ n, E →L[ℝ] H n) (a b : ℕ → ℝ) (B : ℝ)
    (ha : ∀ n, 0 ≤ a n) (hB : 0 ≤ B) (hb : HasSum b B)
    (hcoord : ∀ v n, L v n = a n • d n v)
    (hbound : ∀ n, a n * ‖d n‖ ≤ b n) : ‖L‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro v
  apply norm_hilbertSum_le_of_hasSum_coordinate_majorant (L v)
    (fun n => b n * ‖v‖) _ (hb.mul_right ‖v‖)
  intro n
  rw [hcoord, norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha n)]
  calc
    a n * ‖d n v‖ ≤ a n * (‖d n‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left ((d n).le_opNorm v) (ha n)
    _ = (a n * ‖d n‖) * ‖v‖ := by ring
    _ ≤ b n * ‖v‖ := mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg v)

/-- The same transfer for a curried bilinear map, preserving both direction norms. -/
theorem norm_hilbertBilinear_le_of_weighted_coordinate_bounds
    (L : E →L[ℝ] (E →L[ℝ] lp H 2)) (d : ∀ n, E →L[ℝ] (E →L[ℝ] H n))
    (a b : ℕ → ℝ) (B : ℝ) (ha : ∀ n, 0 ≤ a n) (hB : 0 ≤ B) (hb : HasSum b B)
    (hcoord : ∀ u v n, L u v n = a n • d n u v)
    (hbound : ∀ n, a n * ‖d n‖ ≤ b n) : ‖L‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro u
  apply norm_hilbertOperator_le_of_weighted_coordinate_bounds (L u) (fun n => d n u)
    a (fun n => b n * ‖u‖) (B * ‖u‖) ha (mul_nonneg hB (norm_nonneg u))
    (hb.mul_right ‖u‖) (hcoord u)
  intro n
  calc
    a n * ‖d n u‖ ≤ a n * (‖d n‖ * ‖u‖) :=
      mul_le_mul_of_nonneg_left ((d n).le_opNorm u) (ha n)
    _ = (a n * ‖d n‖) * ‖u‖ := by ring
    _ ≤ b n * ‖u‖ := mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg u)

/-- The weighted coordinate first-derivative difference has the original
common local coefficient, using only C2 and the second derivative growth. -/
theorem sourceFeatureScale_mul_norm_fderiv_sub_le
    (c C g p q D : ℝ) (φ : ∀ n, E → H n) (hC : 0 ≤ C) (hD : 1 ≤ D)
    (hφ : ∀ n, ContDiff ℝ 2 (φ n))
    (hgrowth₂ : ∀ n z, ‖iteratedFDeriv ℝ 2 (φ n) z‖ ≤
      featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1 - 2)))
    (x y : E) (hx : ‖x‖ ≤ D) (hy : ‖y‖ ≤ D) (n : ℕ) :
    sourceFeatureScale c p n * ‖fderiv ℝ (φ n) x - fderiv ℝ (φ n) y‖ ≤
      featureWeight c C g p q n * (1 + D ^ (n + 1)) * ‖x - y‖ := by
  have h := feature_derivative_sub_le_local_envelope (fderiv ℝ (φ n)) D
    (featureGrowth C g q n) n 2 hD (featureGrowth_nonneg C g q hC n)
    (fun z _ => ((hφ n).contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt_one)
    (fun z _ => by simpa only [norm_second_fderiv_eq_iterated] using hgrowth₂ n z)
    x y hx hy
  have hw := mul_le_mul_of_nonneg_left h (sourceFeatureScale_pos c p n).le
  simpa only [sourceFeatureScale, featureWeight, featureGrowth, mul_assoc] using hw

/-- Existence and growth of the coordinate third derivative imply the second
spatial difference bound; continuity of D3 is not an input. -/
theorem sourceFeatureScale_mul_norm_second_fderiv_sub_le
    (c C g p q D : ℝ) (φ : ∀ n, E → H n) (hC : 0 ≤ C) (hD : 1 ≤ D)
    (hthird : ∀ n z, DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ (φ n))) z)
    (hgrowth₃ : ∀ n z, ‖iteratedFDeriv ℝ 3 (φ n) z‖ ≤
      featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1 - 3)))
    (x y : E) (hx : ‖x‖ ≤ D) (hy : ‖y‖ ≤ D) (n : ℕ) :
    sourceFeatureScale c p n *
        ‖fderiv ℝ (fderiv ℝ (φ n)) x - fderiv ℝ (fderiv ℝ (φ n)) y‖ ≤
      featureWeight c C g p q n * (1 + D ^ (n + 1)) * ‖x - y‖ := by
  have h := feature_derivative_sub_le_local_envelope (fderiv ℝ (fderiv ℝ (φ n))) D
    (featureGrowth C g q n) n 3 hD (featureGrowth_nonneg C g q hC n)
    (fun z _ => hthird n z)
    (fun z _ => by simpa only [norm_third_fderiv_eq_iterated] using hgrowth₃ n z)
    x y hx hy
  have hw := mul_le_mul_of_nonneg_left h (sourceFeatureScale_pos c p n).le
  simpa only [sourceFeatureScale, featureWeight, featureGrowth, mul_assoc] using hw

section Source

variable [∀ n, CompleteSpace (H n)]
variable (c C g p q : ℝ) (φ : ∀ n, E → H n)
  (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
  (hφ : ∀ n, ContDiff ℝ 2 (φ n))
  (hgrowth : ∀ n x k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) x‖ ≤
    featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1 - k)))

include hc hC hp hq hφ hgrowth

/-- The actual source first derivative is locally Lipschitz with the exact
coefficient sum_m a_m L_m (1+D^m). -/
theorem norm_fderiv_sourceWeightedFeatureMap_sub_le (D : ℝ) (hD : 1 ≤ D)
    (x y : E) (hx : ‖x‖ ≤ D) (hy : ‖y‖ ≤ D) :
    ‖fderiv ℝ (sourceWeightedFeatureMap c p φ) x - fderiv ℝ (sourceWeightedFeatureMap c p φ) y‖ ≤
      (∑' n, featureWeight c C g p q n * (1 + D ^ (n + 1))) * ‖x - y‖ := by
  let M := fun n => featureWeight c C g p q n * (1 + D ^ (n + 1))
  have hM := summable_feature_regularity_envelope c C g p q D hc hp hq hD
  have hM0 : ∀ n, 0 ≤ M n := fun n =>
    mul_nonneg (featureWeight_nonneg c C g p q hC n) (by positivity)
  apply norm_hilbertOperator_le_of_weighted_coordinate_bounds _
    (fun n => fderiv ℝ (φ n) x - fderiv ℝ (φ n) y)
    (sourceFeatureScale c p) (fun n => M n * ‖x - y‖) _
    (fun n => (sourceFeatureScale_pos c p n).le)
    (mul_nonneg (tsum_nonneg hM0) (norm_nonneg _))
    (hM.hasSum.mul_right ‖x - y‖)
  · intro v n
    change (fderiv ℝ (sourceWeightedFeatureMap c p φ) x v) n -
        (fderiv ℝ (sourceWeightedFeatureMap c p φ) y v) n = _
    rw [fderiv_sourceWeightedFeatureMap_coordinate c C g p q φ hc hC hp hq hφ hgrowth,
      fderiv_sourceWeightedFeatureMap_coordinate c C g p q φ hc hC hp hq hφ hgrowth]
    simp only [sub_apply, smul_sub]
  · intro n
    exact sourceFeatureScale_mul_norm_fderiv_sub_le c C g p q D φ hC hD hφ
      (fun i z => hgrowth i z 2 le_rfl) x y hx hy n

/-- The actual source second derivative is locally Lipschitz from existence
and growth of the coordinate third derivatives, without D3 continuity. -/
theorem norm_second_fderiv_sourceWeightedFeatureMap_sub_le
    (hthird : ∀ n z, DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ (φ n))) z)
    (hgrowth₃ : ∀ n z, ‖iteratedFDeriv ℝ 3 (φ n) z‖ ≤
      featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1 - 3)))
    (D : ℝ) (hD : 1 ≤ D) (x y : E) (hx : ‖x‖ ≤ D) (hy : ‖y‖ ≤ D) :
    ‖fderiv ℝ (fderiv ℝ (sourceWeightedFeatureMap c p φ)) x -
      fderiv ℝ (fderiv ℝ (sourceWeightedFeatureMap c p φ)) y‖ ≤
      (∑' n, featureWeight c C g p q n * (1 + D ^ (n + 1))) * ‖x - y‖ := by
  let M := fun n => featureWeight c C g p q n * (1 + D ^ (n + 1))
  have hM := summable_feature_regularity_envelope c C g p q D hc hp hq hD
  have hM0 : ∀ n, 0 ≤ M n := fun n =>
    mul_nonneg (featureWeight_nonneg c C g p q hC n) (by positivity)
  apply norm_hilbertBilinear_le_of_weighted_coordinate_bounds _
    (fun n => fderiv ℝ (fderiv ℝ (φ n)) x - fderiv ℝ (fderiv ℝ (φ n)) y)
    (sourceFeatureScale c p) (fun n => M n * ‖x - y‖) _
    (fun n => (sourceFeatureScale_pos c p n).le)
    (mul_nonneg (tsum_nonneg hM0) (norm_nonneg _))
    (hM.hasSum.mul_right ‖x - y‖)
  · intro u v n
    change (fderiv ℝ (fderiv ℝ (sourceWeightedFeatureMap c p φ)) x u v) n -
        (fderiv ℝ (fderiv ℝ (sourceWeightedFeatureMap c p φ)) y u v) n = _
    rw [second_fderiv_sourceWeightedFeatureMap_coordinate c C g p q φ hc hC hp hq hφ hgrowth,
      second_fderiv_sourceWeightedFeatureMap_coordinate c C g p q φ hc hC hp hq hφ hgrowth]
    simp only [sub_apply, smul_sub]
  · intro n
    exact sourceFeatureScale_mul_norm_second_fderiv_sub_le c C g p q D φ hC hD hthird
      hgrowth₃ x y hx hy n

end Source

end PaperFormalization.Manuscript
