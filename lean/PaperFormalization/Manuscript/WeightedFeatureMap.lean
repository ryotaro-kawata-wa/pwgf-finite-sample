import PaperFormalization.Manuscript.WeightedHilbert
import PaperFormalization.Manuscript.FeatureRegularityBounds
import PaperFormalization.Continuous.SeriesDerivatives
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import PaperFormalization.Manuscript.MomentGradientField

/-! # The actual source weighted feature map is C2

Coordinates are represented in the complete Hilbert sum by a_m times their
source values. The source coordinate C2 and growth bounds through order two
imply convergence and C2 of this actual series. No smoothness of its sum or
continuity of the third coordinate derivative is assumed.
-/

open Set
open scoped BigOperators ContDiff

namespace PaperFormalization.Manuscript

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

/-- The source weight a_m at m=n+1. -/
noncomputable def sourceFeatureScale (c p : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-c * ((n + 1 : ℕ) : ℝ) ^ p)

/-- The actual weighted feature map, represented by its scaled coordinates. -/
noncomputable def sourceWeightedFeatureMap (c p : ℝ) (φ : ∀ n, E → H n) (x : E) : lp H 2 :=
  weightedHilbertSum (sourceFeatureScale c p) (fun n => φ n x)

/-- Source weights are strictly positive, hence coordinates can be decoded. -/
theorem sourceFeatureScale_pos (c p : ℝ) (n : ℕ) : 0 < sourceFeatureScale c p n :=
  Real.exp_pos _

omit [NormedSpace ℝ E] [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)] in
/-- The source coordinate bounds imply actual weighted absolute convergence. -/
theorem summable_sourceWeightedFeatureMap (c C g p q : ℝ) (φ : ∀ n, E → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hgrowth : ∀ n x, ‖φ n x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1)))
    (x : E) : Summable (fun n => sourceFeatureScale c p n * ‖φ n x‖) := by
  let D := 1 + ‖x‖
  have hD : 1 ≤ D := by dsimp [D]; linarith [norm_nonneg x]
  apply (summable_feature_regularity_envelope c C g p q D hc hp hq hD).of_nonneg_of_le
  · intro n
    exact mul_nonneg (sourceFeatureScale_pos c p n).le (norm_nonneg _)
  · intro n
    exact feature_weighted_norm_le_local_envelope (φ n) c C g p q D n 0 hC hD
      (by simpa only [Nat.sub_zero] using hgrowth n) x (by dsimp [D]; linarith)

omit [NormedSpace ℝ E] in
/-- The represented coordinates are exactly the source weighted features. -/
theorem sourceWeightedFeatureMap_apply (c C g p q : ℝ) (φ : ∀ n, E → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hgrowth : ∀ n x, ‖φ n x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1)))
    (x : E) (n : ℕ) :
    sourceWeightedFeatureMap c p φ x n = sourceFeatureScale c p n • φ n x := by
  exact weightedHilbertSum_apply _ (fun n => (sourceFeatureScale_pos c p n).le) _
    (summable_sourceWeightedFeatureMap c C g p q φ hc hC hp hq hgrowth x) n

omit [∀ n, CompleteSpace (H n)] in
/-- Every embedded source derivative through order two has the same summable
local majorant; the operator norm of insertion introduces exactly a_m. -/
theorem norm_sourceFeatureTerm_iterated_le (c C g p q D : ℝ) (φ : ∀ n, E → H n)
    (hC : 0 ≤ C) (hD : 1 ≤ D) (hφ : ∀ n, ContDiff ℝ 2 (φ n))
    (hgrowth : ∀ n x k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) x‖ ≤
      featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1 - k)))
    (n k : ℕ) (hk : k ≤ 2) (x : E) (hx : ‖x‖ ≤ D) :
    ‖iteratedFDeriv ℝ k
      (fun y => weightedCoordinateEmbedding (sourceFeatureScale c p) n (φ n y)) x‖ ≤
      featureWeight c C g p q n * (1 + D ^ (n + 1)) := by
  have hcomp := (weightedCoordinateEmbedding (sourceFeatureScale c p) n).norm_iteratedFDeriv_comp_left (x := x)
    (hφ n).contDiffAt (show (k : ℕ∞ω) ≤ 2 by exact_mod_cast hk)
  apply hcomp.trans
  calc
    ‖weightedCoordinateEmbedding (sourceFeatureScale c p) n‖ * ‖iteratedFDeriv ℝ k (φ n) x‖ ≤
        sourceFeatureScale c p n * ‖iteratedFDeriv ℝ k (φ n) x‖ :=
      mul_le_mul_of_nonneg_right
        (norm_weightedCoordinateEmbedding_le _ n (sourceFeatureScale_pos c p n).le) (norm_nonneg _)
    _ ≤ _ := feature_weighted_norm_le_local_envelope
      (fun y => iteratedFDeriv ℝ k (φ n) y) c C g p q D n k hC hD
      (fun y => hgrowth n y k hk) x hx

/-- Local C2 of the actual source series, derived on a ball from the coordinate
C2 assumptions and the original growth/decay parameters. -/
theorem contDiffAt_sourceWeightedFeatureMap (c C g p q : ℝ) (φ : ∀ n, E → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hφ : ∀ n, ContDiff ℝ 2 (φ n))
    (hgrowth : ∀ n x k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) x‖ ≤
      featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1 - k)))
    (x : E) : ContDiffAt ℝ 2 (sourceWeightedFeatureMap c p φ) x := by
  let D := 1 + ‖x‖
  let M := fun n => featureWeight c C g p q n * (1 + D ^ (n + 1))
  let f := fun n y => weightedCoordinateEmbedding (sourceFeatureScale c p) n (φ n y)
  have hD : 1 ≤ D := by dsimp [D]; linarith [norm_nonneg x]
  have hM : Summable M := summable_feature_regularity_envelope c C g p q D hc hp hq hD
  have hbound : ∀ n y, y ∈ Metric.ball (0 : E) D → ∀ k, k ≤ 2 →
      ‖iteratedFDeriv ℝ k (f n) y‖ ≤ M n := by
    intro n y hy k hk
    exact norm_sourceFeatureTerm_iterated_le c C g p q D φ hC hD hφ hgrowth n k hk y
      (by
        have hy' : ‖y‖ < D := by simpa only [Metric.mem_ball, dist_zero_right] using hy
        exact hy'.le)
  change ContDiffAt ℝ 2 (fun y => ∑' n, f n y) x
  apply Continuous.contDiffAt_two_tsum_fderivBounds_on_open f M M M
    (Metric.ball (0 : E) D) Metric.isOpen_ball hM hM hM
  · intro n y _
    exact (weightedCoordinateEmbedding (sourceFeatureScale c p) n).contDiff.contDiffAt.comp y
      (hφ n).contDiffAt
  · intro n y hy
    simpa only [norm_iteratedFDeriv_zero] using hbound n y hy 0 (by omega)
  · intro n y hy
    simpa only [norm_iteratedFDeriv_one] using hbound n y hy 1 (by omega)
  · intro n y hy
    rw [norm_second_fderiv_eq_iterated]
    exact hbound n y hy 2 le_rfl
  · simpa only [Metric.mem_ball, dist_zero_right, D] using
      (show ‖x‖ < 1 + ‖x‖ by linarith)

/-- The source weighted feature map is C2 on the whole particle space. -/
theorem contDiff_sourceWeightedFeatureMap (c C g p q : ℝ) (φ : ∀ n, E → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hφ : ∀ n, ContDiff ℝ 2 (φ n))
    (hgrowth : ∀ n x k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) x‖ ≤
      featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1 - k))) :
    ContDiff ℝ 2 (sourceWeightedFeatureMap c p φ) :=
  contDiff_iff_contDiffAt.mpr (contDiffAt_sourceWeightedFeatureMap c C g p q φ hc hC hp hq hφ hgrowth)

/-- The source C2 feature conclusion discharges the empirical-field derivative
premise. Only actual reachable-moment membership in the original open G-domain
remains explicit; no global smoothness of G or convexity of U is introduced. -/
theorem hasFDerivAt_sourceEmpiricalMomentGradientField
    {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P] {ι : Type*} [Fintype ι]
    (c C g p q : ℝ) (φ : ∀ n, P → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hφ : ∀ n, ContDiff ℝ 2 (φ n))
    (hgrowth : ∀ n x k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) x‖ ≤
      featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1 - k)))
    (G : lp H 2 → ℝ) (U : Set (lp H 2)) (hU : IsOpen U)
    (hG : ContDiffOn ℝ 3 G U) (X : PiLp 2 fun _ : ι => P)
    (hX : empiricalMomentMap (sourceWeightedFeatureMap c p φ) X ∈ U) :
    let J := sourceWeightedFeatureMap c p φ
    HasFDerivAt (empiricalConfigurationField J (momentGradientField (fderiv ℝ J) (gradient G)))
      (-Continuous.sampledBlockOperator
        (fun i => momentSpatialHessian (fderiv ℝ (fderiv ℝ J) (X i))
          (gradient G (empiricalMomentMap J X)))
        (fun i j => momentIntegralHessian (fderiv ℝ J (X i)) (fderiv ℝ J (X j))
          (momentObjectiveHessian G (empiricalMomentMap J X)))) X := by
  apply hasFDerivAt_actualEmpiricalMomentGradientField
  · intro i
    exact contDiffAt_sourceWeightedFeatureMap c C g p q φ hc hC hp hq hφ hgrowth (X i)
  · exact (hG.contDiffAt (hU.mem_nhds hX)).of_le (by norm_num)

end PaperFormalization.Manuscript
