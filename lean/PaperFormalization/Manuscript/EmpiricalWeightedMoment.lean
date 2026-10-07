import PaperFormalization.Manuscript.WeightedFeatureMap
import PaperFormalization.Manuscript.CoordinateMoments

/-! # Finite empirical moments of the actual weighted feature map

Averaging the represented feature map has exactly the represented coordinate
empirical means. Decoding recovers the original source means, and the squared
norm of an empirical difference is the exact weighted coordinate squared norm.
Only source value growth and weight decay are needed: no differentiability,
probability law, or conditional-law identification is assumed.
-/

open scoped BigOperators

namespace PaperFormalization.Manuscript

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

/-- Averaging the actual weighted feature map gives exactly a_m times the
source coordinate empirical mean, retaining the reciprocal particle count. -/
theorem empirical_sourceWeightedFeatureMap_apply
    (c C g p q : ℝ) (φ : ∀ n, E → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hgrowth : ∀ n x, ‖φ n x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1)))
    (X : PiLp 2 fun _ : ι => E) (n : ℕ) :
    empiricalMomentMap (sourceWeightedFeatureMap c p φ) X n =
      sourceFeatureScale c p n • finiteFeatureMean (fun i => φ n (X i)) := by
  classical
  change (lp.evalCLM ℝ H 2 n)
    ((Fintype.card ι : ℝ)⁻¹ • ∑ i, sourceWeightedFeatureMap c p φ (X i)) = _
  rw [map_smul, map_sum]
  change (Fintype.card ι : ℝ)⁻¹ • ∑ i, sourceWeightedFeatureMap c p φ (X i) n = _
  simp only [sourceWeightedFeatureMap_apply c C g p q φ hc hC hp hq hgrowth]
  rw [← Finset.smul_sum]
  exact smul_comm _ _ _

/-- Decoding the represented empirical moment recovers the actual unweighted
coordinate mean in its source Hilbert space. -/
theorem weightedCoordinateProjection_empirical_sourceWeightedFeatureMap
    (c C g p q : ℝ) (φ : ∀ n, E → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hgrowth : ∀ n x, ‖φ n x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1)))
    (X : PiLp 2 fun _ : ι => E) (n : ℕ) :
    weightedCoordinateProjection (sourceFeatureScale c p) n
      (empiricalMomentMap (sourceWeightedFeatureMap c p φ) X) =
      finiteFeatureMean (fun i => φ n (X i)) := by
  rw [weightedCoordinateProjection_apply,
    empirical_sourceWeightedFeatureMap_apply c C g p q φ hc hC hp hq hgrowth X n]
  simp [smul_smul, (sourceFeatureScale_pos c p n).ne']

/-- Empirical differences preserve the coordinate order and carry one source
weight, before the Hilbert norm squares that weight. -/
theorem empirical_sourceWeightedFeatureMap_sub_apply
    (c C g p q : ℝ) (φ : ∀ n, E → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hgrowth : ∀ n x, ‖φ n x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1)))
    (X Y : PiLp 2 fun _ : ι => E) (n : ℕ) :
    (empiricalMomentMap (sourceWeightedFeatureMap c p φ) X -
      empiricalMomentMap (sourceWeightedFeatureMap c p φ) Y) n =
      sourceFeatureScale c p n •
        (finiteFeatureMean (fun i => φ n (X i)) - finiteFeatureMean (fun i => φ n (Y i))) := by
  change empiricalMomentMap (sourceWeightedFeatureMap c p φ) X n -
    empiricalMomentMap (sourceWeightedFeatureMap c p φ) Y n = _
  rw [empirical_sourceWeightedFeatureMap_apply c C g p q φ hc hC hp hq hgrowth X n,
    empirical_sourceWeightedFeatureMap_apply c C g p q φ hc hC hp hq hgrowth Y n,
    smul_sub]

/-- Exact source weighted squared norm for the difference of two actual
empirical moment vectors; no abstract moment-vector equality is assumed. -/
theorem norm_empirical_sourceWeightedFeatureMap_sub_sq
    (c C g p q : ℝ) (φ : ∀ n, E → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hgrowth : ∀ n x, ‖φ n x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1)))
    (X Y : PiLp 2 fun _ : ι => E) :
    ‖empiricalMomentMap (sourceWeightedFeatureMap c p φ) X -
      empiricalMomentMap (sourceWeightedFeatureMap c p φ) Y‖ ^ 2 =
      ∑' n, (sourceFeatureScale c p n) ^ 2 *
        ‖finiteFeatureMean (fun i => φ n (X i)) - finiteFeatureMean (fun i => φ n (Y i))‖ ^ 2 := by
  rw [hilbertSum_norm_sq]
  congr 1
  funext n
  rw [empirical_sourceWeightedFeatureMap_sub_apply c C g p q φ hc hC hp hq hgrowth X Y n,
    norm_smul, mul_pow]
  simp

end PaperFormalization.Manuscript
