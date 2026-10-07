import PaperFormalization.Manuscript.HilbertMomentResidual
import PaperFormalization.Manuscript.EmpiricalWeightedMoment
import PaperFormalization.Manuscript.WeightedBochnerMoment

/-! # The literal residual for actual empirical and fixed-law population moments

The empirical coordinates are the finite source means. The population
coordinates are Bochner integrals under one fixed supplied probability law.
Coordinate amplitudes prove convergence of the original residual series, and
coordinate recovery identifies the actual Hilbert moment difference. The
local factor L may be zero. No conditional-law identification is asserted.
-/

open MeasureTheory Set
open scoped NNReal

namespace PaperFormalization.Manuscript

variable {Ω ι E : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

/-- Source empirical and population amplitude bounds prove convergence of
exactly the literal weighted residual of their coordinate moments. -/
theorem summable_empirical_population_momentResidual
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → E)
    (c C g p q K D alpha : ℝ) (L : ℝ≥0) (φ : ∀ n, E → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hK : 0 < K) (hD : 1 ≤ D)
    (hmoment : ∀ n, Integrable (fun ω => ‖Y ω‖ ^ (n + 1)) μ)
    (hmean : ∀ n, (∫ ω, ‖Y ω‖ ^ (n + 1) ∂μ) ≤
      K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha))
    (hgrowth : ∀ n x, ‖φ n x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1)))
    (X : PiLp 2 fun _ : ι => E) (hX : ∀ i, ‖X i‖ ≤ D) (t : ℝ) :
    Summable (fun n => momentResidualTerm (featureResidualWeight c p L)
      (fun n _ => finiteFeatureMean (fun i => φ n (X i)))
      (fun n _ => ∫ ω, φ n (Y ω) ∂μ) n t) := by
  apply featureResidual_summable
    (fun n _ => finiteFeatureMean (fun i => φ n (X i)))
    (fun n _ => ∫ ω, φ n (Y ω) ∂μ)
    c C g p q K D alpha L univ hc hp hq hK (by linarith) ?_ ?_ t (mem_univ _)
  · intro n _ _
    exact norm_empirical_feature_mean_le (fun i => X i) (φ n) (n + 1)
      (featureGrowth C g q n) D (featureGrowth_nonneg C g q hC n) hX (hgrowth n)
  · intro n _ _
    exact norm_coordinate_feature_integral_le μ Y (φ n) (n + 1)
      (featureGrowth C g q n)
      (K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha))
      (featureGrowth_nonneg C g q hC n) (hmoment n) (hmean n) (hgrowth n)

omit [Fintype ι] [Nonempty ι] in
/-- Each coordinate of the genuine Hilbert-valued population integral is
exactly its original feature expectation multiplied by the source weight. -/
theorem source_population_moment_apply
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → E)
    (c C g p q K alpha : ℝ) (φ : ∀ n, E → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K)
    (hY : AEStronglyMeasurable Y μ) (hφ : ∀ n, Continuous (φ n))
    (hmoment : ∀ n, Integrable (fun ω => ‖Y ω‖ ^ (n + 1)) μ)
    (hmean : ∀ n, (∫ ω, ‖Y ω‖ ^ (n + 1) ∂μ) ≤
      K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha))
    (hgrowth : ∀ n x, ‖φ n x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1)))
    (n : ℕ) :
    (∫ ω, sourceWeightedFeatureMap c p φ (Y ω) ∂μ) n =
      sourceFeatureScale c p n • (∫ ω, φ n (Y ω) ∂μ) := by
  have hd := decoded_sourceWeightedMoment_of_moments μ Y c C g p q K alpha φ
    hc hC hp hq hK hY hφ hmoment hmean hgrowth n
  calc
    _ = sourceFeatureScale c p n • weightedCoordinateProjection (sourceFeatureScale c p) n
        (∫ ω, sourceWeightedFeatureMap c p φ (Y ω) ∂μ) :=
      (smul_weightedCoordinateProjection (sourceFeatureScale c p) n
        (sourceFeatureScale_pos c p n).ne' _).symm
    _ = _ := congrArg (fun v => sourceFeatureScale c p n • v) hd

/-- The actual encoded empirical moment minus the actual fixed-law population
Bochner moment is controlled by the original literal Gamma. Convergence is
derived from source amplitudes; L is never divided out. -/
theorem scaled_empirical_population_moment_difference_le_residual
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → E)
    (c C g p q K D alpha : ℝ) (L : ℝ≥0) (φ : ∀ n, E → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hK : 0 < K) (hD : 1 ≤ D)
    (hY : AEStronglyMeasurable Y μ) (hφ : ∀ n, Continuous (φ n))
    (hmoment : ∀ n, Integrable (fun ω => ‖Y ω‖ ^ (n + 1)) μ)
    (hmean : ∀ n, (∫ ω, ‖Y ω‖ ^ (n + 1) ∂μ) ≤
      K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha))
    (hgrowth : ∀ n x, ‖φ n x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1)))
    (X : PiLp 2 fun _ : ι => E) (hX : ∀ i, ‖X i‖ ≤ D) (t : ℝ) :
    (L : ℝ) * ‖empiricalMomentMap (sourceWeightedFeatureMap c p φ) X -
      ∫ ω, sourceWeightedFeatureMap c p φ (Y ω) ∂μ‖ ≤
      momentResidual (featureResidualWeight c p L)
        (fun n _ => finiteFeatureMean (fun i => φ n (X i)))
        (fun n _ => ∫ ω, φ n (Y ω) ∂μ) t := by
  apply scaled_moment_difference_le_residual c p L
    (fun n _ => finiteFeatureMean (fun i => φ n (X i)))
    (fun n _ => ∫ ω, φ n (Y ω) ∂μ) t
    (empiricalMomentMap (sourceWeightedFeatureMap c p φ) X)
    (∫ ω, sourceWeightedFeatureMap c p φ (Y ω) ∂μ)
  · exact empirical_sourceWeightedFeatureMap_apply c C g p q φ hc hC hp hq hgrowth X
  · exact source_population_moment_apply μ Y c C g p q K alpha φ
      hc hC hp hq hK hY hφ hmoment hmean hgrowth
  · exact summable_empirical_population_momentResidual μ Y c C g p q K D alpha L φ
      hc hC hp hq hK hD hmoment hmean hgrowth X hX t

end PaperFormalization.Manuscript
