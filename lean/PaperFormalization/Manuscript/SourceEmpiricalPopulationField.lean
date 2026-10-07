import PaperFormalization.Manuscript.MeasureRegionObjective
import PaperFormalization.Manuscript.SourceFeatureRadius
import PaperFormalization.Manuscript.EmpiricalPopulationResidual

/-! # Concrete source field and Hessian comparison against actual population moments

The particle moment is the actual finite empirical mean of J0. The population
moment is the genuine Bochner integral under a member of the supplied class P.
The original open domain U contains the exact measure-generated finite convex
hull; it is neither enlarged nor assumed convex. Source coordinate hypotheses
and local C3 of G derive the field and both Hessian estimates with the literal
residual Gamma. No model derivative bound or residual convergence is assumed.
-/

open MeasureTheory Set
open scoped NNReal

set_option maxSynthPendingDepth 8

namespace PaperFormalization.Manuscript

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The actual signed field difference is at most Gamma; the spatial and
integral Hessian differences are each at most Gamma/2. All norms, moment
membership, convergence, and derivative estimates are derived from the source
hypotheses and the literal L=4QR³. P is retained exactly as supplied. -/
theorem source_empirical_population_field_bounds_by_residual
    (c C g p q K D alpha C3 : ℝ) (φ : ∀ n, E → H n) (P : Set (Measure E))
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (hD : 1 ≤ D)
    (hφ : ∀ n, ContDiff ℝ 2 (φ n))
    (hgrowth : ∀ n z k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) z‖ ≤
      featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1 - k)))
    (hPprob : ∀ μ ∈ P, IsProbabilityMeasure μ)
    (hPmoment : ∀ μ ∈ P, ∀ n, Integrable (fun z : E => ‖z‖ ^ (n + 1)) μ)
    (hPmean : ∀ μ ∈ P, ∀ n, (∫ z : E, ‖z‖ ^ (n + 1) ∂μ) ≤
      K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha))
    (G : lp H 2 → ℝ) (U : Set (lp H 2)) (hU : IsOpen U)
    (hSU : measureMomentRegion (sourceWeightedFeatureMap c p φ) P D ⊆ U)
    (hG : ContDiffOn ℝ 3 G U)
    (hthird : ∀ theta ∈ measureMomentRegion (sourceWeightedFeatureMap c p φ) P D,
      ‖iteratedFDeriv ℝ 3 G theta‖ ≤ C3)
    (L : ℝ≥0) (hL : (L : ℝ) = sourceComparisonEnvelope c C g p q K D alpha C3 φ G)
    (μ : Measure E) (hμ : μ ∈ P) (X : PiLp 2 fun _ : ι => E)
    (hX : ∀ i, ‖X i‖ ≤ D) (x y : E) (hx : ‖x‖ ≤ D) (hy : ‖y‖ ≤ D) (t : ℝ) :
    let J := sourceWeightedFeatureMap c p φ
    let theta := empiricalMomentMap J X
    let theta' := ∫ z, J z ∂μ
    ‖momentGradientField (fderiv ℝ J) (gradient G) (theta, x) -
      momentGradientField (fderiv ℝ J) (gradient G) (theta', x)‖ ≤
        momentResidual (featureResidualWeight c p L)
          (fun n _ => finiteFeatureMean (fun i => φ n (X i)))
          (fun n _ => ∫ z, φ n z ∂μ) t ∧
    ‖momentSpatialHessian (fderiv ℝ (fderiv ℝ J) x) (gradient G theta) -
      momentSpatialHessian (fderiv ℝ (fderiv ℝ J) x) (gradient G theta')‖ ≤
        momentResidual (featureResidualWeight c p L)
          (fun n _ => finiteFeatureMean (fun i => φ n (X i)))
          (fun n _ => ∫ z, φ n z ∂μ) t / 2 ∧
    ‖momentIntegralHessian (fderiv ℝ J x) (fderiv ℝ J y) (momentObjectiveHessian G theta) -
      momentIntegralHessian (fderiv ℝ J x) (fderiv ℝ J y) (momentObjectiveHessian G theta')‖ ≤
        momentResidual (featureResidualWeight c p L)
          (fun n _ => finiteFeatureMean (fun i => φ n (X i)))
          (fun n _ => ∫ z, φ n z ∂μ) t / 2 := by
  dsimp only
  letI : IsProbabilityMeasure μ := hPprob μ hμ
  have hcont : ∀ n, Continuous (φ n) := fun n => (hφ n).continuous
  have hvalue : ∀ n z, ‖φ n z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1)) := by
    intro n z
    simpa only [norm_iteratedFDeriv_zero, Nat.sub_zero] using hgrowth n z 0 (by omega)
  let J := sourceWeightedFeatureMap c p φ
  let theta := empiricalMomentMap J X
  let theta' := ∫ z, J z ∂μ
  have htheta : theta ∈ measureMomentRegion J P D :=
    empiricalMomentMap_mem_measureMomentRegion J P D X hX
  have htheta' : theta' ∈ measureMomentRegion J P D :=
    population_integral_mem_measureMomentRegion J P D μ hμ
  have hb := source_measure_region_objective_bounds c C g p q K D alpha C3 φ P
    hc hC hp hq hK hD hcont hPprob hPmoment hPmean hvalue G U hU hSU hG hthird
  have hd := source_measure_region_objective_differences c C g p q K D alpha C3 φ P
    hc hC hp hq hK hD hcont hPprob hPmoment hPmean hvalue G U hU hSU hG hthird
    theta theta' htheta htheta'
  have hfx := source_feature_norms_le_radius c C g p q K D alpha φ
    hc hC hp hq hK hD hφ hgrowth x hx
  have hfy := source_feature_norms_le_radius c C g p q K D alpha φ
    hc hC hp hq hK hD hφ hgrowth y hy
  exact source_moment_measure_bounds_by_residual c p L
    (fun n _ => finiteFeatureMean (fun i => φ n (X i)))
    (fun n _ => ∫ z, φ n z ∂μ) t theta theta'
    (empirical_sourceWeightedFeatureMap_apply c C g p q φ hc hC hp hq hvalue X)
    (source_population_moment_apply μ id c C g p q K alpha φ hc hC hp hq hK
      aestronglyMeasurable_id hcont (hPmoment μ hμ) (hPmean μ hμ) hvalue)
    (summable_empirical_population_momentResidual μ id c C g p q K D alpha L φ
      hc hC hp hq hK hD (hPmoment μ hμ) (hPmean μ hμ) hvalue X hX t)
    (fderiv ℝ J) (gradient G) x y (fderiv ℝ (fderiv ℝ J) x)
    (momentObjectiveHessian G theta) (momentObjectiveHessian G theta')
    (sourceObjectiveAnchorFactor c p C3 φ G) (sourceMomentRadius c C g p q K D alpha)
    hb.1 (one_le_sourceMomentRadius c C g p q K D alpha hC hK.le (by linarith))
    hL hfx.2.1 hfy.2.1 hfx.2.2 hd.1 hd.2

end PaperFormalization.Manuscript
