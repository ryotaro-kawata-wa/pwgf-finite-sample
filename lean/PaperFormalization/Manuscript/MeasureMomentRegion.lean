import PaperFormalization.Manuscript.MomentRegionGeometry
import PaperFormalization.Manuscript.EmpiricalMeasureMoment
import PaperFormalization.Manuscript.WeightedBochnerMoment
import PaperFormalization.Manuscript.CoordinateMoments
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # A feasible moment region built from actual probability measures

The population class P is supplied unchanged. It is never replaced by the
larger class of measures satisfying only integer-moment inequalities. The
other source class consists of probability measures with full mass in the
closed D-ball. The region is the finite convex hull of actual Bochner moments.
Integrability is proved separately from any bound on a totalized integral.
-/

open MeasureTheory Set Filter
open scoped BigOperators

namespace PaperFormalization.Manuscript

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]

/-- The source bounded-support probability class. -/
def boundedSupportProbabilityClass (D : ℝ) : Set (Measure E) :=
  {μ | IsProbabilityMeasure μ ∧ μ (Metric.closedBall (0 : E) D) = 1}

/-- The exact finite convex hull of moments of the supplied population class
and the bounded-support probability class. No closure is added. -/
noncomputable def measureMomentRegion
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (J : E → F) (P : Set (Measure E)) (D : ℝ) : Set F :=
  convexHull ℝ ((fun μ : Measure E => ∫ x, J x ∂μ) '' (P ∪ boundedSupportProbabilityClass D))

/-- Full mass in the measurable closed ball gives the actual AE support bound. -/
theorem ae_norm_le_of_closedBall_mass_one [BorelSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (D : ℝ)
    (hsupport : μ (Metric.closedBall (0 : E) D) = 1) :
    ∀ᵐ x ∂μ, ‖x‖ ≤ D := by
  have hs : ∀ᵐ x ∂μ, x ∈ Metric.closedBall (0 : E) D :=
    (mem_ae_iff_prob_eq_one Metric.isClosed_closedBall.measurableSet).2 hsupport
  simpa only [Metric.mem_closedBall, dist_zero_right] using hs

/-- Every integer norm power is genuinely integrable under a bounded-support
probability measure, before any moment integral bound is used. -/
theorem integrable_norm_pow_of_closedBall_mass_one [BorelSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (D : ℝ)
    (hsupport : μ (Metric.closedBall (0 : E) D) = 1) (m : ℕ) :
    Integrable (fun x : E => ‖x‖ ^ m) μ := by
  apply (integrable_const (D ^ m)).mono' (continuous_norm.pow m).aestronglyMeasurable
  filter_upwards [ae_norm_le_of_closedBall_mass_one μ D hsupport] with x hx
  simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg x) m)] using
    pow_le_pow_left₀ (norm_nonneg x) hx m

/-- The bounded-support moment has its exact D^m upper bound. -/
theorem integral_norm_pow_le_of_closedBall_mass_one [BorelSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (D : ℝ)
    (hsupport : μ (Metric.closedBall (0 : E) D) = 1) (m : ℕ) :
    (∫ x : E, ‖x‖ ^ m ∂μ) ≤ D ^ m := by
  have h := integral_mono_ae (integrable_norm_pow_of_closedBall_mass_one μ D hsupport m)
    (integrable_const (D ^ m)) (by
      filter_upwards [ae_norm_le_of_closedBall_mass_one μ D hsupport] with x hx
      exact pow_le_pow_left₀ (norm_nonneg x) hx m)
  simpa only [integral_const, probReal_univ, one_smul] using h

/-- Continuous coordinate features of the source growth are Bochner
integrable on bounded support, without target separability assumptions. -/
theorem coordinate_feature_integrable_of_closedBall_mass_one
    [BorelSpace E] [SecondCountableTopology E]
    {F : Type*} [NormedAddCommGroup F]
    (μ : Measure E) [IsProbabilityMeasure μ] (φ : E → F) (m : ℕ) (L D : ℝ)
    (hφ : Continuous φ) (hsupport : μ (Metric.closedBall (0 : E) D) = 1)
    (hgrowth : ∀ x, ‖φ x‖ ≤ L * (1 + ‖x‖ ^ m)) : Integrable φ μ := by
  exact coordinate_feature_integrable μ id φ m L aestronglyMeasurable_id hφ
    (integrable_norm_pow_of_closedBall_mass_one μ D hsupport m) hgrowth

/-- The actual bounded-support coordinate moment obeys the source amplitude. -/
theorem norm_coordinate_integral_le_of_closedBall_mass_one
    [BorelSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E) [IsProbabilityMeasure μ] (φ : E → F) (m : ℕ) (L D : ℝ)
    (hL : 0 ≤ L) (hsupport : μ (Metric.closedBall (0 : E) D) = 1)
    (hgrowth : ∀ x, ‖φ x‖ ≤ L * (1 + ‖x‖ ^ m)) :
    ‖∫ x, φ x ∂μ‖ ≤ L * (1 + D ^ m) :=
  norm_coordinate_feature_integral_le μ id φ m L (D ^ m) hL
    (integrable_norm_pow_of_closedBall_mass_one μ D hsupport m)
    (integral_norm_pow_le_of_closedBall_mass_one μ D hsupport m) hgrowth

section Membership

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual moment region is convex by construction. -/
theorem convex_measureMomentRegion (J : E → F) (P : Set (Measure E)) (D : ℝ) :
    Convex ℝ (measureMomentRegion J P D) := convex_convexHull _ _

/-- A supplied population member contributes its own actual Bochner moment. -/
theorem population_integral_mem_measureMomentRegion
    (J : E → F) (P : Set (Measure E)) (D : ℝ) (μ : Measure E) (hμ : μ ∈ P) :
    (∫ x, J x ∂μ) ∈ measureMomentRegion J P D :=
  subset_convexHull ℝ _ ⟨μ, Or.inl hμ, rfl⟩

/-- A bounded-support probability measure contributes its actual moment. -/
theorem supported_integral_mem_measureMomentRegion
    (J : E → F) (P : Set (Measure E)) (D : ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (hsupport : μ (Metric.closedBall (0 : E) D) = 1) :
    (∫ x, J x ∂μ) ∈ measureMomentRegion J P D :=
  subset_convexHull ℝ _ ⟨μ, Or.inr ⟨inferInstance, hsupport⟩, rfl⟩

/-- The original Dirac anchor is an actual member, with moment exactly J(0). -/
theorem zero_anchor_mem_measureMomentRegion [MeasurableSingletonClass E] [CompleteSpace F]
    (J : E → F) (P : Set (Measure E)) (D : ℝ) (hD : 0 ≤ D) :
    J 0 ∈ measureMomentRegion J P D := by
  rw [← integral_dirac_zero_feature J]
  exact supported_integral_mem_measureMomentRegion J P D (Measure.dirac 0)
    (dirac_zero_closedBall D hD)

/-- A localized finite configuration's true empirical Bochner moment belongs
to the source region, with exact reciprocal-cardinality normalization. -/
theorem empirical_mean_mem_measureMomentRegion
    [MeasurableSingletonClass E] [CompleteSpace F]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (J : E → F) (P : Set (Measure E)) (D : ℝ) (X : ι → E)
    (hX : ∀ i, ‖X i‖ ≤ D) :
    finiteFeatureMean (fun i => J (X i)) ∈ measureMomentRegion J P D := by
  rw [← integral_finiteEmpiricalMeasure X J]
  exact supported_integral_mem_measureMomentRegion J P D (finiteEmpiricalMeasure X)
    (finiteEmpiricalMeasure_closedBall X D hX)

/-- Feasible moment segments stay in the exact finite-convex-hull region. -/
theorem affine_segment_mem_measureMomentRegion
    (J : E → F) (P : Set (Measure E)) (D : ℝ) (theta theta' : F)
    (htheta : theta ∈ measureMomentRegion J P D) (htheta' : theta' ∈ measureMomentRegion J P D)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    theta + s • (theta' - theta) ∈ measureMomentRegion J P D :=
  (convex_measureMomentRegion J P D).add_smul_sub_mem htheta htheta' hs

end Membership

/-- The existing configuration moment map is precisely the actual empirical
moment whose source-region membership has just been established. -/
theorem empiricalMomentMap_mem_measureMomentRegion
    [MeasurableSingletonClass E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (J : E → F) (P : Set (Measure E)) (D : ℝ) (X : PiLp 2 fun _ : ι => E)
    (hX : ∀ i, ‖X i‖ ≤ D) :
    empiricalMomentMap J X ∈ measureMomentRegion J P D := by
  simpa only [finiteFeatureMean, empiricalMomentMap] using
    empirical_mean_mem_measureMomentRegion J P D (fun i => X i) hX

section Source

variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

/-- Continuous coordinate evaluation of an actual Bochner integral gives the
literal scaled source-coordinate integral, under the same measure. -/
theorem sourceWeightedMoment_coordinate_of_integrable
    (μ : Measure E) (c C g p q : ℝ) (φ : ∀ n, E → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hgrowth : ∀ n x, ‖φ n x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1)))
    (hJ : Integrable (sourceWeightedFeatureMap c p φ) μ) (n : ℕ) :
    (∫ x, sourceWeightedFeatureMap c p φ x ∂μ) n =
      sourceFeatureScale c p n • ∫ x, φ n x ∂μ := by
  have heq := (lp.evalCLM ℝ H 2 n).integral_comp_comm hJ
  change (∫ x, sourceWeightedFeatureMap c p φ x n ∂μ) =
    (∫ x, sourceWeightedFeatureMap c p φ x ∂μ) n at heq
  rw [← heq]
  simp_rw [sourceWeightedFeatureMap_apply c C g p q φ hc hC hp hq hgrowth]
  exact integral_smul _ _

/-- Bounded support gives genuine Hilbert-valued Bochner integrability, the
exact source D-envelope, and encoded coordinate bounds under the same measure. -/
theorem source_supported_measure_moment_bounds
    [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure E) [IsProbabilityMeasure μ] (c C g p q D : ℝ) (φ : ∀ n, E → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hD : 1 ≤ D)
    (hφ : ∀ n, Continuous (φ n))
    (hsupport : μ (Metric.closedBall (0 : E) D) = 1)
    (hgrowth : ∀ n x, ‖φ n x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1))) :
    Integrable (sourceWeightedFeatureMap c p φ) μ ∧
    ‖∫ x, sourceWeightedFeatureMap c p φ x ∂μ‖ ≤
        ∑' n, featureWeight c C g p q n * (1 + D ^ (n + 1)) ∧
    ∀ n, ‖(∫ x, sourceWeightedFeatureMap c p φ x ∂μ) n‖ ≤
      featureWeight c C g p q n * (1 + D ^ (n + 1)) := by
  have hf : ∀ n, Integrable (φ n) μ := fun n =>
    coordinate_feature_integrable_of_closedBall_mass_one μ (φ n) (n + 1)
      (featureGrowth C g q n) D (hφ n) hsupport (hgrowth n)
  have hbound : ∀ n, sourceFeatureScale c p n * (∫ x, ‖φ n x‖ ∂μ) ≤
      featureWeight c C g p q n * (1 + D ^ (n + 1)) := by
    intro n
    have hb := integral_norm_coordinate_feature_le μ id (φ n) (n + 1)
      (featureGrowth C g q n) (D ^ (n + 1)) (featureGrowth_nonneg C g q hC n) (hf n)
      (integrable_norm_pow_of_closedBall_mass_one μ D hsupport (n + 1))
      (integral_norm_pow_le_of_closedBall_mass_one μ D hsupport (n + 1)) (hgrowth n)
    have hw := mul_le_mul_of_nonneg_left hb (sourceFeatureScale_pos c p n).le
    simpa only [id_eq, sourceFeatureScale, featureWeight, featureGrowth, mul_assoc] using hw
  have hs : Summable (fun n => sourceFeatureScale c p n * ∫ x, ‖φ n x‖ ∂μ) :=
    Summable.of_nonneg_of_le
      (fun n => mul_nonneg (sourceFeatureScale_pos c p n).le (integral_nonneg (fun _ => norm_nonneg _)))
      hbound (summable_feature_regularity_envelope c C g p q D hc hp hq hD)
  have hJ : Integrable (sourceWeightedFeatureMap c p φ) μ :=
    integrable_weightedHilbertSum μ (sourceFeatureScale c p)
      (fun n => (sourceFeatureScale_pos c p n).le) φ hf hs
  refine ⟨hJ, ?_, ?_⟩
  · exact (norm_integral_weightedHilbertSum_le μ (sourceFeatureScale c p)
      (fun n => (sourceFeatureScale_pos c p n).le) φ hf hs).trans
      (Summable.tsum_le_tsum hbound hs
        (summable_feature_regularity_envelope c C g p q D hc hp hq hD))
  · intro n
    rw [sourceWeightedMoment_coordinate_of_integrable μ c C g p q φ hc hC hp hq hgrowth hJ,
      norm_smul, Real.norm_eq_abs, abs_of_pos (sourceFeatureScale_pos c p n)]
    exact (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm (φ n))
      (sourceFeatureScale_pos c p n).le).trans (hbound n)

/-- A member of the supplied population class has actual integrable Hilbert
moments and the literal encoded population coordinate envelope. Integer power
integrability is explicit; this theorem does not define or enlarge that class. -/
theorem source_population_measure_moment_bounds
    [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure E) [IsProbabilityMeasure μ] (c C g p q K alpha : ℝ) (φ : ∀ n, E → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K)
    (hφ : ∀ n, Continuous (φ n))
    (hmoment : ∀ n, Integrable (fun x : E => ‖x‖ ^ (n + 1)) μ)
    (hmean : ∀ n, (∫ x : E, ‖x‖ ^ (n + 1) ∂μ) ≤
      K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha))
    (hgrowth : ∀ n x, ‖φ n x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1))) :
    Integrable (sourceWeightedFeatureMap c p φ) μ ∧
    ∀ n, ‖(∫ x, sourceWeightedFeatureMap c p φ x ∂μ) n‖ ≤
      featureWeight c C g p q n *
        (1 + K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha)) := by
  have hJ := integrable_sourceWeightedFeatureMap_of_moments μ id c C g p q K alpha φ
    hc hC hp hq hK aestronglyMeasurable_id hφ hmoment hmean hgrowth
  refine ⟨hJ, ?_⟩
  intro n
  rw [sourceWeightedMoment_coordinate_of_integrable μ c C g p q φ hc hC hp hq hgrowth hJ,
    norm_smul, Real.norm_eq_abs, abs_of_pos (sourceFeatureScale_pos c p n)]
  have hb := norm_coordinate_feature_integral_le μ id (φ n) (n + 1)
    (featureGrowth C g q n)
    (K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha))
    (featureGrowth_nonneg C g q hC n) (hmoment n) (hmean n) (hgrowth n)
  have hw := mul_le_mul_of_nonneg_left hb (sourceFeatureScale_pos c p n).le
  simpa only [id_eq, sourceFeatureScale, featureWeight, featureGrowth, mul_assoc] using hw

/-- Reusable encoded coordinate bounds for every actual measure-generated
moment. The supplied population set is preserved exactly. -/
theorem source_measureMomentRegion_generator_coordinate_bounds
    [BorelSpace E] [SecondCountableTopology E]
    (c C g p q K D alpha : ℝ) (φ : ∀ n, E → H n) (P : Set (Measure E))
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (hD : 1 ≤ D)
    (hφ : ∀ n, Continuous (φ n))
    (hPprob : ∀ μ ∈ P, IsProbabilityMeasure μ)
    (hPmoment : ∀ μ ∈ P, ∀ n, Integrable (fun x : E => ‖x‖ ^ (n + 1)) μ)
    (hPmean : ∀ μ ∈ P, ∀ n, (∫ x : E, ‖x‖ ^ (n + 1) ∂μ) ≤
      K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha))
    (hgrowth : ∀ n x, ‖φ n x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1))) :
    ∀ z ∈ ((fun μ : Measure E => ∫ x, sourceWeightedFeatureMap c p φ x ∂μ) ''
        (P ∪ boundedSupportProbabilityClass D)), ∀ n,
      ‖z n‖ ≤ featureWeight c C g p q n * (1 + D ^ (n + 1)) ∨
      ‖z n‖ ≤ featureWeight c C g p q n *
        (1 + K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha)) := by
  rintro z ⟨μ, hμ, rfl⟩ n
  rcases hμ with hμ | hμ
  · letI : IsProbabilityMeasure μ := hPprob μ hμ
    exact Or.inr ((source_population_measure_moment_bounds μ c C g p q K alpha φ
      hc hC hp hq hK hφ (hPmoment μ hμ) (hPmean μ hμ) hgrowth).2 n)
  · letI : IsProbabilityMeasure μ := hμ.1
    exact Or.inl ((source_supported_measure_moment_bounds μ c C g p q D φ
      hc hC hp hq hD hφ hμ.2 hgrowth).2.2 n)

/-- The actual source-shaped measure region has the exact anchor radius R-1.
P is retained as supplied, with explicit probability, integrability and source
moment consequences; no equality with an integer-moment class is asserted. -/
theorem source_measureMomentRegion_anchor_radius
    [BorelSpace E] [SecondCountableTopology E]
    (c C g p q K D alpha : ℝ) (φ : ∀ n, E → H n) (P : Set (Measure E))
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (hD : 1 ≤ D)
    (hφ : ∀ n, Continuous (φ n))
    (hPprob : ∀ μ ∈ P, IsProbabilityMeasure μ)
    (hPmoment : ∀ μ ∈ P, ∀ n, Integrable (fun x : E => ‖x‖ ^ (n + 1)) μ)
    (hPmean : ∀ μ ∈ P, ∀ n, (∫ x : E, ‖x‖ ^ (n + 1) ∂μ) ≤
      K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha))
    (hgrowth : ∀ n x, ‖φ n x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1)))
    (theta : lp H 2) (htheta : theta ∈ measureMomentRegion (sourceWeightedFeatureMap c p φ) P D) :
    ‖theta - sourceWeightedFeatureMap c p φ 0‖ ≤ sourceMomentRadius c C g p q K D alpha - 1 ∧
      sourceMomentRadius c C g p q K D alpha - 1 ≤ sourceMomentRadius c C g p q K D alpha := by
  apply source_moment_convexHull_anchor_radius c C g p q K D alpha φ hc hC hp hq hK hD
    ?_ _ ?_ theta htheta
  · intro n
    simpa only [norm_zero, zero_pow (Nat.succ_ne_zero n), add_zero, mul_one] using hgrowth n 0
  · exact source_measureMomentRegion_generator_coordinate_bounds c C g p q K D alpha φ P
      hc hC hp hq hK hD hφ hPprob hPmoment hPmean hgrowth

end Source

end PaperFormalization.Manuscript
