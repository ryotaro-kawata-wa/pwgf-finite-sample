import PaperFormalization.Manuscript.SourceMomentClass
import PaperFormalization.Manuscript.CoordinateMoments
import PaperFormalization.Manuscript.FeatureResidual
import Mathlib.Analysis.Calculus.MeanValue

/-! # Actual coordinate moments and residual regularity under one fixed path law

Every population integral uses the same probability measure on paths. The
marginal at each time is its actual pushforward and belongs to the original
all-real-order source moment class. No conditioning, independence, or law
identification is inferred from empirical localization. One common AE event
carries the path Lipschitz property. Coordinate and residual rates retain the
source feature index m=n+1 and its exact previous-order moment envelope.
-/

open MeasureTheory Set Filter
open scoped NNReal BigOperators

namespace PaperFormalization.Manuscript

section PathMoments

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
  [NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E]

/-- Source-class membership of the actual pushforward gives genuine integer
moment integrability and its numerical bound under the original path law. -/
theorem source_path_norm_pow_moment
    (μ : Measure Ω) (X : Ω → E) (alpha K : ℝ) (hK : 0 < K)
    (hX : AEStronglyMeasurable X μ) (hclass : μ.map X ∈ sourceMomentClass alpha K)
    (m : ℕ) (hm : 1 ≤ m) :
    Integrable (fun ω => ‖X ω‖ ^ m) μ ∧
      (∫ ω, ‖X ω‖ ^ m ∂μ) ≤ K ^ m * (m : ℝ) ^ ((m : ℝ) / alpha) := by
  have hi := sourceMomentClass_integrable_norm_pow alpha K (μ.map X) hclass m hm
  have hb := sourceMomentClass_integral_norm_pow_le alpha K hK (μ.map X) hclass m hm
  constructor
  · exact (integrable_map_measure (continuous_norm.pow m).aestronglyMeasurable
      hX.aemeasurable).mp hi
  · have heq := integral_map (f := fun z : E => ‖z‖ ^ m) hX.aemeasurable
      (continuous_norm.pow m).aestronglyMeasurable
    rw [heq] at hb
    exact hb

/-- The previous-order moment has exactly the source m-th-order scale.
At n=0 its integral is one; no zero-order class condition is introduced. -/
theorem source_path_previous_moment
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E)
    (alpha K : ℝ) (halpha : 0 < alpha) (hK : 0 < K)
    (hX : AEStronglyMeasurable X μ) (hclass : μ.map X ∈ sourceMomentClass alpha K)
    (n : ℕ) :
    Integrable (fun ω => ‖X ω‖ ^ n) μ ∧
      (∫ ω, ‖X ω‖ ^ n ∂μ) ≤ (K * ((n + 1 : ℕ) : ℝ) ^ (1 / alpha)) ^ n := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hn1 : 1 ≤ n := by omega
    have hm := source_path_norm_pow_moment μ X alpha K hK hX hclass n hn1
    refine ⟨hm.1, hm.2.trans ?_⟩
    calc
      K ^ n * (n : ℝ) ^ ((n : ℝ) / alpha) = (K * (n : ℝ) ^ (1 / alpha)) ^ n := by
        rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
        congr 2
        ring
      _ ≤ (K * ((n + 1 : ℕ) : ℝ) ^ (1 / alpha)) ^ n := by
        apply pow_le_pow_left₀ (by positivity)
        apply mul_le_mul_of_nonneg_left _ hK.le
        exact Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast Nat.le_succ n) (by positivity)

end PathMoments

section FeatureDifference

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Actual first-derivative growth gives the two-point feature bound used
under a fixed path law, with no additional factor in front of the norms. -/
theorem feature_sub_le_from_derivative_growth
    (φ : E → F) (n : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hdiff : Differentiable ℝ φ)
    (hderiv : ∀ z, ‖fderiv ℝ φ z‖ ≤ L * (1 + ‖z‖ ^ n)) (x y : E) :
    ‖φ x - φ y‖ ≤ L * (1 + ‖x‖ ^ n + ‖y‖ ^ n) * ‖x - y‖ := by
  let R := max ‖x‖ ‖y‖
  have hb : ∀ z ∈ Metric.closedBall (0 : E) R,
      ‖fderiv ℝ φ z‖ ≤ L * (1 + ‖x‖ ^ n + ‖y‖ ^ n) := by
    intro z hz
    have hzR : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    have hp : ‖z‖ ^ n ≤ ‖x‖ ^ n + ‖y‖ ^ n := by
      have hzn := pow_le_pow_left₀ (norm_nonneg z) hzR n
      rcases le_total ‖x‖ ‖y‖ with hxy | hyx
      · dsimp [R] at hzn
        rw [max_eq_right hxy] at hzn
        linarith [pow_nonneg (norm_nonneg x) n]
      · dsimp [R] at hzn
        rw [max_eq_left hyx] at hzn
        linarith [pow_nonneg (norm_nonneg y) n]
    exact (hderiv z).trans (mul_le_mul_of_nonneg_left (by linarith) hL)
  apply (convex_closedBall (0 : E) R).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hdiff z) hb
  · simpa only [Metric.mem_closedBall, dist_zero_right] using le_max_right ‖x‖ ‖y‖
  · simpa only [Metric.mem_closedBall, dist_zero_right] using le_max_left ‖x‖ ‖y‖

end FeatureDifference

section CoordinatePath

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] [SecondCountableTopology E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, NormedSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

/-- Actual population feature moments have precisely featurePopulationRate
under one fixed probability path law and its original marginal moment class. -/
theorem source_population_coordinate_lipschitzOn
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ → E)
    (φ : ∀ n, E → H n) (C g q K alpha : ℝ) (B : ℝ≥0) (S : Set ℝ)
    (hC : 0 ≤ C) (hK : 0 < K) (halpha : 0 < alpha)
    (hφ : ∀ n, ContDiff ℝ 1 (φ n))
    (hgrowth : ∀ n z k, k ≤ 1 → ‖iteratedFDeriv ℝ k (φ n) z‖ ≤
      featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1 - k)))
    (hY : ∀ t ∈ S, AEStronglyMeasurable (fun ω => Y ω t) μ)
    (hclass : ∀ t ∈ S, μ.map (fun ω => Y ω t) ∈ sourceMomentClass alpha K)
    (hpath : ∀ᵐ ω ∂μ, LipschitzOnWith B (Y ω) S) (n : ℕ) :
    LipschitzOnWith (featurePopulationRate B C g q K alpha n)
      (fun t => ∫ ω, φ n (Y ω t) ∂μ) S := by
  have hvalue : ∀ z, ‖φ n z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1)) := by
    intro z
    simpa only [norm_iteratedFDeriv_zero, Nat.sub_zero] using hgrowth n z 0 (by omega)
  have hderiv : ∀ z, ‖fderiv ℝ (φ n) z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ n) := by
    intro z
    simpa only [norm_iteratedFDeriv_one, Nat.add_sub_cancel] using hgrowth n z 1 (by omega)
  have hdiff := feature_sub_le_from_derivative_growth (φ n) n (featureGrowth C g q n)
    (featureGrowth_nonneg C g q hC n) ((hφ n).differentiable (by norm_num)) hderiv
  have hint : ∀ t ∈ S, Integrable (fun ω => φ n (Y ω t)) μ := by
    intro t ht
    exact coordinate_feature_integrable μ (fun ω => Y ω t) (φ n) (n + 1)
      (featureGrowth C g q n) (hY t ht) (hφ n).continuous
      (source_path_norm_pow_moment μ (fun ω => Y ω t) alpha K hK (hY t ht)
        (hclass t ht) (n + 1) (by omega)).1 hvalue
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht u hu
  rw [dist_eq_norm, featurePopulationRate_coe B C g q K alpha hC hK.le n]
  have hpair : ∀ᵐ ω ∂μ, ‖Y ω t - Y ω u‖ ≤ (B : ℝ) * dist t u := by
    filter_upwards [hpath] with ω hω
    simpa only [dist_eq_norm] using hω.dist_le_mul t ht u hu
  have hmt := source_path_previous_moment μ (fun ω => Y ω t) alpha K halpha hK
    (hY t ht) (hclass t ht) n
  have hmu := source_path_previous_moment μ (fun ω => Y ω u) alpha K halpha hK
    (hY u hu) (hclass u hu) n
  exact norm_coordinate_feature_integral_sub_le μ (fun ω => Y ω t) (fun ω => Y ω u)
    (φ n) n (featureGrowth C g q n) B
    ((K * ((n + 1 : ℕ) : ℝ) ^ (1 / alpha)) ^ n) (dist t u)
    (featureGrowth_nonneg C g q hC n) B.coe_nonneg dist_nonneg
    (hint t ht) (hint u hu) hmt.1 hmu.1 hmt.2 hmu.2 hpair hdiff

omit [NormedSpace ℝ E] in
/-- Actual population feature integrability and amplitude under the same
fixed path measure, derived from its time-marginal source-class membership. -/
theorem source_population_coordinate_amplitude
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → E)
    (φ : ∀ n, E → H n) (C g q K alpha : ℝ) (hC : 0 ≤ C) (hK : 0 < K)
    (hφ : ∀ n, Continuous (φ n))
    (hgrowth : ∀ n z, ‖φ n z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1)))
    (hY : AEStronglyMeasurable Y μ) (hclass : μ.map Y ∈ sourceMomentClass alpha K) (n : ℕ) :
    Integrable (fun ω => φ n (Y ω)) μ ∧
      ‖∫ ω, φ n (Y ω) ∂μ‖ ≤ featureGrowth C g q n *
        (1 + K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha)) := by
  have hm := source_path_norm_pow_moment μ Y alpha K hK hY hclass (n + 1) (by omega)
  exact ⟨coordinate_feature_integrable μ Y (φ n) (n + 1) (featureGrowth C g q n)
      hY (hφ n) hm.1 (hgrowth n),
    norm_coordinate_feature_integral_le μ Y (φ n) (n + 1) (featureGrowth C g q n) _
      (featureGrowth_nonneg C g q hC n) hm.1 hm.2 (hgrowth n)⟩

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [∀ n, CompleteSpace (H n)] in
/-- Localized B-Lipschitz particle paths give the actual empirical coordinate
rate B L_m(1+D^(m-1)), preserving the exact reciprocal particle count. -/
theorem source_empirical_coordinate_lipschitzOn
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (X : ι → ℝ → E) (φ : ∀ n, E → H n) (C g q D : ℝ) (B : ℝ≥0) (S : Set ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hφ : ∀ n, ContDiff ℝ 1 (φ n))
    (hgrowth : ∀ n z, ‖fderiv ℝ (φ n) z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ n))
    (hX : ∀ i, LipschitzOnWith B (X i) S) (hXloc : ∀ i t, t ∈ S → ‖X i t‖ ≤ D) (n : ℕ) :
    LipschitzOnWith (featureEmpiricalRate B C g q D n)
      (fun t => finiteFeatureMean (fun i => φ n (X i t))) S := by
  apply finiteFeatureMean_lipschitzOn
  intro i
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht u hu
  rw [dist_eq_norm, featureEmpiricalRate_coe B C g q D hC hD n]
  have hb : ∀ z ∈ Metric.closedBall (0 : E) D,
      ‖fderiv ℝ (φ n) z‖ ≤ featureGrowth C g q n * (1 + D ^ n) := by
    intro z hz
    have hzD : ‖z‖ ≤ D := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    exact (hgrowth n z).trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg z) hzD n)) (featureGrowth_nonneg C g q hC n))
  have hmvt := (convex_closedBall (0 : E) D).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hφ n).differentiable (by norm_num) z) hb
    (show X i u ∈ Metric.closedBall (0 : E) D by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hXloc i u hu)
    (show X i t ∈ Metric.closedBall (0 : E) D by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hXloc i t ht)
  have hx := (hX i).dist_le_mul t ht u hu
  rw [dist_eq_norm] at hx
  calc
    _ ≤ featureGrowth C g q n * (1 + D ^ n) * ‖X i t - X i u‖ := hmvt
    _ ≤ featureGrowth C g q n * (1 + D ^ n) * ((B : ℝ) * dist t u) :=
      mul_le_mul_of_nonneg_left hx (mul_nonneg (featureGrowth_nonneg C g q hC n) (by positivity))
    _ = _ := by ring

/-- The literal residual of actual empirical means and actual fixed-law
population expectations converges and is Lipschitz at the source rate series.
All coordinate amplitudes and rates are derived here from source hypotheses. -/
theorem source_momentResidual_lipschitzOn
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ → E) (X : ι → ℝ → E)
    (φ : ∀ n, E → H n) (c C g p q K D alpha : ℝ) (L B : ℝ≥0) (S : Set ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hK : 0 < K) (hD : 1 ≤ D) (halpha : 0 < alpha)
    (hφ : ∀ n, ContDiff ℝ 1 (φ n))
    (hgrowth : ∀ n z k, k ≤ 1 → ‖iteratedFDeriv ℝ k (φ n) z‖ ≤
      featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1 - k)))
    (hY : ∀ t ∈ S, AEStronglyMeasurable (fun ω => Y ω t) μ)
    (hclass : ∀ t ∈ S, μ.map (fun ω => Y ω t) ∈ sourceMomentClass alpha K)
    (hpath : ∀ᵐ ω ∂μ, LipschitzOnWith B (Y ω) S)
    (hX : ∀ i, LipschitzOnWith B (X i) S) (hXloc : ∀ i t, t ∈ S → ‖X i t‖ ≤ D) :
    let Emp := fun n t => finiteFeatureMean (fun i => φ n (X i t))
    let Pop := fun n t => ∫ ω, φ n (Y ω t) ∂μ
    (∀ t ∈ S, Summable (fun n => momentResidualTerm (featureResidualWeight c p L) Emp Pop n t)) ∧
      LipschitzOnWith (∑' n, featureResidualWeight c p L n *
        (featureEmpiricalRate B C g q D n + featurePopulationRate B C g q K alpha n))
        (momentResidual (featureResidualWeight c p L) Emp Pop) S := by
  have hvalue : ∀ n z, ‖φ n z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1)) := by
    intro n z
    simpa only [norm_iteratedFDeriv_zero, Nat.sub_zero] using hgrowth n z 0 (by omega)
  have hderiv : ∀ n z, ‖fderiv ℝ (φ n) z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ n) := by
    intro n z
    simpa only [norm_iteratedFDeriv_one, Nat.add_sub_cancel] using hgrowth n z 1 (by omega)
  let Emp := fun n t => finiteFeatureMean (fun i => φ n (X i t))
  let Pop := fun n t => ∫ ω, φ n (Y ω t) ∂μ
  have hEmp : ∀ n t, t ∈ S → ‖Emp n t‖ ≤ featureGrowth C g q n * (1 + D ^ (n + 1)) := by
    intro n t ht
    exact norm_empirical_feature_mean_le (fun i => X i t) (φ n) (n + 1)
      (featureGrowth C g q n) D (featureGrowth_nonneg C g q hC n)
      (fun i => hXloc i t ht) (hvalue n)
  have hPop : ∀ n t, t ∈ S → ‖Pop n t‖ ≤ featureGrowth C g q n *
      (1 + K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha)) := by
    intro n t ht
    exact (source_population_coordinate_amplitude μ (fun ω => Y ω t) φ C g q K alpha hC hK
      (fun n => (hφ n).continuous) hvalue (hY t ht) (hclass t ht) n).2
  exact ⟨featureResidual_summable Emp Pop c C g p q K D alpha L S
      hc hp hq hK (by linarith) hEmp hPop,
    featureResidual_lipschitzOn Emp Pop c C g p q K D alpha L B S
      hc hC hp hq hK hD halpha hEmp hPop
      (source_empirical_coordinate_lipschitzOn X φ C g q D B S hC (by linarith) hφ hderiv hX hXloc)
      (source_population_coordinate_lipschitzOn μ Y φ C g q K alpha B S
        hC hK halpha hφ hgrowth hY hclass hpath)⟩

/-- On a closed branch, the actual source residual is absolutely continuous
and interval-integrable, with no separately supplied coordinate estimates. -/
theorem source_momentResidual_branch_regularity
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ → E) (X : ι → ℝ → E)
    (φ : ∀ n, E → H n) (c C g p q K D alpha : ℝ) (L B : ℝ≥0) (a b : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hK : 0 < K) (hD : 1 ≤ D) (halpha : 0 < alpha)
    (hφ : ∀ n, ContDiff ℝ 1 (φ n))
    (hgrowth : ∀ n z k, k ≤ 1 → ‖iteratedFDeriv ℝ k (φ n) z‖ ≤
      featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1 - k)))
    (hY : ∀ t ∈ uIcc a b, AEStronglyMeasurable (fun ω => Y ω t) μ)
    (hclass : ∀ t ∈ uIcc a b, μ.map (fun ω => Y ω t) ∈ sourceMomentClass alpha K)
    (hpath : ∀ᵐ ω ∂μ, LipschitzOnWith B (Y ω) (uIcc a b))
    (hX : ∀ i, LipschitzOnWith B (X i) (uIcc a b))
    (hXloc : ∀ i t, t ∈ uIcc a b → ‖X i t‖ ≤ D) :
    let Gamma := momentResidual (featureResidualWeight c p L)
      (fun n t => finiteFeatureMean (fun i => φ n (X i t)))
      (fun n t => ∫ ω, φ n (Y ω t) ∂μ)
    AbsolutelyContinuousOnInterval Gamma a b ∧ IntervalIntegrable Gamma volume a b := by
  have hl := (source_momentResidual_lipschitzOn μ Y X φ c C g p q K D alpha L B (uIcc a b)
    hc hC hp hq hK hD halpha hφ hgrowth hY hclass hpath hX hXloc).2
  exact ⟨hl.absolutelyContinuousOnInterval, hl.continuousOn.intervalIntegrable⟩

end CoordinatePath

end PaperFormalization.Manuscript
