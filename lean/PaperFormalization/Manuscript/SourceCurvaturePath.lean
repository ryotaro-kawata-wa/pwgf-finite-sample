import PaperFormalization.Manuscript.SourceMomentPathRegularity
import PaperFormalization.Manuscript.SourceODEDrift
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-! # Actual fixed-law moment and full sampled-curvature paths

The population moment is the genuine Hilbert-valued Bochner integral under
one fixed probability measure on paths. Its source coordinate rates give a
summable Hilbert norm majorant. The full population-sampled Hessian retains
both blocks and the exact 1/N normalization; it is not the derivative of a
field with its population moment frozen.
-/

open MeasureTheory Set Filter
open scoped NNReal BigOperators

set_option maxSynthPendingDepth 8

namespace PaperFormalization.Manuscript

open Continuous

/-- The population coordinate rates alone have a summable source-weighted
majorant, extracted from the already proved full residual rate series. -/
theorem summable_source_population_rate (c C g p q K alpha : ℝ) (B : ℝ≥0)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hK : 0 ≤ K) (halpha : 0 < alpha) :
    Summable (fun n => (featureResidualWeight c p 1 n : ℝ) *
      (featurePopulationRate B C g q K alpha n : ℝ)) := by
  apply (summable_featureResidual_rate c C g p q K 1 alpha 1 B
    hc hC hp hq hK le_rfl halpha).of_nonneg_of_le
  · intro n
    positivity
  · intro n
    exact mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (featureEmpiricalRate B C g q 1 n).coe_nonneg)
      (featureResidualWeight c p 1 n).coe_nonneg

section Population

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] [SecondCountableTopology E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

/-- The actual Hilbert-valued population integral is Lipschitz with the exact
sum of weighted coordinate rates, under the same fixed probability path law. -/
theorem source_population_hilbertMoment_lipschitzOn
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ → E)
    (φ : ∀ n, E → H n) (c C g p q K alpha : ℝ) (B : ℝ≥0) (S : Set ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (halpha : 0 < alpha)
    (hφ : ∀ n, ContDiff ℝ 1 (φ n))
    (hgrowth : ∀ n z k, k ≤ 1 → ‖iteratedFDeriv ℝ k (φ n) z‖ ≤
      featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1 - k)))
    (hY : ∀ t ∈ S, AEStronglyMeasurable (fun ω => Y ω t) μ)
    (hclass : ∀ t ∈ S, μ.map (fun ω => Y ω t) ∈ sourceMomentClass alpha K)
    (hpath : ∀ᵐ ω ∂μ, LipschitzOnWith B (Y ω) S) :
    LipschitzOnWith (∑' n, featureResidualWeight c p 1 n * featurePopulationRate B C g q K alpha n)
      (fun t => ∫ ω, sourceWeightedFeatureMap c p φ (Y ω t) ∂μ) S := by
  have hvalue : ∀ n z, ‖φ n z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1)) := by
    intro n z
    simpa only [norm_iteratedFDeriv_zero, Nat.sub_zero] using hgrowth n z 0 (by omega)
  have hcoord : ∀ t ∈ S, ∀ n,
      (∫ ω, sourceWeightedFeatureMap c p φ (Y ω t) ∂μ) n =
        sourceFeatureScale c p n • ∫ ω, φ n (Y ω t) ∂μ := by
    intro t ht
    exact source_population_moment_apply μ (fun ω => Y ω t) c C g p q K alpha φ
      hc hC hp hq hK (hY t ht) (fun n => (hφ n).continuous)
      (fun n => (source_path_norm_pow_moment μ (fun ω => Y ω t) alpha K hK
        (hY t ht) (hclass t ht) (n + 1) (by omega)).1)
      (fun n => (source_path_norm_pow_moment μ (fun ω => Y ω t) alpha K hK
        (hY t ht) (hclass t ht) (n + 1) (by omega)).2) hvalue
  have hr := source_population_coordinate_lipschitzOn μ Y φ C g q K alpha B S
    hC hK halpha hφ hgrowth hY hclass hpath
  have hs := summable_source_population_rate c C g p q K alpha B hc hC hp hq hK.le halpha
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht u hu
  rw [dist_eq_norm, NNReal.coe_tsum]
  simp only [NNReal.coe_mul]
  rw [← tsum_mul_right]
  apply norm_hilbertSum_le_of_hasSum_coordinate_majorant _ _ _ (hs.mul_right (dist t u)).hasSum
  intro n
  change ‖(∫ ω, sourceWeightedFeatureMap c p φ (Y ω t) ∂μ) n -
    (∫ ω, sourceWeightedFeatureMap c p φ (Y ω u) ∂μ) n‖ ≤ _
  rw [hcoord t ht n, hcoord u hu n, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_pos (sourceFeatureScale_pos c p n)]
  have hn := (hr n).dist_le_mul t ht u hu
  rw [dist_eq_norm] at hn
  calc
    _ ≤ sourceFeatureScale c p n * ((featurePopulationRate B C g q K alpha n : ℝ) * dist t u) :=
      mul_le_mul_of_nonneg_left hn (sourceFeatureScale_pos c p n).le
    _ = _ := by rw [featureResidualWeight_coe]; simp only [NNReal.coe_one, one_mul, sourceFeatureScale, mul_assoc]

end Population

section OperatorContinuity

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Continuous individual blocks give operator-norm continuity of the
actual normalized finite sampled block operator. -/
theorem continuousOn_sampledBlockOperator
    (D : ℝ → ι → E →L[ℝ] E) (K : ℝ → ι → ι → E →L[ℝ] E) (S : Set ℝ)
    (hD : ∀ i, ContinuousOn (fun t => D t i) S)
    (hK : ∀ i j, ContinuousOn (fun t => K t i j) S) :
    ContinuousOn (fun t => sampledBlockOperator (D t) (K t)) S := by
  classical
  let Q := PiLp 2 fun _ : ι => E
  have hd : ContinuousOn (fun t => diagonalOperator (D t)) S := by
    apply ContinuousOn.clm_comp continuousOn_const
    exact (ContinuousLinearMap.piEquivL ℝ Q (fun _ : ι => E)).continuous.comp_continuousOn
      (continuousOn_pi.mpr fun i => (hD i).clm_comp continuousOn_const)
  have hk : ContinuousOn (fun t => blockOperator (K t)) S := by
    apply ContinuousOn.clm_comp continuousOn_const
    exact (ContinuousLinearMap.piEquivL ℝ Q (fun _ : ι => E)).continuous.comp_continuousOn
      (continuousOn_pi.mpr fun i => continuousOn_finsetSum _
        (fun j _ => (hK i j).clm_comp continuousOn_const))
  exact hd.add (hk.const_smul (Fintype.card ι : ℝ)⁻¹)

end OperatorContinuity

section HessianContinuity

variable {ι E F : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Actual local C2 feature regularity and local C3 of G give continuity of
the full sampled Hessian along continuous particle and moment paths. -/
theorem continuousOn_sampledMomentHessian
    (J : E → F) (G : F → ℝ) (U : Set F) (S : Set ℝ)
    (hJ : ContDiff ℝ 2 J) (hU : IsOpen U) (hG : ContDiffOn ℝ 3 G U)
    (theta : ℝ → F) (htheta : ContinuousOn theta S) (hthetaU : MapsTo theta S U)
    (X : ℝ → PiLp 2 fun _ : ι => E) (hX : ∀ i, ContinuousOn (fun t => X t i) S) :
    ContinuousOn (fun t => sampledMomentHessian J G (theta t) (X t)) S := by
  have hdJ : ∀ i, ContinuousOn (fun t => fderiv ℝ J (X t i)) S := fun i =>
    (hJ.continuous_fderiv (by norm_num)).comp_continuousOn (hX i)
  have hddJ : ∀ i, ContinuousOn (fun t => fderiv ℝ (fderiv ℝ J) (X t i)) S := fun i =>
    ((hJ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).comp_continuousOn (hX i)
  have hdG : ContinuousOn (fun t => fderiv ℝ G (theta t)) S :=
    (hG.continuousOn_fderiv_of_isOpen hU (by norm_num)).comp htheta hthetaU
  have hddG : ContinuousOn (fun t => fderiv ℝ (fderiv ℝ G) (theta t)) S :=
    ((hG.fderiv_of_isOpen hU (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hU le_rfl).comp
      htheta hthetaU
  have hg : ContinuousOn (fun t => gradient G (theta t)) S :=
    (InnerProductSpace.toDual ℝ F).symm.continuous.comp_continuousOn hdG
  have hH : ContinuousOn (fun t => momentObjectiveHessian G (theta t)) S :=
    continuousOn_const.clm_comp hddG
  apply continuousOn_sampledBlockOperator
  · intro i
    have hadj : ContinuousOn (fun t => (realAdjointLinear (E := E) (H := F)).comp
        (fderiv ℝ (fderiv ℝ J) (X t i))) S := continuousOn_const.clm_comp (hddJ i)
    exact ((ContinuousLinearMap.flipₗᵢ ℝ E F E).continuous.comp_continuousOn hadj).clm_apply hg
  · intro i j
    have hadj : ContinuousOn (fun t => (fderiv ℝ J (X t i)).adjoint) S :=
      (realAdjointLinear (E := E) (H := F)).continuous.comp_continuousOn (hdJ i)
    exact hadj.clm_comp (hH.clm_comp (hdJ j))

end HessianContinuity

section SourceCurvature

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [BorelSpace E] [SecondCountableTopology E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]
variable {ι : Type*} [Fintype ι]

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ → E)
  (φ : ∀ n, E → H n) (c C g p q K D alpha : ℝ) (B : ℝ≥0)
  (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (halpha : 0 < alpha)
  (hφ : ∀ n, ContDiff ℝ 2 (φ n))
  (hgrowth : ∀ n z k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) z‖ ≤
    featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1 - k)))
  (G : lp H 2 → ℝ) (U : Set (lp H 2)) (hU : IsOpen U)
  (hSU : measureMomentRegion (sourceWeightedFeatureMap c p φ) (sourceMomentClass alpha K) D ⊆ U)
  (hG : ContDiffOn ℝ 3 G U)

include hc hC hp hq hK halpha hφ hgrowth hU hSU hG

/-- The actual full population-sampled Hessian is continuous on the branch.
Population membership in the original U is derived from its actual marginal
law; no continuity or membership of the Hilbert moment path is assumed. -/
theorem source_sampledHessian_continuousOn
    (S : Set ℝ)
    (hY : ∀ t ∈ S, AEStronglyMeasurable (fun ω => Y ω t) μ)
    (hclass : ∀ t ∈ S, μ.map (fun ω => Y ω t) ∈ sourceMomentClass alpha K)
    (hpath : ∀ᵐ ω ∂μ, LipschitzOnWith B (Y ω) S)
    (X : ℝ → PiLp 2 fun _ : ι => E) (hX : ∀ i, ContinuousOn (fun t => X t i) S) :
    ContinuousOn (fun t => sampledMomentHessian (sourceWeightedFeatureMap c p φ) G
      (∫ ω, sourceWeightedFeatureMap c p φ (Y ω t) ∂μ) (X t)) S := by
  let J := sourceWeightedFeatureMap c p φ
  have hJ : ContDiff ℝ 2 J :=
    contDiff_sourceWeightedFeatureMap c C g p q φ hc hC hp hq hφ hgrowth
  have hm := source_population_hilbertMoment_lipschitzOn μ Y φ c C g p q K alpha B S
    hc hC hp hq hK halpha (fun n => (hφ n).of_le (by norm_num))
    (fun n z k hk => hgrowth n z k (by omega)) hY hclass hpath
  apply continuousOn_sampledMomentHessian J G U S hJ hU hG
    (fun t => ∫ ω, J (Y ω t) ∂μ) hm.continuousOn ?_ X hX
  intro t ht
  have hmem := population_integral_mem_measureMomentRegion J (sourceMomentClass alpha K) D
    (μ.map (fun ω => Y ω t)) (hclass t ht)
  have heq := coordinate_feature_integral_map μ (fun ω => Y ω t) J (hY t ht).aemeasurable hJ.continuous
  rw [heq] at hmem
  exact hSU hmem

/-- On a closed branch the literal unit-sphere Rayleigh infimum of the full
population-sampled Hessian is continuous and interval-integrable. Nontrivial
particle space and nonempty sample index ensure a nonempty unit sphere; no
eigenvalue or attainment characterization is substituted. -/
theorem source_curvature_branch_regularity [Nontrivial E] [Nonempty ι]
    (a b : ℝ)
    (hY : ∀ t ∈ uIcc a b, AEStronglyMeasurable (fun ω => Y ω t) μ)
    (hclass : ∀ t ∈ uIcc a b, μ.map (fun ω => Y ω t) ∈ sourceMomentClass alpha K)
    (hpath : ∀ᵐ ω ∂μ, LipschitzOnWith B (Y ω) (uIcc a b))
    (X : ℝ → PiLp 2 fun _ : ι => E)
    (hX : ∀ i, ContinuousOn (fun t => X t i) (uIcc a b)) :
    let A := fun t => sampledMomentHessian (sourceWeightedFeatureMap c p φ) G
      (∫ ω, sourceWeightedFeatureMap c p φ (Y ω t) ∂μ) (X t)
    ContinuousOn A (uIcc a b) ∧
      ContinuousOn (fun t => rayleighInf (A t)) (uIcc a b) ∧
      IntervalIntegrable (fun t => rayleighInf (A t)) volume a b := by
  have hA := source_sampledHessian_continuousOn μ Y φ c C g p q K D alpha B
    hc hC hp hq hK halpha hφ hgrowth G U hU hSU hG (uIcc a b) hY hclass hpath X hX
  exact ⟨hA, rayleighInf_continuousOn _ _ hA, rayleighInf_intervalIntegrable _ a b hA⟩

end SourceCurvature

end PaperFormalization.Manuscript
