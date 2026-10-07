import PaperFormalization.Manuscript.BlockODE
import PaperFormalization.Manuscript.FeatureDisplacement
import PaperFormalization.Manuscript.SourceEmpiricalPopulationField
import PaperFormalization.Manuscript.SourceSegmentRegularity
import PaperFormalization.Manuscript.SourceMomentClass
import PaperFormalization.Manuscript.SourceLocalField

/-! # Actual source-model nonlinear drift

The empirical negative-gradient field and the population field use their
actual Hilbert-valued moments. The full population-sampled Hessian retains
its kernel blocks; it is not the derivative of the frozen population field.
The original all-real-order population class, local objective hypotheses,
source feature bounds, localization, and anti-spikiness derive the block
mismatch and residual estimates. The coefficients remain the literal source
Gamma, Lambda, and L=4 Q R^3, without additional dimension or particle factors.
-/

open MeasureTheory Set
open scoped BigOperators NNReal

set_option maxSynthPendingDepth 8

namespace PaperFormalization.Manuscript

open Continuous

section Definition

variable {ι E F : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The full sampled Hessian at a supplied moment and configuration, keeping
both spatial and normalized integral blocks even for a population moment. -/
noncomputable def sampledMomentHessian (J : E → F) (G : F → ℝ) (theta : F)
    (Y : PiLp 2 fun _ : ι => E) :
    (PiLp 2 fun _ : ι => E) →L[ℝ] (PiLp 2 fun _ : ι => E) :=
  sampledBlockOperator
    (fun i => momentSpatialHessian (fderiv ℝ (fderiv ℝ J) (Y i)) (gradient G theta))
    (fun i j => momentIntegralHessian (fderiv ℝ J (Y i)) (fderiv ℝ J (Y j))
      (momentObjectiveHessian G theta))

end Definition

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]
variable {N : ℕ}

variable (c C g p q K D alpha C3 : ℝ) (φ : ∀ n, E → H n)
  (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (hD : 1 ≤ D)
  (hφ : ∀ n, ContDiff ℝ 2 (φ n))
  (hgrowth : ∀ n z k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) z‖ ≤
    featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1 - k)))
  (hthirdφ : ∀ n z, DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ (φ n))) z)
  (hgrowth₃ : ∀ n z, ‖iteratedFDeriv ℝ 3 (φ n) z‖ ≤
    featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1 - 3)))
  (G : lp H 2 → ℝ) (U : Set (lp H 2)) (hU : IsOpen U)
  (hSU : measureMomentRegion (sourceWeightedFeatureMap c p φ) (sourceMomentClass alpha K) D ⊆ U)
  (hG : ContDiffOn ℝ 3 G U)
  (hthirdG : ∀ theta ∈ measureMomentRegion (sourceWeightedFeatureMap c p φ)
      (sourceMomentClass alpha K) D, ‖iteratedFDeriv ℝ 3 G theta‖ ≤ C3)
  (L : ℝ≥0) (hL : (L : ℝ) = sourceComparisonEnvelope c C g p q K D alpha C3 φ G)
  (μ : Measure E) (hμ : μ ∈ sourceMomentClass alpha K)

include hc hC hp hq hK hD hφ hgrowth hthirdφ hgrowth₃ hU hSU hG hthirdG hL hμ

/-- Point-slot changes at the actual population moment have the literal
source L bound. Probability and genuine moment bounds come from the same
original all-real-order class; no lower objective derivative bound is assumed. -/
theorem source_population_spatial_bounds
    (x x' y y' : E) (hx : ‖x‖ ≤ D) (hx' : ‖x'‖ ≤ D)
    (hy : ‖y‖ ≤ D) (hy' : ‖y'‖ ≤ D) :
    let J := sourceWeightedFeatureMap c p φ
    let theta := ∫ z, J z ∂μ
    ‖momentSpatialHessian (fderiv ℝ (fderiv ℝ J) x) (gradient G theta) -
      momentSpatialHessian (fderiv ℝ (fderiv ℝ J) x') (gradient G theta)‖ ≤
        (L : ℝ) * ‖x - x'‖ ∧
    ‖momentIntegralHessian (fderiv ℝ J x) (fderiv ℝ J y) (momentObjectiveHessian G theta) -
      momentIntegralHessian (fderiv ℝ J x') (fderiv ℝ J y') (momentObjectiveHessian G theta)‖ ≤
        (L : ℝ) * (‖x - x'‖ + ‖y - y'‖) := by
  have hvalue : ∀ n z, ‖φ n z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1)) := by
    intro n z
    simpa only [norm_iteratedFDeriv_zero, Nat.sub_zero] using hgrowth n z 0 (by omega)
  have hb := source_measure_region_objective_bounds c C g p q K D alpha C3 φ
    (sourceMomentClass alpha K) hc hC hp hq hK hD (fun n => (hφ n).continuous)
    (sourceMomentClass_isProbabilityMeasure alpha K)
    (fun ν hν n => (sourceMomentClass_succ_moment alpha K hK ν hν n).1)
    (fun ν hν n => (sourceMomentClass_succ_moment alpha K hK ν hν n).2)
    hvalue G U hU hSU hG hthirdG
  have ht := hb.2 _ (population_integral_mem_measureMomentRegion
    (sourceWeightedFeatureMap c p φ) (sourceMomentClass alpha K) D μ hμ)
  have hxJ := source_feature_norms_le_radius c C g p q K D alpha φ
    hc hC hp hq hK hD hφ hgrowth x' hx'
  have hyJ := source_feature_norms_le_radius c C g p q K D alpha φ
    hc hC hp hq hK hD hφ hgrowth y hy
  have hs := source_moment_spatial_bounds (fderiv ℝ (sourceWeightedFeatureMap c p φ))
    (gradient G) (∫ z, sourceWeightedFeatureMap c p φ z ∂μ) x x' y y'
    (fderiv ℝ (fderiv ℝ (sourceWeightedFeatureMap c p φ)) x)
    (fderiv ℝ (fderiv ℝ (sourceWeightedFeatureMap c p φ)) x')
    (momentObjectiveHessian G (∫ z, sourceWeightedFeatureMap c p φ z ∂μ))
    (sourceObjectiveAnchorFactor c p C3 φ G) (sourceMomentRadius c C g p q K D alpha)
    hb.1 (one_le_sourceMomentRadius c C g p q K D alpha hC hK.le (by linarith))
    hxJ.2.1 hyJ.2.1
    (source_feature_fderiv_sub_le_radius c C g p q K D alpha φ
      hc hC hp hq hK hD hφ hgrowth x x' hx hx')
    (source_feature_fderiv_sub_le_radius c C g p q K D alpha φ
      hc hC hp hq hK hD hφ hgrowth y y' hy hy')
    (source_feature_second_fderiv_sub_le_radius c C g p q K D alpha φ
      hc hC hp hq hK hD hφ hgrowth hthirdφ hgrowth₃ x x' hx hx') ht.1 ht.2
  simpa only [hL, sourceComparisonEnvelope] using hs.2

/-- The actual source blocks yield the normalized quadratic mismatch and
actual particle residual needed by the ODE drift theorem. The full population
sampled Hessian is used for curvature, including its integral block. -/
theorem source_hessian_mismatch_and_residual
    (X Y : PiLp 2 fun _ : Fin N => E) (hN : 0 < N)
    (hX : ∀ i, ‖X i‖ ≤ D) (hY : ∀ i, ‖Y i‖ ≤ D) (A_sp : ℝ)
    (hanti : (N : ℝ)⁻¹ * ∑ i : Fin N, ‖(X - Y) i‖ ^ 3 ≤
      A_sp * (‖X - Y‖ / Real.sqrt N) ^ 3) :
    let J := sourceWeightedFeatureMap c p φ
    let theta := ∫ z, J z ∂μ
    let V := empiricalConfigurationField (ι := Fin N) J
      (momentGradientField (fderiv ℝ J) (gradient G))
    let w := frozenMomentConfigurationField (momentGradientField (fderiv ℝ J) (gradient G)) theta Y
    let Gamma := momentResidual (featureResidualWeight c p L)
      (fun n _ => finiteFeatureMean (fun i => φ n (Y i))) (fun n _ => ∫ z, φ n z ∂μ) 0
    let r := ‖X - Y‖ / Real.sqrt N
    (∀ s ∈ Icc (0 : ℝ) 1,
      |inner ℝ (X - Y) ((empiricalMomentHessian J G (Y + s • (X - Y)) -
        sampledMomentHessian J G theta Y) (X - Y)) / N| ≤
          (featureDisplacementLambda c C g p q D L + (2 + A_sp) * (L : ℝ)) * r ^ 3 +
            Gamma * r ^ 2) ∧
      ∀ i, ‖(V Y - w) i‖ ≤ Gamma := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  letI : IsProbabilityMeasure μ := sourceMomentClass_isProbabilityMeasure alpha K μ hμ
  let J := sourceWeightedFeatureMap c p φ
  let theta := ∫ z, J z ∂μ
  let Z := fun s : ℝ => Y + s • (X - Y)
  let Ds := fun s i => momentSpatialHessian (fderiv ℝ (fderiv ℝ J) (Z s i))
    (gradient G (empiricalMomentMap J (Z s)))
  let Ks := fun s i j => momentIntegralHessian (fderiv ℝ J (Z s i)) (fderiv ℝ J (Z s j))
    (momentObjectiveHessian G (empiricalMomentMap J (Z s)))
  let Dm := fun s i => momentSpatialHessian (fderiv ℝ (fderiv ℝ J) (Z s i)) (gradient G theta)
  let Km := fun s i j => momentIntegralHessian (fderiv ℝ J (Z s i)) (fderiv ℝ J (Z s j))
    (momentObjectiveHessian G theta)
  let Dr := fun i => momentSpatialHessian (fderiv ℝ (fderiv ℝ J) (Y i)) (gradient G theta)
  let Kr := fun i j => momentIntegralHessian (fderiv ℝ J (Y i)) (fderiv ℝ J (Y j))
    (momentObjectiveHessian G theta)
  let gamma := fun W : PiLp 2 fun _ : Fin N => E =>
    momentResidual (featureResidualWeight c p L)
      (fun n _ => finiteFeatureMean (fun i => φ n (W i))) (fun n _ => ∫ z, φ n z ∂μ) 0
  let b := fun s => gamma (Z s)
  have hvalue : ∀ n z, ‖φ n z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1)) := by
    intro n z
    simpa only [norm_iteratedFDeriv_zero, Nat.sub_zero] using hgrowth n z 0 (by omega)
  have hdiff : ∀ n z, z ∈ Metric.closedBall (0 : E) D → DifferentiableAt ℝ (φ n) z :=
    fun n z _ => (hφ n).differentiable (by norm_num) z
  have hderiv : ∀ n z, z ∈ Metric.closedBall (0 : E) D →
      ‖fderiv ℝ (φ n) z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ n) := by
    intro n z _
    simpa only [norm_iteratedFDeriv_one, Nat.add_sub_cancel] using hgrowth n z 1 (by omega)
  have hpop : ∀ n, ‖∫ z, φ n z ∂μ‖ ≤ featureGrowth C g q n *
      (1 + K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha)) := by
    intro n
    exact norm_coordinate_feature_integral_le μ id (φ n) (n + 1) (featureGrowth C g q n) _
      (featureGrowth_nonneg C g q hC n)
      (sourceMomentClass_succ_moment alpha K hK μ hμ n).1
      (sourceMomentClass_succ_moment alpha K hK μ hμ n).2 (hvalue n)
  have hZ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i, ‖Z s i‖ ≤ D := by
    intro s hs i
    exact particle_interpolation_norm_le (X i) (Y i) D s (hX i) (hY i) hs
  have hzdis : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i, ‖Z s i - Y i‖ ≤ ‖(X - Y) i‖ := by
    intro s hs i
    change ‖Y i + s • (X i - Y i) - Y i‖ ≤ ‖X i - Y i‖
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hs.2
  have hb : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ b s := fun s _ =>
    momentResidual_nonneg _ _ _ _
  have hbupper : ∀ s ∈ Icc (0 : ℝ) 1,
      b s ≤ featureDisplacementLambda c C g p q D L * (‖X - Y‖ / Real.sqrt N) + gamma Y := by
    intro s hs
    exact (feature_interpolated_momentResidual_le (fun i => X i) (fun i => Y i) φ
      (fun n => ∫ z, φ n z ∂μ) c C g p q K D alpha L s hN hc hC hp hq hK hD hs
      hX hY hdiff hderiv hvalue hpop).2
  have hcompare := fun (W : PiLp 2 fun _ : Fin N => E) (hW : ∀ i, ‖W i‖ ≤ D)
      (x y : E) (hx : ‖x‖ ≤ D) (hy : ‖y‖ ≤ D) =>
    source_empirical_population_field_bounds_by_residual c C g p q K D alpha C3 φ
      (sourceMomentClass alpha K) hc hC hp hq hK hD hφ hgrowth
      (sourceMomentClass_isProbabilityMeasure alpha K)
      (fun ν hν n => (sourceMomentClass_succ_moment alpha K hK ν hν n).1)
      (fun ν hν n => (sourceMomentClass_succ_moment alpha K hK ν hν n).2)
      G U hU hSU hG hthirdG L hL μ hμ W hW x y hx hy 0
  have hKm : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i j, ‖Ks s i j - Km s i j‖ ≤ b s / 2 := by
    intro s hs i j
    exact (hcompare (Z s) (hZ s hs) (Z s i) (Z s j) (hZ s hs i) (hZ s hs j)).2.2
  have hDm : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i, ‖Ds s i - Dm s i‖ ≤ b s / 2 := by
    intro s hs i
    exact (hcompare (Z s) (hZ s hs) (Z s i) (Z s i) (hZ s hs i) (hZ s hs i)).2.1
  have hKp : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i j,
      ‖Km s i j - Kr i j‖ ≤ (L : ℝ) * ‖(X - Y) i‖ + (L : ℝ) * ‖(X - Y) j‖ := by
    intro s hs i j
    have ht := (source_population_spatial_bounds c C g p q K D alpha C3 φ
      hc hC hp hq hK hD hφ hgrowth hthirdφ hgrowth₃ G U hU hSU hG hthirdG L hL μ hμ
      (Z s i) (Y i) (Z s j) (Y j) (hZ s hs i) (hY i) (hZ s hs j) (hY j)).2
    exact ht.trans (by
      rw [mul_add]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hzdis s hs i) L.coe_nonneg)
        (mul_le_mul_of_nonneg_left (hzdis s hs j) L.coe_nonneg))
  have hDp : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i, ‖Dm s i - Dr i‖ ≤ (L : ℝ) * ‖(X - Y) i‖ := by
    intro s hs i
    have ht := (source_population_spatial_bounds c C g p q K D alpha C3 φ
      hc hC hp hq hK hD hφ hgrowth hthirdφ hgrowth₃ G U hU hSU hG hthirdG L hL μ hμ
      (Z s i) (Y i) (Z s i) (Y i) (hZ s hs i) (hY i) (hZ s hs i) (hY i)).1
    exact ht.trans (mul_le_mul_of_nonneg_left (hzdis s hs i) L.coe_nonneg)
  have hquad := sampled_hessian_mismatch_bound (X - Y) Ds Dm Dr Ks Km Kr b
    L A_sp (featureDisplacementLambda c C g p q D L) (gamma Y) hN L.coe_nonneg
    hb hbupper hKm hDm hKp hDp hanti
  constructor
  · intro s hs
    exact (hquad.2 s hs).trans hquad.1
  · intro i
    exact (hcompare Y hY (Y i) (Y i) (hY i) (hY i)).1

/-- The actual source-model ODEs imply the manuscript positive-discrepancy
drift with exact c_D=Lambda+(2+A_sp)L. The source Jacobian, action integrability,
local block errors, and particle residual bound are conclusions of upstream
source theorems, not additional premises of this result. The supplied μ is
the population law at this time; no time derivative of μ is used. -/
theorem source_ode_discrepancy_deriv_le
    (X Y : ℝ → PiLp 2 fun _ : Fin N => E) (t : ℝ) (hN : 0 < N)
    (hXloc : ∀ i, ‖X t i‖ ≤ D) (hYloc : ∀ i, ‖Y t i‖ ≤ D) (A_sp : ℝ)
    (hanti : (N : ℝ)⁻¹ * ∑ i : Fin N, ‖(X t - Y t) i‖ ^ 3 ≤
      A_sp * (‖X t - Y t‖ / Real.sqrt N) ^ 3)
    (hXode : HasDerivAt X
      (empiricalConfigurationField (sourceWeightedFeatureMap c p φ)
        (momentGradientField (fderiv ℝ (sourceWeightedFeatureMap c p φ)) (gradient G)) (X t)) t)
    (hYode : HasDerivAt Y
      (frozenMomentConfigurationField
        (momentGradientField (fderiv ℝ (sourceWeightedFeatureMap c p φ)) (gradient G))
        (∫ z, sourceWeightedFeatureMap c p φ z ∂μ) (Y t)) t)
    (hpos : 0 < ‖X t - Y t‖ / Real.sqrt N) :
    let J := sourceWeightedFeatureMap c p φ
    let theta := ∫ z, J z ∂μ
    let Gamma := momentResidual (featureResidualWeight c p L)
      (fun n _ => finiteFeatureMean (fun i => φ n (Y t i))) (fun n _ => ∫ z, φ n z ∂μ) 0
    let r := ‖X t - Y t‖ / Real.sqrt N
    deriv (fun u => ‖X u - Y u‖ / Real.sqrt N) t ≤
      -rayleighInf (sampledMomentHessian J G theta (Y t)) * r +
        (featureDisplacementLambda c C g p q D L + (2 + A_sp) * (L : ℝ)) * r ^ 2 +
        Gamma * r + Gamma := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let J := sourceWeightedFeatureMap c p φ
  let V := empiricalConfigurationField (ι := Fin N) J
    (momentGradientField (fderiv ℝ J) (gradient G))
  let theta := ∫ z, J z ∂μ
  let w := frozenMomentConfigurationField (momentGradientField (fderiv ℝ J) (gradient G)) theta (Y t)
  let Gamma := momentResidual (featureResidualWeight c p L)
    (fun n _ => finiteFeatureMean (fun i => φ n (Y t i))) (fun n _ => ∫ z, φ n z ∂μ) 0
  have he := source_hessian_mismatch_and_residual c C g p q K D alpha C3 φ
    hc hC hp hq hK hD hφ hgrowth hthirdφ hgrowth₃ G U hU hSU hG hthirdG L hL μ hμ
    (X t) (Y t) hN hXloc hYloc A_sp hanti
  have hreg := source_empirical_segment_regularity c C g p q φ hc hC hp hq hφ hgrowth
    (sourceMomentClass alpha K) D G U hU hSU hG (X t) (Y t) hXloc hYloc
  exact ode_normalized_discrepancy_deriv_le X Y V w
    (fun s => empiricalMomentHessian J G (Y t + s • (X t - Y t)))
    (sampledMomentHessian J G theta (Y t)) N t
    (featureDisplacementLambda c C g p q D L + (2 + A_sp) * (L : ℝ)) Gamma
    hXode hYode hreg.1 hreg.2.2.1 he.1
    (normalized_particle_residual_le (V (Y t) - w) Gamma hN he.2) hpos

end PaperFormalization.Manuscript
