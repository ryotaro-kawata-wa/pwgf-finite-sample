import PaperFormalization.Manuscript.FeatureDisplacement
import PaperFormalization.Manuscript.EmpiricalWeightedMoment
import PaperFormalization.Manuscript.HilbertMomentResidual
import PaperFormalization.Manuscript.MeasureRegionObjective
import PaperFormalization.Manuscript.SourceFeatureRadius
import PaperFormalization.Manuscript.SourceMomentClass

/-! # Actual empirical kernel differences with the original source constants

The paired coordinate means and summable literal weights first control the
actual scaled Hilbert moment difference. Both empirical configurations lie
in the original measure-generated region through bounded-support membership;
neither empirical law is required to belong to the population moment class.
The kernel comparison has no anti-spikiness or dimension assumption.
-/

open MeasureTheory Set
open scoped BigOperators NNReal
set_option maxSynthPendingDepth 8

namespace PaperFormalization.Manuscript

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]
variable {N : ℕ}

omit [CompleteSpace E] in
/-- Paired localized empirical moments have their actual Hilbert difference
bounded by the literal source Lambda times RMS displacement. Summability is
derived, and the local factor L is never divided out (so L=0 is included). -/
theorem source_scaled_empiricalMoment_sub_le
    (c C g p q D : ℝ) (φ : ∀ n, E → H n) (L : ℝ≥0)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hD : 1 ≤ D)
    (hφ : ∀ n, ContDiff ℝ 1 (φ n))
    (hgrowth : ∀ n z k, k ≤ 1 → ‖iteratedFDeriv ℝ k (φ n) z‖ ≤
      featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1 - k)))
    (X Y : PiLp 2 fun _ : Fin N => E) (hN : 0 < N)
    (hX : ∀ i, ‖X i‖ ≤ D) (hY : ∀ i, ‖Y i‖ ≤ D) :
    (L : ℝ) * ‖empiricalMomentMap (sourceWeightedFeatureMap c p φ) X -
      empiricalMomentMap (sourceWeightedFeatureMap c p φ) Y‖ ≤
      featureDisplacementLambda c C g p q D L * (‖X - Y‖ / Real.sqrt N) := by
  let r := ‖X - Y‖ / Real.sqrt N
  let Ex := fun n (_ : ℝ) => finiteFeatureMean (fun i => φ n (X i))
  let Ey := fun n (_ : ℝ) => finiteFeatureMean (fun i => φ n (Y i))
  have hvalue : ∀ n z, ‖φ n z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1)) := by
    intro n z
    simpa only [norm_iteratedFDeriv_zero, Nat.sub_zero] using hgrowth n z 0 (by omega)
  have hderiv : ∀ n z, ‖fderiv ℝ (φ n) z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ n) := by
    intro n z
    simpa only [norm_iteratedFDeriv_one, Nat.add_sub_cancel] using hgrowth n z 1 (by omega)
  have hcoord : ∀ n, ‖Ex n 0 - Ey n 0‖ ≤ featureGrowth C g q n * (1 + 2 * D ^ n) * r := by
    intro n
    apply norm_finiteFeatureMean_sub_le_of_paired_bound
      (fun i => φ n (X i)) (fun i => φ n (Y i)) (fun i => X i - Y i)
      (featureGrowth C g q n * (1 + 2 * D ^ n)) hN (by
        exact mul_nonneg (featureGrowth_nonneg C g q hC n) (by positivity))
    intro i
    exact localized_feature_sub_le (φ n) D (featureGrowth C g q n) n
      (by linarith) (featureGrowth_nonneg C g q hC n)
      (fun z _ => (hφ n).differentiable (by norm_num) z)
      (fun z _ => hderiv n z) (X i) (Y i) (hX i) (hY i)
  have hsum := (summable_featureDisplacement c C g p q D L hc hC hp hq hD).mul_right r
  have ht : ∀ n, momentResidualTerm (featureResidualWeight c p L) Ex Ey n 0 ≤
      ((featureResidualWeight c p L n : ℝ) * (featureGrowth C g q n * (1 + 2 * D ^ n))) * r := by
    intro n
    exact (mul_le_mul_of_nonneg_left (hcoord n) (featureResidualWeight c p L n).coe_nonneg).trans_eq
      (by ring)
  have hres := hsum.of_nonneg_of_le
    (fun n => momentResidualTerm_nonneg (featureResidualWeight c p L) Ex Ey n 0) ht
  have hh := scaled_moment_difference_le_residual c p L Ex Ey 0
    (empiricalMomentMap (sourceWeightedFeatureMap c p φ) X)
    (empiricalMomentMap (sourceWeightedFeatureMap c p φ) Y)
    (empirical_sourceWeightedFeatureMap_apply c C g p q φ hc hC hp hq hvalue X)
    (empirical_sourceWeightedFeatureMap_apply c C g p q φ hc hC hp hq hvalue Y) hres
  have hbound := hres.tsum_le_tsum ht hsum
  rw [tsum_mul_right] at hbound
  exact hh.trans hbound

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The actual kernel blocks of two localized empirical configurations obey
the source Step-2 bound. Both moments enter the unchanged measure region via
bounded-support empirical laws, not via population-class membership. Only
feature C2 is used; no third feature derivative or anti-spikiness is needed. -/
theorem source_empirical_kernel_difference_le
    (c C g p q K D alpha C3 : ℝ) (φ : ∀ n, E → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (hD : 1 ≤ D)
    (hφ : ∀ n, ContDiff ℝ 2 (φ n))
    (hgrowth : ∀ n z k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) z‖ ≤
      featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1 - k)))
    (G : lp H 2 → ℝ) (U : Set (lp H 2)) (hU : IsOpen U)
    (hSU : measureMomentRegion (sourceWeightedFeatureMap c p φ) (sourceMomentClass alpha K) D ⊆ U)
    (hG : ContDiffOn ℝ 3 G U)
    (hthirdG : ∀ theta ∈ measureMomentRegion (sourceWeightedFeatureMap c p φ)
      (sourceMomentClass alpha K) D, ‖iteratedFDeriv ℝ 3 G theta‖ ≤ C3)
    (L : ℝ≥0) (hL : (L : ℝ) = sourceComparisonEnvelope c C g p q K D alpha C3 φ G)
    (X Y : PiLp 2 fun _ : Fin N => E) (hN : 0 < N)
    (hX : ∀ i, ‖X i‖ ≤ D) (hY : ∀ i, ‖Y i‖ ≤ D) (i j : Fin N) :
    let J := sourceWeightedFeatureMap c p φ
    ‖momentIntegralHessian (fderiv ℝ J (X i)) (fderiv ℝ J (X j))
        (momentObjectiveHessian G (empiricalMomentMap J X)) -
      momentIntegralHessian (fderiv ℝ J (Y i)) (fderiv ℝ J (Y j))
        (momentObjectiveHessian G (empiricalMomentMap J Y))‖ ≤
      featureDisplacementLambda c C g p q D L * (‖X - Y‖ / Real.sqrt N) +
        (L : ℝ) * (‖X i - Y i‖ + ‖X j - Y j‖) := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let J := sourceWeightedFeatureMap c p φ
  let thetaX := empiricalMomentMap J X
  let thetaY := empiricalMomentMap J Y
  let Q := sourceObjectiveAnchorFactor c p C3 φ G
  let R := sourceMomentRadius c C g p q K D alpha
  have hvalue : ∀ n z, ‖φ n z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1)) := by
    intro n z
    simpa only [norm_iteratedFDeriv_zero, Nat.sub_zero] using hgrowth n z 0 (by omega)
  have hthetaX : thetaX ∈ measureMomentRegion J (sourceMomentClass alpha K) D :=
    empiricalMomentMap_mem_measureMomentRegion J (sourceMomentClass alpha K) D X hX
  have hthetaY : thetaY ∈ measureMomentRegion J (sourceMomentClass alpha K) D :=
    empiricalMomentMap_mem_measureMomentRegion J (sourceMomentClass alpha K) D Y hY
  have hb := source_measure_region_objective_bounds c C g p q K D alpha C3 φ
    (sourceMomentClass alpha K) hc hC hp hq hK hD (fun n => (hφ n).continuous)
    (sourceMomentClass_isProbabilityMeasure alpha K)
    (fun ν hν n => (sourceMomentClass_succ_moment alpha K hK ν hν n).1)
    (fun ν hν n => (sourceMomentClass_succ_moment alpha K hK ν hν n).2)
    hvalue G U hU hSU hG hthirdG
  have hd := source_measure_region_objective_differences c C g p q K D alpha C3 φ
    (sourceMomentClass alpha K) hc hC hp hq hK hD (fun n => (hφ n).continuous)
    (sourceMomentClass_isProbabilityMeasure alpha K)
    (fun ν hν n => (sourceMomentClass_succ_moment alpha K hK ν hν n).1)
    (fun ν hν n => (sourceMomentClass_succ_moment alpha K hK ν hν n).2)
    hvalue G U hU hSU hG hthirdG thetaX thetaY hthetaX hthetaY
  have hR : 1 ≤ R := one_le_sourceMomentRadius c C g p q K D alpha hC hK.le (by linarith)
  have hQ : 1 ≤ Q := hb.1
  have hQ0 : 0 ≤ Q := by linarith
  have hR0 : 0 ≤ R := by linarith
  have hXi := source_feature_norms_le_radius c C g p q K D alpha φ
    hc hC hp hq hK hD hφ hgrowth (X i) (hX i)
  have hXj := source_feature_norms_le_radius c C g p q K D alpha φ
    hc hC hp hq hK hD hφ hgrowth (X j) (hX j)
  have hYi := source_feature_norms_le_radius c C g p q K D alpha φ
    hc hC hp hq hK hD hφ hgrowth (Y i) (hY i)
  have hm := (source_moment_measure_bounds (fderiv ℝ J) (gradient G) thetaX thetaY
    (X i) (X j) (fderiv ℝ (fderiv ℝ J) (X i))
    (momentObjectiveHessian G thetaX) (momentObjectiveHessian G thetaY)
    Q R ‖thetaX - thetaY‖ hQ hR hXi.2.1 hXj.2.1 hXi.2.2 le_rfl hd.1 hd.2).2.2
  have hscaled : (L : ℝ) * ‖thetaX - thetaY‖ ≤
      featureDisplacementLambda c C g p q D L * (‖X - Y‖ / Real.sqrt N) :=
    source_scaled_empiricalMoment_sub_le c C g p q D φ L hc hC hp hq hD
      (fun n => (hφ n).of_le (by norm_num))
      (fun n z k hk => hgrowth n z k (by omega)) X Y hN hX hY
  have hLQR : (L : ℝ) = 4 * Q * R ^ 3 := hL
  have hmeasure : ‖momentIntegralHessian (fderiv ℝ J (X i)) (fderiv ℝ J (X j))
        (momentObjectiveHessian G thetaX) -
      momentIntegralHessian (fderiv ℝ J (X i)) (fderiv ℝ J (X j))
        (momentObjectiveHessian G thetaY)‖ ≤
      featureDisplacementLambda c C g p q D L * (‖X - Y‖ / Real.sqrt N) := by
    rw [← hLQR] at hm
    nlinarith [mul_nonneg L.coe_nonneg (norm_nonneg (thetaX - thetaY))]
  have hdi : ‖fderiv ℝ J (X i) - fderiv ℝ J (Y i)‖ ≤ R * ‖X i - Y i‖ :=
    source_feature_fderiv_sub_le_radius c C g p q K D alpha φ
      hc hC hp hq hK hD hφ hgrowth (X i) (Y i) (hX i) (hY i)
  have hdj : ‖fderiv ℝ J (X j) - fderiv ℝ J (Y j)‖ ≤ R * ‖X j - Y j‖ :=
    source_feature_fderiv_sub_le_radius c C g p q K D alpha φ
      hc hC hp hq hK hD hφ hgrowth (X j) (Y j) (hX j) (hY j)
  have hBY : ‖momentObjectiveHessian G thetaY‖ ≤ Q * R := (hb.2 thetaY hthetaY).2
  have hspatial : ‖momentIntegralHessian (fderiv ℝ J (X i)) (fderiv ℝ J (X j))
        (momentObjectiveHessian G thetaY) -
      momentIntegralHessian (fderiv ℝ J (Y i)) (fderiv ℝ J (Y j))
        (momentObjectiveHessian G thetaY)‖ ≤ (L : ℝ) * (‖X i - Y i‖ + ‖X j - Y j‖) := by
    calc
      _ ≤ ‖fderiv ℝ J (X i) - fderiv ℝ J (Y i)‖ * ‖momentObjectiveHessian G thetaY‖ *
          ‖fderiv ℝ J (X j)‖ + ‖fderiv ℝ J (Y i)‖ * ‖momentObjectiveHessian G thetaY‖ *
          ‖fderiv ℝ J (X j) - fderiv ℝ J (Y j)‖ :=
        norm_momentIntegralHessian_sub_spatial_le _ _ _ _ _
      _ ≤ (R * ‖X i - Y i‖) * (Q * R) * R + R * (Q * R) * (R * ‖X j - Y j‖) := by
        gcongr
        · exact hXj.2.1
        · exact hYi.2.1
      _ = (Q * R ^ 3) * (‖X i - Y i‖ + ‖X j - Y j‖) := by ring
      _ ≤ _ := by
        rw [hLQR]
        exact mul_le_mul_of_nonneg_right (local_moment_constant_domination Q R hQ0 hR).2
          (add_nonneg (norm_nonneg _) (norm_nonneg _))
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hmeasure hspatial)

end PaperFormalization.Manuscript
