import PaperFormalization.Manuscript.SourceODEBranch

/-! # Continuous-branch inputs from an actual fixed reference path law

The population law at time t is the pushforward of one fixed probability
measure by evaluation of its supplied reference paths. Genuine source moment
bounds and one common AE path-Lipschitz event give the literal Gamma and
full sampled-Hessian curvature regularity. The source ODEs are required on
one common AE time event; the scalar drift also covers zero discrepancy.
No conditional-law identification or cross-jump endpoint extension is claimed.
-/

open MeasureTheory Set Filter
open scoped NNReal BigOperators

set_option maxSynthPendingDepth 8

namespace PaperFormalization.Manuscript

open Continuous

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

include hc hC hp hq hK hD hφ hgrowth hthirdφ hgrowth₃ hU hSU hG hthirdG hL

variable {Ω : Type*} [MeasurableSpace Ω]

/-- All continuous-branch analytic inputs for the actual source model, with
Gamma and curvature constructed from the same fixed population path law.
The coefficient is exactly Lambda + (2 + A_sp)L and the curvature uses the
full population-sampled Hessian, including its 1/N integral block. -/
theorem source_fixedLaw_continuous_branch [Nontrivial E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ → E)
    (X Y : ℝ → PiLp 2 fun _ : Fin N => E)
    (a b A_sp : ℝ) (B : ℝ≥0) (hN : 0 < N) (halpha : 0 < alpha)
    (hZ : ∀ t ∈ uIcc a b, AEStronglyMeasurable (fun ω => Z ω t) μ)
    (hclass : ∀ t ∈ uIcc a b, μ.map (fun ω => Z ω t) ∈ sourceMomentClass alpha K)
    (hpath : ∀ᵐ ω ∂μ, LipschitzOnWith B (Z ω) (uIcc a b))
    (hXlip : ∀ i, LipschitzOnWith B (fun t => X t i) (uIcc a b))
    (hYlip : ∀ i, LipschitzOnWith B (fun t => Y t i) (uIcc a b))
    (hYloc : ∀ i t, t ∈ uIcc a b → ‖Y t i‖ ≤ D)
    (hgood : ∀ᵐ t ∂volume.restrict (Icc a b),
      (∀ i, ‖X t i‖ ≤ D) ∧
      (N : ℝ)⁻¹ * ∑ i : Fin N, ‖(X t - Y t) i‖ ^ 3 ≤
        A_sp * (‖X t - Y t‖ / Real.sqrt N) ^ 3 ∧
      HasDerivAt X
        (empiricalConfigurationField (sourceWeightedFeatureMap c p φ)
          (momentGradientField (fderiv ℝ (sourceWeightedFeatureMap c p φ)) (gradient G)) (X t)) t ∧
      HasDerivAt Y
        (frozenMomentConfigurationField
          (momentGradientField (fderiv ℝ (sourceWeightedFeatureMap c p φ)) (gradient G))
          (∫ ω, sourceWeightedFeatureMap c p φ (Z ω t) ∂μ) (Y t)) t) :
    let J := sourceWeightedFeatureMap c p φ
    let r := fun t => ‖X t - Y t‖ / Real.sqrt N
    let kappa := fun t => rayleighInf (sampledMomentHessian J G
      (∫ ω, J (Z ω t) ∂μ) (Y t))
    let Gamma := momentResidual (featureResidualWeight c p L)
      (fun n t => finiteFeatureMean (fun i => φ n (Y t i)))
      (fun n t => ∫ ω, φ n (Z ω t) ∂μ)
    AbsolutelyContinuousOnInterval r a b ∧
      AbsolutelyContinuousOnInterval Gamma a b ∧ IntervalIntegrable Gamma volume a b ∧
      ContinuousOn kappa (uIcc a b) ∧ IntervalIntegrable kappa volume a b ∧
      (∀ t, 0 ≤ Gamma t) ∧
      ∀ᵐ t ∂volume.restrict (Icc a b),
        deriv r t ≤ -kappa t * r t +
          (featureDisplacementLambda c C g p q D L + (2 + A_sp) * (L : ℝ)) * (r t) ^ 2 +
          Gamma t * r t + Gamma t := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let J := sourceWeightedFeatureMap c p φ
  have hJ : ContDiff ℝ 2 J :=
    contDiff_sourceWeightedFeatureMap c C g p q φ hc hC hp hq hφ hgrowth
  have hm : ∀ t ∈ uIcc a b,
      (∫ z, J z ∂(μ.map (fun ω => Z ω t))) = ∫ ω, J (Z ω t) ∂μ := by
    intro t ht
    exact coordinate_feature_integral_map μ (fun ω => Z ω t) J (hZ t ht).aemeasurable hJ.continuous
  have hbranch := source_ode_closed_branch c C g p q K D alpha C3 φ
    hc hC hp hq hK hD hφ hgrowth hthirdφ hgrowth₃ G U hU hSU hG hthirdG L hL
    (fun t => μ.map (fun ω => Z ω t)) X Y a b A_sp B hN hXlip hYlip (by
      filter_upwards [hgood, ae_restrict_mem measurableSet_Icc] with t ht hti
      have htu : t ∈ uIcc a b := Icc_subset_uIcc hti
      refine ⟨hclass t htu, ht.1, fun i => hYloc i t htu, ht.2.1, ht.2.2.1, ?_⟩
      change HasDerivAt Y (frozenMomentConfigurationField
        (momentGradientField (fderiv ℝ J) (gradient G))
        (∫ z, J z ∂(μ.map (fun ω => Z ω t))) (Y t)) t
      rw [hm t htu]
      exact ht.2.2.2)
  have hGamma := source_momentResidual_branch_regularity μ Z (fun i t => Y t i)
    φ c C g p q K D alpha L B a b hc hC hp hq hK hD halpha
    (fun n => (hφ n).of_le (by norm_num))
    (fun n z k hk => hgrowth n z k (by omega)) hZ hclass hpath hYlip hYloc
  have hkappa := source_curvature_branch_regularity μ Z φ c C g p q K D alpha B
    hc hC hp hq hK halpha hφ hgrowth G U hU hSU hG a b hZ hclass hpath
    Y (fun i => (hYlip i).continuousOn)
  refine ⟨hbranch.1, hGamma.1, hGamma.2, hkappa.2.1, hkappa.2.2,
    fun t => momentResidual_nonneg _ _ _ t, ?_⟩
  filter_upwards [hbranch.2.2, ae_restrict_mem measurableSet_Icc] with t ht hti
  have htu : t ∈ uIcc a b := Icc_subset_uIcc hti
  have hcoordinate : ∀ n, (∫ z, φ n z ∂(μ.map (fun ω => Z ω t))) =
      ∫ ω, φ n (Z ω t) ∂μ := by
    intro n
    exact coordinate_feature_integral_map μ (fun ω => Z ω t) (φ n)
      (hZ t htu).aemeasurable (hφ n).continuous
  dsimp only [J] at hm
  simp only [hm t htu, momentResidual, momentResidualTerm, hcoordinate] at ht ⊢
  exact ht

end PaperFormalization.Manuscript
