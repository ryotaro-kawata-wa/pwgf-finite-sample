import PaperFormalization.Manuscript.SourceODETraceBranch

/-! # Actual source ODEs on all branches of one schedule

The population law is the literal pushforward of one unchanged path law.
Its source-class membership is derived from the same closed population
representatives at each interior time. Actual ODEs, particle localization,
anti-spikiness, and one-sided particle traces give every scalar branch input.
No scalar drift inequality is a premise, and no jump recursion is asserted.
-/
open MeasureTheory Set Filter
open scoped NNReal BigOperators Topology
set_option maxSynthPendingDepth 8
namespace PaperFormalization.Manuscript
open Continuous
variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]
variable {N : ℕ}
variable {Ω : Type*} [MeasurableSpace Ω]

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


set_option maxHeartbeats 1600000 in
/-- A single consistent source population path law and actual ODE/trace inputs
give all closed pre-jump AC branches, the final AC branch (possibly empty),
and the literal full nonlinear drift on every open branch. -/
theorem source_ode_schedule_of_actual_paths
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : ℕ) (tau : ℕ → ℝ) (T A_sp : ℝ) (B : ℝ≥0) (hN : 0 < N)
    (htime : ∀ k < J, tau k < tau (k+1))
    (Z : Ω → ℝ → E) (Zbranch : ℕ → Ω → ℝ → E)
    (X Y : ℝ → PiLp 2 fun _ : Fin N => E)
    (preX preY : ℕ → PiLp 2 fun _ : Fin N => E)
    (hclass : ∀ k ≤ J, ∀ t ∈ uIcc (tau k) (if k < J then tau (k+1) else T),
      μ.map (fun ω => Zbranch k ω t) ∈ sourceMomentClass alpha K)
    (hZeq : ∀ k ≤ J, ∀ t ∈ Ioo (tau k) (if k < J then tau (k+1) else T),
      ∀ᵐ ω ∂μ, Zbranch k ω t = Z ω t)
    (hXlip : ∀ k < J, ∀ i, LipschitzOnWith B (fun t => X t i) (Ioo (tau k) (tau (k+1))))
    (hYlip : ∀ k < J, ∀ i, LipschitzOnWith B (fun t => Y t i) (Ioo (tau k) (tau (k+1))))
    (hXa : ∀ k < J, ∀ i, Tendsto (fun t => X t i) (𝓝[>] (tau k)) (𝓝 (X (tau k) i)))
    (hYa : ∀ k < J, ∀ i, Tendsto (fun t => Y t i) (𝓝[>] (tau k)) (𝓝 (Y (tau k) i)))
    (hXb : ∀ k < J, ∀ i, Tendsto (fun t => X t i) (𝓝[<] (tau (k+1))) (𝓝 (preX k i)))
    (hYb : ∀ k < J, ∀ i, Tendsto (fun t => Y t i) (𝓝[<] (tau (k+1))) (𝓝 (preY k i)))
    (hXfinal : ∀ i, LipschitzOnWith B (fun t => X t i) (uIcc (tau J) T))
    (hYfinal : ∀ i, LipschitzOnWith B (fun t => Y t i) (uIcc (tau J) T))
    (hgood : ∀ k ≤ J, ∀ᵐ t ∂volume.restrict (Ioo (tau k) (if k < J then tau (k+1) else T)),
      (∀ i, ‖X t i‖ ≤ D) ∧ (∀ i, ‖Y t i‖ ≤ D) ∧
      (N : ℝ)⁻¹ * ∑ i : Fin N, ‖(X t - Y t) i‖ ^ 3 ≤
        A_sp * (‖X t - Y t‖ / Real.sqrt N) ^ 3 ∧
      HasDerivAt X
        (empiricalConfigurationField (sourceWeightedFeatureMap c p φ)
          (momentGradientField (fderiv ℝ (sourceWeightedFeatureMap c p φ)) (gradient G)) (X t)) t ∧
      HasDerivAt Y
        (frozenMomentConfigurationField
          (momentGradientField (fderiv ℝ (sourceWeightedFeatureMap c p φ)) (gradient G))
          (∫ z, sourceWeightedFeatureMap c p φ z ∂(μ.map (fun ω => Z ω t))) (Y t)) t) :
    let F := sourceWeightedFeatureMap c p φ
    let r := fun t => ‖X t - Y t‖ / Real.sqrt N
    let pre := fun k => ‖preX k - preY k‖ / Real.sqrt N
    let kappa := fun t => rayleighInf (sampledMomentHessian F G
      (∫ z, F z ∂(μ.map (fun ω => Z ω t))) (Y t))
    let Gamma := momentResidual (featureResidualWeight c p L)
      (fun n t => finiteFeatureMean (fun i => φ n (Y t i)))
      (fun n t => ∫ z, φ n z ∂(μ.map (fun ω => Z ω t)))
    (∀ k < J, AbsolutelyContinuousOnInterval (closedBranch r (tau (k+1)) (pre k))
      (tau k) (tau (k+1)) ∧ Tendsto r (𝓝[<] (tau (k+1))) (𝓝 (pre k))) ∧
    AbsolutelyContinuousOnInterval r (tau J) T ∧
    ∀ k ≤ J, ∀ᵐ t ∂volume.restrict (Ioo (tau k) (if k < J then tau (k+1) else T)),
      deriv r t ≤ -kappa t * r t +
        (featureDisplacementLambda c C g p q D L + (2+A_sp)*(L : ℝ)) * (r t)^2 +
          Gamma t*r t+Gamma t := by
  let pop := fun t => μ.map (fun ω => Z ω t)
  have hpop k (hk : k ≤ J) t (ht : t ∈ Ioo (tau k) (if k < J then tau (k+1) else T)) :
      pop t ∈ sourceMomentClass alpha K := by
    have hb := hclass k hk t (Icc_subset_uIcc ⟨ht.1.le,ht.2.le⟩)
    rwa [Measure.map_congr (hZeq k hk t ht)] at hb
  have hfull k (hk : k ≤ J) : ∀ᵐ t ∂volume.restrict (Ioo (tau k) (if k < J then tau (k+1) else T)),
      pop t ∈ sourceMomentClass alpha K ∧
      (∀ i, ‖X t i‖ ≤ D) ∧ (∀ i, ‖Y t i‖ ≤ D) ∧
      (N : ℝ)⁻¹ * ∑ i : Fin N, ‖(X t - Y t) i‖ ^ 3 ≤
        A_sp * (‖X t - Y t‖ / Real.sqrt N) ^ 3 ∧
      HasDerivAt X
        (empiricalConfigurationField (sourceWeightedFeatureMap c p φ)
          (momentGradientField (fderiv ℝ (sourceWeightedFeatureMap c p φ)) (gradient G)) (X t)) t ∧
      HasDerivAt Y
        (frozenMomentConfigurationField
          (momentGradientField (fderiv ℝ (sourceWeightedFeatureMap c p φ)) (gradient G))
          (∫ z, sourceWeightedFeatureMap c p φ z ∂(pop t)) (Y t)) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,hgood k hk] with t ht hmodel
    exact ⟨hpop k hk t ht,hmodel⟩
  have hbranches k (hk : k < J) := source_ode_branch_of_actual_traces c C g p q K D alpha C3 φ
    hc hC hp hq hK hD hφ hgrowth hthirdφ hgrowth₃ G U hU hSU hG hthirdG L hL
    pop X Y (preX k) (preY k) (tau k) (tau (k+1)) A_sp B hN (htime k hk)
    (hXlip k hk) (hYlip k hk) (hXa k hk) (hYa k hk) (hXb k hk) (hYb k hk)
    (by simpa only [if_pos hk] using hfull k hk.le)
  have hfinal := source_ode_closed_branch c C g p q K D alpha C3 φ
    hc hC hp hq hK hD hφ hgrowth hthirdφ hgrowth₃ G U hU hSU hG hthirdG L hL
    pop X Y (tau J) T A_sp B hN hXfinal hYfinal
    (by simpa only [lt_self_iff_false, ↓reduceIte, restrict_Ioo_eq_restrict_Icc] using hfull J le_rfl)
  refine ⟨fun k hk => ⟨(hbranches k hk).1,(hbranches k hk).2.1⟩,hfinal.1,?_⟩
  intro k hk
  by_cases hkJ : k < J
  · simpa only [if_pos hkJ] using (hbranches k hkJ).2.2.2
  · have hkEq : k = J := by omega
    subst k
    simpa only [lt_self_iff_false, ↓reduceIte, restrict_Ioo_eq_restrict_Icc] using hfinal.2.2
end PaperFormalization.Manuscript
