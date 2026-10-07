import PaperFormalization.Manuscript.SourceODESchedule
import PaperFormalization.Manuscript.SourceScheduleMarginals
import PaperFormalization.Manuscript.SourceGammaTraceTransfer
import PaperFormalization.Manuscript.SourceJumpTraceRecursion
import PaperFormalization.Manuscript.SourceObservedJumpSchedule

/-! # Primitive actual-path inputs for deterministic source tracking

This record contains particle/population paths, their actual branch and trace
identities, and the original ODE model. The theorem consumes independently
proved residual-event conditions and actual observed jump-event exclusions.
It derives the scalar AC, integrability, drift and jump inputs; none are record
fields. The stochastic construction and observation-law identifications remain
explicit in the existing observed-view records.
-/
open Matrix MeasureTheory Set Filter
open scoped BigOperators NNReal Topology Matrix.Norms.Frobenius
set_option maxSynthPendingDepth 8
namespace PaperFormalization.Manuscript
open Continuous
variable {Ω : Type*} [MeasurableSpace Ω] {N d : ℕ}
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

/-- Actual model paths and trace identities, with no scalar comparison premise. -/
structure SourceTrackingPaths (μ : Measure Ω) (J : ℕ) (tau : ℕ → ℝ) (T : ℝ)
    (B : ℝ≥0) (c p K D alpha A_sp : ℝ)
    (φ : ∀ n, EuclideanSpace ℝ (Fin d) → H n) (G : lp H 2 → ℝ) where
  Z : Ω → ℝ → EuclideanSpace ℝ (Fin d)
  Zbranch : ℕ → Ω → ℝ → EuclideanSpace ℝ (Fin d)
  X : ℝ → PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d)
  Y : ℝ → PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d)
  Ybranch : ℕ → ℝ → PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d)
  preX : ℕ → PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d)
  preY : ℕ → PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d)
  population_class : ∀ k ≤ J, ∀ t ∈ uIcc (tau k) (if k < J then tau (k+1) else T),
    μ.map (fun ω => Zbranch k ω t) ∈ sourceMomentClass alpha K
  population_lip : ∀ k ≤ J, ∀ᵐ ω ∂μ,
    LipschitzOnWith B (Zbranch k ω) (uIcc (tau k) (if k < J then tau (k+1) else T))
  representative_lip : ∀ k ≤ J, ∀ i, LipschitzOnWith B (fun t => Ybranch k t i)
    (uIcc (tau k) (if k < J then tau (k+1) else T))
  representative_local : ∀ k ≤ J, ∀ i t, t ∈ uIcc (tau k) (if k < J then tau (k+1) else T) →
    ‖Ybranch k t i‖ ≤ D
  population_right_identity : ∀ k ≤ J, ∀ t ∈ Icc (tau k) (if k < J then tau (k+1) else T),
    (k < J → t < tau (k+1)) → ∀ᵐ ω ∂μ, Zbranch k ω t = Z ω t
  particle_right_identity : ∀ k ≤ J, ∀ t ∈ Icc (tau k) (if k < J then tau (k+1) else T),
    (k < J → t < tau (k+1)) → Ybranch k t = Y t
  particle_pre_identity : ∀ k < J, Ybranch k (tau (k+1)) = preY k
  preX_local : ∀ k < J, ∀ i, ‖preX k i‖ ≤ D
  X_lip : ∀ k < J, ∀ i, LipschitzOnWith B (fun t => X t i) (Ioo (tau k) (tau (k+1)))
  Y_lip : ∀ k < J, ∀ i, LipschitzOnWith B (fun t => Y t i) (Ioo (tau k) (tau (k+1)))
  X_right : ∀ k < J, ∀ i, Tendsto (fun t => X t i) (𝓝[>] (tau k)) (𝓝 (X (tau k) i))
  Y_right : ∀ k < J, ∀ i, Tendsto (fun t => Y t i) (𝓝[>] (tau k)) (𝓝 (Y (tau k) i))
  X_pre : ∀ k < J, ∀ i, Tendsto (fun t => X t i) (𝓝[<] (tau (k+1))) (𝓝 (preX k i))
  Y_pre : ∀ k < J, ∀ i, Tendsto (fun t => Y t i) (𝓝[<] (tau (k+1))) (𝓝 (preY k i))
  X_final_lip : ∀ i, LipschitzOnWith B (fun t => X t i) (uIcc (tau J) T)
  Y_final_lip : ∀ i, LipschitzOnWith B (fun t => Y t i) (uIcc (tau J) T)
  initial_match : X 0 = Y 0
  model_ode : ∀ k ≤ J, ∀ᵐ t ∂volume.restrict (Ioo (tau k) (if k < J then tau (k+1) else T)),
    (∀ i, ‖X t i‖ ≤ D) ∧ (∀ i, ‖Y t i‖ ≤ D) ∧
    (N : ℝ)⁻¹ * ∑ i : Fin N, ‖(X t-Y t) i‖^3 ≤ A_sp*(‖X t-Y t‖/Real.sqrt N)^3 ∧
    HasDerivAt X (empiricalConfigurationField (sourceWeightedFeatureMap c p φ)
      (momentGradientField (fderiv ℝ (sourceWeightedFeatureMap c p φ)) (gradient G)) (X t)) t ∧
    HasDerivAt Y (frozenMomentConfigurationField
      (momentGradientField (fderiv ℝ (sourceWeightedFeatureMap c p φ)) (gradient G))
      (∫ z, sourceWeightedFeatureMap c p φ z ∂(μ.map (fun ω => Z ω t))) (Y t)) t

variable (c C g p q K D alpha C3 : ℝ) (φ : ∀ n, EuclideanSpace ℝ (Fin d) → H n)
  (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (hD : 1 ≤ D)
  (halpha : 0 < alpha) (hφ : ∀ n, ContDiff ℝ 2 (φ n))
  (hgrowth : ∀ n z k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) z‖ ≤
    featureGrowth C g q n*(1+‖z‖^(n+1-k)))
  (hthirdφ : ∀ n z, DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ (φ n))) z)
  (hgrowth₃ : ∀ n z, ‖iteratedFDeriv ℝ 3 (φ n) z‖ ≤ featureGrowth C g q n*(1+‖z‖^(n+1-3)))
  (G : lp H 2 → ℝ) (U : Set (lp H 2)) (hU : IsOpen U)
  (hSU : measureMomentRegion (sourceWeightedFeatureMap c p φ) (sourceMomentClass alpha K) D ⊆ U)
  (hG : ContDiffOn ℝ 3 G U)
  (hthirdG : ∀ theta ∈ measureMomentRegion (sourceWeightedFeatureMap c p φ)
    (sourceMomentClass alpha K) D, ‖iteratedFDeriv ℝ 3 G theta‖ ≤ C3)
  (L : ℝ≥0) (hL : (L : ℝ) = sourceComparisonEnvelope c C g p q K D alpha C3 φ G)

include hc hC hp hq hK hD halpha hφ hgrowth hthirdφ hgrowth₃ hthirdG hL

set_option maxHeartbeats 2000000 in
/-- All deterministic comparison inputs follow from primitive actual model
paths and the independently derived residual and observed jump events. The
pre-law is the actual terminal representative marginal, separate from the
post-jump law. No scalar AC, drift or jump inequality is assumed. -/
theorem actual_source_tracking_inputs
    (μ : Measure Ω) [IsProbabilityMeasure μ] (J : ℕ) (tau eta : ℕ → ℝ) (T A_sp : ℝ)
    (B : ℝ≥0) (hN : 0 < N) (htau0 : tau 0 = 0)
    (htime : ∀ k < J, tau k < tau (k+1)) (hT : tau J ≤ T)
    (P : SourceTrackingPaths (N := N) μ J tau T B c p K D alpha A_sp φ G)
    (delta deltaTilde pTotal : ℝ)
    (hGammaLabels : ∀ k ≤ J, ∀ t ∈ Icc (tau k) (if k < J then tau (k+1) else T),
      weightedSampleResidual (featureResidualWeight c p L) φ
        (fun n => ∫ ω, φ n (P.Zbranch k ω t) ∂μ) (fun i => P.Ybranch k t i) ≤ delta)
    (hCovPre : ∀ k < J,
      let F := sourceWeightedFeatureMap c p φ
      let muPre := μ.map (fun ω => P.Zbranch k ω (tau (k+1)))
      matrixNuclearValue (populationCovarianceResidual muPre (fun i => P.preY k i)
        (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix F G
          (∫ z, F z ∂muPre) (P.preY k i) z))) / N ≤ deltaTilde)
    {O : Type*} [MeasurableSpace O] (ν : Measure O)
    (S V : Fin J → Type*) [∀ j, MeasurableSpace (S j)] [∀ j, MeasurableSpace (V j)]
    (view : ∀ j, SourceObservedJumpView c p K D alpha φ G U hU hSU
      (hG.of_le (by norm_num)) hN ν (S j) (V j)) (ω : O)
    (hJumpGood : ∀ j, (view j).observation ω ∉ actualSourceJumpFailure c C g p q D φ G L
      (view j).PopGood (fun h => (view j).κ h) (view j).X (view j).Y
      (view j).Xpost (view j).Ypost (view j).eta (pTotal/(8*((J : ℝ)+1))))
    (hPopGood : ∀ j, ((view j).observation ω).1 ∈ (view j).PopGood)
    (hPreX : ∀ j, (view j).X ((view j).observation ω).1 = P.preX j)
    (hPreY : ∀ j, (view j).Y ((view j).observation ω).1 = P.preY j)
    (hPostX : ∀ j, (view j).Xpost ((view j).observation ω).1 ((view j).observation ω).2 = P.X (tau (j+1)))
    (hPostY : ∀ j, (view j).Ypost ((view j).observation ω).1 ((view j).observation ω).2 = P.Y (tau (j+1)))
    (hPreLaw : ∀ j, (view j).κ ((view j).observation ω).1 =
      μ.map (fun ω => P.Zbranch j ω (tau (j+1))))
    (hEta : ∀ j, (view j).eta = eta j) :
    let F := sourceWeightedFeatureMap c p φ
    let r := fun t => ‖P.X t-P.Y t‖/Real.sqrt N
    let pre := fun k => ‖P.preX k-P.preY k‖/Real.sqrt N
    let kappa := fun t => rayleighInf (sampledMomentHessian F G
      (∫ z, F z ∂(μ.map (fun ω => P.Z ω t))) (P.Y t))
    let Gamma := momentResidual (featureResidualWeight c p L)
      (fun n t => finiteFeatureMean (fun i => φ n (P.Y t i)))
      (fun n t => ∫ z, φ n z ∂(μ.map (fun ω => P.Z ω t)))
    let muPre := fun k => μ.map (fun ω => P.Zbranch k ω (tau (k+1)))
    let GammaPre := fun k => momentResidual (featureResidualWeight c p L)
      (fun n _ => finiteFeatureMean (fun i => φ n (P.preY k i))) (fun n _ => ∫ z, φ n z ∂muPre k) 0
    let GammaTildePre := fun k => matrixNuclearValue (populationCovarianceResidual (muPre k) (fun i => P.preY k i)
      (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix F G (∫ z, F z ∂muPre k) (P.preY k i) z))) / N
    let cD := featureDisplacementLambda c C g p q D L+(2+A_sp)*(L : ℝ)
    let A := sourceJumpCoefficient d (featureDisplacementLambda c C g p q D L) L *
      sourceGaussianDeviation (pTotal/(8*((J : ℝ)+1)))
    (∀ k < J, AbsolutelyContinuousOnInterval (closedBranch r (tau (k+1)) (pre k)) (tau k) (tau (k+1))) ∧
    AbsolutelyContinuousOnInterval r (tau J) T ∧
    IntervalIntegrable kappa volume 0 T ∧ IntervalIntegrable Gamma volume 0 T ∧
    (∀ t ∈ Icc 0 T, 0 ≤ Gamma t ∧ Gamma t ≤ delta) ∧
    (∀ k < J, GammaPre k ≤ delta ∧ GammaTildePre k ≤ deltaTilde ∧ 0 ≤ eta k) ∧
    (∀ k ≤ J, ∀ᵐ t ∂volume.restrict (Ioo (tau k) (if k < J then tau (k+1) else T)),
      deriv r t ≤ -kappa t*r t+cD*(r t)^2+Gamma t*r t+Gamma t) ∧
    (∀ k < J, r (tau (k+1)) ≤ (1+sourceJumpError A eta k)*pre k+
      sourceJumpForcing A eta GammaPre GammaTildePre k) ∧ r 0 = 0 := by
  have hZeq k (hk : k ≤ J) t (ht : t ∈ Ioo (tau k) (if k < J then tau (k+1) else T)) :
      ∀ᵐ ω ∂μ, P.Zbranch k ω t = P.Z ω t :=
    P.population_right_identity k hk t ⟨ht.1.le,ht.2.le⟩ (fun hkj => by simpa only [if_pos hkj] using ht.2)
  have hYeq k (hk : k ≤ J) t (ht : t ∈ Ioo (tau k) (if k < J then tau (k+1) else T)) :
      P.Ybranch k t = P.Y t :=
    P.particle_right_identity k hk t ⟨ht.1.le,ht.2.le⟩ (fun hkj => by simpa only [if_pos hkj] using ht.2)
  have hode := source_ode_schedule_of_actual_paths c C g p q K D alpha C3 φ hc hC hp hq hK hD
    hφ hgrowth hthirdφ hgrowth₃ G U hU hSU hG hthirdG L hL
    μ J tau T A_sp B hN htime P.Z P.Zbranch P.X P.Y P.preX P.preY P.population_class hZeq
    P.X_lip P.Y_lip P.X_right P.Y_right P.X_pre P.Y_pre P.X_final_lip P.Y_final_lip P.model_ode
  have hreg := source_schedule_marginal_residual_curvature_integrable μ N J hN tau T htau0
    (fun k hk => (htime k hk).le) hT P.Z P.Y P.Zbranch P.Ybranch φ c C g p q K D alpha L B
    hc hC hp hq hK hD halpha hφ hgrowth G U hU hSU hG P.population_class P.population_lip
    P.representative_lip P.representative_local hZeq hYeq
  have hgb := source_gamma_bound_of_actual_closed_labels μ tau J T delta htau0
    (fun k hk => (htime k hk).le) P.Z (fun t i => P.Y t i) P.Zbranch (fun k t i => P.Ybranch k t i)
    (fun k i => P.preY k i) (fun k => μ.map (fun ω => P.Zbranch k ω (tau (k+1))))
    (featureResidualWeight c p L) φ (fun n => (hφ n).continuous)
    (fun k hk t ht => (P.population_class k hk t (Icc_subset_uIcc ht)).1) hGammaLabels
    P.population_right_identity
    (fun k hk t ht hr => congrArg (fun v i => v i) (P.particle_right_identity k hk t ht hr))
    (fun k hk => congrArg (fun v i => v i) (P.particle_pre_identity k hk)) (fun _ _ => rfl)
  refine ⟨fun k hk => (hode.1 k hk).1,hode.2.1,hreg.2.1,hreg.1,
    fun t ht => ⟨hreg.2.2 t,hgb.1 t ht⟩,?_,hode.2.2,?_,?_⟩
  · intro k hk
    have he := (view ⟨k,hk⟩).eta_nonneg
    rw [hEta ⟨k,hk⟩] at he
    exact ⟨hgb.2 k hk,hCovPre k hk,he⟩
  · intro k hk
    let j : Fin J := ⟨k,hk⟩
    have hyloc : ∀ i, ‖P.preY k i‖ ≤ D := by
      intro i
      rw [← P.particle_pre_identity k hk]
      apply P.representative_local k hk.le i (tau (k+1))
      rw [if_pos hk]
      exact right_mem_uIcc
    exact actual_tracking_jump_recursion_of_observed_not_mem c C g p q D φ G L (view j).PopGood
      (fun h => (view j).κ h) (view j).X (view j).Y (view j).Xpost (view j).Ypost
      (view j).eta (pTotal/(8*((J : ℝ)+1))) ((view j).observation ω).1 ((view j).observation ω).2
      tau eta P.X P.Y P.preX P.preY (fun k => μ.map (fun ω => P.Zbranch k ω (tau (k+1)))) k
      (hJumpGood j) (hPopGood j) (P.preX_local k hk) hyloc (hPreX j) (hPreY j)
      (hPostX j) (hPostY j) (hPreLaw j) (hEta j)
  · simp only [P.initial_match,sub_self,norm_zero,zero_div]
end PaperFormalization.Manuscript
