import PaperFormalization.Manuscript.SourceScheduleRegularity

/-! # Actual population marginals over the full jump schedule

The marginal is literally the pushforward of the unchanged path law. Closed
representatives provide measurability only at open branch times; their actual
AE identification suffices to derive every needed integral-map identity there.
Finite endpoint exceptions need no new moment or measurability assumptions.
-/
open MeasureTheory Set Filter
open scoped NNReal BigOperators
namespace PaperFormalization.Manuscript
open Continuous

/-- Transfer a global integrability result through equality on each open
branch. All finitely many pre/post endpoint discrepancies are allowed. -/
theorem intervalIntegrable_of_schedule_interior_eq
    (tau : ℕ → ℝ) (J : ℕ) (T : ℝ) (f g : ℝ → ℝ)
    (htau0 : tau 0 = 0) (htime : ∀ k < J, tau k ≤ tau (k+1)) (hT : tau J ≤ T)
    (hf : IntervalIntegrable f volume 0 T)
    (heq : ∀ k ≤ J, EqOn f g (Ioo (tau k) (if k < J then tau (k+1) else T))) :
    IntervalIntegrable g volume 0 T := by
  have hmono : Monotone (fun k => tau (min k J)) := by
    apply monotone_nat_of_le_succ
    intro k
    by_cases hk : k < J
    · simpa only [min_eq_left hk.le, min_eq_left (show k+1 ≤ J by omega)] using htime k hk
    · have hk' : J ≤ k := by omega
      simp only [min_eq_right hk', min_eq_right (show J ≤ k+1 by omega), le_refl]
  have hbounds (k : ℕ) (hk : k ≤ J) : 0 ≤ tau k ∧ tau k ≤ T := by
    have hlo := hmono (Nat.zero_le k)
    have hup := hmono hk
    simp only [Nat.zero_min, min_eq_left hk, min_self, htau0] at hlo hup
    exact ⟨hlo,hup.trans hT⟩
  have hT0 : 0 ≤ T := (hbounds J le_rfl).1.trans hT
  have hsub (a b : ℝ) (ha : 0 ≤ a ∧ a ≤ T) (hb : 0 ≤ b ∧ b ≤ T) :
      uIcc a b ⊆ uIcc 0 T := by
    rw [uIcc_of_le hT0]
    exact uIcc_subset_Icc ha hb
  have hreg (k : ℕ) (hk : k ≤ J) :
      IntervalIntegrable f volume (tau k) (if k < J then tau (k+1) else T) := by
    apply hf.mono_set
    apply hsub _ _ (hbounds k hk)
    split_ifs with hkj
    · exact hbounds (k+1) (by omega)
    · exact ⟨hT0,le_rfl⟩
  have hh := intervalIntegrable_of_finite_branch_representatives_and_final tau (fun _ => f) g f J T htime
    (fun k hk => by simpa only [if_pos hk] using hreg k hk.le)
    (fun k hk => by simpa only [if_pos hk] using heq k hk.le)
    hT (by simpa only [lt_self_iff_false, ↓reduceIte] using hreg J le_rfl)
    (by simpa only [lt_self_iff_false, ↓reduceIte] using heq J le_rfl)
  simpa only [htau0] using hh

section Marginal
variable {Ω E F : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
  [TopologicalSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- An actual variable AE equal to a probability-valued branch representative
is measurable up to null sets. Its continuous-feature integral is the integral
under its own genuine pushforward, with no extra endpoint law premise. -/
theorem integral_map_of_ae_probability_representative
    (μ : Measure Ω) (Zbranch Z : Ω → E)
    (hprob : IsProbabilityMeasure (μ.map Zbranch)) (heq : Zbranch =ᵐ[μ] Z)
    (f : E → F) (hf : Continuous f) :
    AEMeasurable Z μ ∧ (∫ z, f z ∂(μ.map Z)) = ∫ ω, f (Z ω) ∂μ := by
  letI := hprob
  have hbranch : AEMeasurable Zbranch μ := aemeasurable_of_map_neZero (by infer_instance)
  have hZ : AEMeasurable Z μ := hbranch.congr heq
  exact ⟨hZ, integral_map hZ hf.aestronglyMeasurable⟩
end Marginal

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [BorelSpace E] [SecondCountableTopology E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000 in
/-- The actual pushforward population laws have globally integrable literal
Gamma and full sampled-Hessian curvature. Gamma is nonnegative at every time;
no summability or moment claim is made at arbitrary unmatched endpoints. -/
theorem source_schedule_marginal_residual_curvature_integrable
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N J : ℕ) (hN : 0 < N) (tau : ℕ → ℝ) (T : ℝ)
    (htau0 : tau 0 = 0) (htime : ∀ k < J, tau k ≤ tau (k+1)) (hT : tau J ≤ T)
    (Z : Ω → ℝ → E) (Y : ℝ → PiLp 2 fun _ : Fin N => E)
    (Zbranch : ℕ → Ω → ℝ → E) (Ybranch : ℕ → ℝ → PiLp 2 fun _ : Fin N => E)
    (φ : ∀ n, E → H n) (c C g p q K D alpha : ℝ) (L B : ℝ≥0)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (hK : 0 < K) (hD : 1 ≤ D) (halpha : 0 < alpha)
    (hφ : ∀ n, ContDiff ℝ 2 (φ n))
    (hgrowth : ∀ n z k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) z‖ ≤
      featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1 - k)))
    (G : lp H 2 → ℝ) (U : Set (lp H 2)) (hU : IsOpen U)
    (hSU : measureMomentRegion (sourceWeightedFeatureMap c p φ) (sourceMomentClass alpha K) D ⊆ U)
    (hG : ContDiffOn ℝ 3 G U)
    (hclass : ∀ k ≤ J, ∀ t ∈ uIcc (tau k) (if k < J then tau (k+1) else T),
      μ.map (fun ω => Zbranch k ω t) ∈ sourceMomentClass alpha K)
    (hpath : ∀ k ≤ J, ∀ᵐ ω ∂μ,
      LipschitzOnWith B (Zbranch k ω) (uIcc (tau k) (if k < J then tau (k+1) else T)))
    (hYlip : ∀ k ≤ J, ∀ i, LipschitzOnWith B (fun t => Ybranch k t i)
      (uIcc (tau k) (if k < J then tau (k+1) else T)))
    (hYloc : ∀ k ≤ J, ∀ i t, t ∈ uIcc (tau k) (if k < J then tau (k+1) else T) →
      ‖Ybranch k t i‖ ≤ D)
    (hZeq : ∀ k ≤ J, ∀ t ∈ Ioo (tau k) (if k < J then tau (k+1) else T),
      ∀ᵐ ω ∂μ, Zbranch k ω t = Z ω t)
    (hYeq : ∀ k ≤ J, ∀ t ∈ Ioo (tau k) (if k < J then tau (k+1) else T),
      Ybranch k t = Y t) :
    let F := sourceWeightedFeatureMap c p φ
    let Gamma := momentResidual (featureResidualWeight c p L)
      (fun n t => finiteFeatureMean (fun i => φ n (Y t i))) (fun n t => ∫ z, φ n z ∂(μ.map (fun ω => Z ω t)))
    let kappa := fun t => rayleighInf (sampledMomentHessian F G (∫ z, F z ∂(μ.map (fun ω => Z ω t))) (Y t))
    IntervalIntegrable Gamma volume 0 T ∧ IntervalIntegrable kappa volume 0 T ∧
      ∀ t, 0 ≤ Gamma t := by
  let F := sourceWeightedFeatureMap c p φ
  let GammaPath := momentResidual (featureResidualWeight c p L)
    (fun n t => finiteFeatureMean (fun i => φ n (Y t i))) (fun n t => ∫ ω, φ n (Z ω t) ∂μ)
  let kappaPath := fun t => rayleighInf (sampledMomentHessian F G (∫ ω, F (Z ω t) ∂μ) (Y t))
  have hreg := source_schedule_residual_curvature_integrable μ N J hN tau T htau0 htime hT
    Z Y Zbranch Ybranch φ c C g p q K D alpha L B hc hC hp hq hK hD halpha
    hφ hgrowth G U hU hSU hG hclass hpath hYlip hYloc hZeq hYeq
  have hF : Continuous F :=
    (contDiff_sourceWeightedFeatureMap c C g p q φ hc hC hp hq hφ hgrowth).continuous
  have hid (k : ℕ) (hk : k ≤ J) (t : ℝ)
      (ht : t ∈ Ioo (tau k) (if k < J then tau (k+1) else T)) :
      AEMeasurable (fun ω => Z ω t) μ := by
    exact (integral_map_of_ae_probability_representative μ (fun ω => Zbranch k ω t)
      (fun ω => Z ω t) (hclass k hk t (Icc_subset_uIcc ⟨ht.1.le,ht.2.le⟩)).1
      (hZeq k hk t ht) F hF).1
  refine ⟨?_, ?_, fun t => momentResidual_nonneg _ _ _ t⟩
  · apply intervalIntegrable_of_schedule_interior_eq tau J T GammaPath _ htau0 htime hT hreg.1
    intro k hk t ht
    dsimp only [GammaPath, momentResidual, momentResidualTerm]
    apply tsum_congr
    intro n
    rw [coordinate_feature_integral_map μ (fun ω => Z ω t) (φ n) (hid k hk t ht) (hφ n).continuous]
  · apply intervalIntegrable_of_schedule_interior_eq tau J T kappaPath _ htau0 htime hT hreg.2
    intro k hk t ht
    dsimp only [kappaPath]
    rw [coordinate_feature_integral_map μ (fun ω => Z ω t) F (hid k hk t ht) hF]
end PaperFormalization.Manuscript
