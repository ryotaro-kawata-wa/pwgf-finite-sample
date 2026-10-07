import PaperFormalization.Manuscript.WeightedClippedSampleMean
import PaperFormalization.Manuscript.MomentResidual
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! # Time regularity of the actual clipped residual under one fixed path law

Clipping acts only on features. Actual time marginals are pushforwards of one
unchanged population path law, with one common AE Lipschitz-path event. No
population support bound or time-dependent reconditioning is used. The source
index is m=n+1, so first-derivative growth has exponent n.
-/

open MeasureTheory Set Filter
open scoped BigOperators NNReal Topology

namespace PaperFormalization.Manuscript

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Actual clipped population coordinate integrals are genuinely integrable
and have time Lipschitz rate B L(1+D^n), from the first derivative and path bounds. -/
theorem clipped_population_coordinate_path_regularity
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ → E)
    (φ : E → F) (n : ℕ) (L D : ℝ) (B : ℝ≥0) (S : Set ℝ)
    (hL : 0 ≤ L) (hD : 0 ≤ D) (hφ : ContDiff ℝ 1 φ)
    (hvalue : ∀ z, ‖φ z‖ ≤ L * (1 + ‖z‖ ^ (n + 1)))
    (hderiv : ∀ z, ‖fderiv ℝ φ z‖ ≤ L * (1 + ‖z‖ ^ n))
    (hY : ∀ t ∈ S, AEStronglyMeasurable (fun ω => Y ω t) μ)
    (hpath : ∀ᵐ ω ∂μ, LipschitzOnWith B (Y ω) S) :
    (∀ t ∈ S, Integrable (fun ω => φ (sourceRadialClip D (Y ω t))) μ ∧
      ‖∫ ω, φ (sourceRadialClip D (Y ω t)) ∂μ‖ ≤ L * (1 + D ^ (n + 1))) ∧
    LipschitzOnWith (Real.toNNReal ((B : ℝ) * L * (1 + D ^ n)))
      (fun t => ∫ ω, φ (sourceRadialClip D (Y ω t)) ∂μ) S := by
  have hc : Continuous (fun z => φ (sourceRadialClip D z)) :=
    hφ.continuous.comp (sourceRadialClip_continuous D hD)
  have hint (t : ℝ) (ht : t ∈ S) :
      Integrable (fun ω => φ (sourceRadialClip D (Y ω t))) μ :=
    Integrable.of_bound (hc.comp_aestronglyMeasurable (hY t ht)) (L * (1 + D ^ (n + 1)))
      (Eventually.of_forall fun ω => norm_clipped_feature_le D L (n + 1) hD hL φ hvalue _)
  constructor
  · intro t ht
    refine ⟨hint t ht, ?_⟩
    simpa using norm_integral_le_of_norm_le_const (μ := μ)
      (Eventually.of_forall fun ω => norm_clipped_feature_le D L (n + 1) hD hL φ hvalue (Y ω t))
  · apply LipschitzOnWith.of_dist_le'
    intro t ht u hu
    rw [dist_eq_norm, ← integral_sub (hint t ht) (hint u hu)]
    have hb : ∀ᵐ ω ∂μ,
        ‖φ (sourceRadialClip D (Y ω t)) - φ (sourceRadialClip D (Y ω u))‖ ≤
          ((B : ℝ) * L * (1 + D ^ n)) * dist t u := by
      filter_upwards [hpath] with ω hω
      have hs := clipped_feature_norm_sub_le D L n hD hL φ
        (fun z _ => hφ.differentiable (by norm_num) z) (fun z _ => hderiv z) (Y ω t) (Y ω u)
      have hp : ‖Y ω t - Y ω u‖ ≤ (B : ℝ) * dist t u := by
        simpa only [dist_eq_norm] using hω.dist_le_mul t ht u hu
      exact (hs.trans (mul_le_mul_of_nonneg_left hp (by positivity))).trans_eq (by ring)
    simpa using norm_integral_le_of_norm_le_const hb

variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)] {N : ℕ}

/-- The actual countable clipped residual converges and has the source time
Lipschitz constant 2BΛ. Coordinate estimates use the sharper 1+D^n bound;
comparison with 1+2D^n recovers exactly the manuscript's Λ. -/
theorem clippedResidualPath_summable_lipschitzOn
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ → E) (X : Fin N → ℝ → E)
    (hN : 0 < N) (D : ℝ) (hD : 0 ≤ D) (B : ℝ≥0) (S : Set ℝ)
    (w : ℕ → ℝ≥0) (L : ℕ → ℝ) (hL : ∀ n, 0 ≤ L n)
    (φ : ∀ n, E → H n) (hφ : ∀ n, ContDiff ℝ 1 (φ n))
    (hvalue : ∀ n z, ‖φ n z‖ ≤ L n * (1 + ‖z‖ ^ (n + 1)))
    (hderiv : ∀ n z, ‖fderiv ℝ (φ n) z‖ ≤ L n * (1 + ‖z‖ ^ n))
    (hY : ∀ t ∈ S, AEStronglyMeasurable (fun ω => Y ω t) μ)
    (hpath : ∀ᵐ ω ∂μ, LipschitzOnWith B (Y ω) S)
    (hX : ∀ i, LipschitzOnWith B (X i) S)
    (hA : Summable (fun n => (w n : ℝ) * (L n * (1 + D ^ (n + 1)))))
    (hΛ : Summable (fun n => (w n : ℝ) * (L n * (1 + 2 * D ^ n)))) :
    (∀ t ∈ S, Summable (fun n => (w n : ℝ) *
      ‖(N : ℝ)⁻¹ • ∑ i, φ n (sourceRadialClip D (X i t)) -
        ∫ z, φ n (sourceRadialClip D z) ∂μ.map (fun ω => Y ω t)‖)) ∧
    LipschitzOnWith (Real.toNNReal
      (2 * (B : ℝ) * ∑' n, (w n : ℝ) * (L n * (1 + 2 * D ^ n))))
      (fun t => weightedClippedSampleResidual (μ.map (fun ω => Y ω t)) D w φ
        (fun i => X i t)) S := by
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  let emp : ∀ n, ℝ → H n := fun n t =>
    finiteFeatureMean (fun i => φ n (sourceRadialClip D (X i t)))
  let pop : ∀ n, ℝ → H n := fun n t => ∫ ω, φ n (sourceRadialClip D (Y ω t)) ∂μ
  let amp : ℕ → ℝ := fun n => L n * (1 + D ^ (n + 1))
  let rate : ℕ → ℝ≥0 := fun n => Real.toNNReal ((B : ℝ) * L n * (1 + D ^ n))
  have hr (n : ℕ) : (rate n : ℝ) = (B : ℝ) * L n * (1 + D ^ n) :=
    Real.coe_toNNReal _ (mul_nonneg (mul_nonneg B.coe_nonneg (hL n)) (by positivity))
  have hpop (n : ℕ) := clipped_population_coordinate_path_regularity μ Y (φ n) n
    (L n) D B S (hL n) hD (hφ n) (hvalue n) (hderiv n) hY hpath
  have hea (n : ℕ) (t : ℝ) (_ht : t ∈ S) : ‖emp n t‖ ≤ amp n := by
    apply norm_finiteFeatureMean_le
    intro i
    exact norm_clipped_feature_le D (L n) (n + 1) hD (hL n) (φ n) (hvalue n) _
  have hpa (n : ℕ) (t : ℝ) (ht : t ∈ S) : ‖pop n t‖ ≤ amp n := (hpop n).1 t ht |>.2
  have hel (n : ℕ) : LipschitzOnWith (rate n) (emp n) S := by
    apply finiteFeatureMean_lipschitzOn
    intro i
    apply LipschitzOnWith.of_dist_le_mul
    intro t ht u hu
    rw [dist_eq_norm, hr]
    have hs := clipped_feature_norm_sub_le D (L n) n hD (hL n) (φ n)
      (fun z _ => (hφ n).differentiable (by norm_num) z) (fun z _ => hderiv n z)
      (X i t) (X i u)
    have hx : ‖X i t - X i u‖ ≤ (B : ℝ) * dist t u := by
      simpa only [dist_eq_norm] using (hX i).dist_le_mul t ht u hu
    exact (hs.trans (mul_le_mul_of_nonneg_left hx (mul_nonneg (hL n) (by positivity)))).trans_eq (by ring)
  have hpl (n : ℕ) : LipschitzOnWith (rate n) (pop n) S := (hpop n).2
  have hAmp : Summable (fun n => (w n : ℝ) * (amp n + amp n)) := by
    apply (hA.mul_left 2).congr
    intro n
    dsimp only [amp]
    ring
  have hterm (n : ℕ) : (w n : ℝ) * ((rate n : ℝ) + (rate n : ℝ)) ≤
      (2 * (B : ℝ)) * ((w n : ℝ) * (L n * (1 + 2 * D ^ n))) := by
    rw [hr]
    calc
      _ = (2 * (B : ℝ)) * ((w n : ℝ) * (L n * (1 + D ^ n))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (by nlinarith [pow_nonneg hD n]) (hL n))
          (w n).coe_nonneg) (by positivity)
  have hRate : Summable (fun n => (w n : ℝ) * ((rate n : ℝ) + (rate n : ℝ))) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hterm (hΛ.mul_left (2 * (B : ℝ)))
  have hbound : (∑' n, w n * (rate n + rate n)) ≤ Real.toNNReal
      (2 * (B : ℝ) * ∑' n, (w n : ℝ) * (L n * (1 + 2 * D ^ n))) := by
    apply NNReal.coe_le_coe.mp
    rw [NNReal.coe_tsum, Real.coe_toNNReal _ (mul_nonneg (by positivity)
      (tsum_nonneg fun n => mul_nonneg (w n).coe_nonneg (mul_nonneg (hL n) (by positivity))))]
    simp only [NNReal.coe_mul, NNReal.coe_add]
    exact (hRate.tsum_le_tsum hterm (hΛ.mul_left (2 * (B : ℝ)))).trans_eq tsum_mul_left
  have heq (t : ℝ) (ht : t ∈ S) (n : ℕ) : momentResidualTerm w emp pop n t =
      (w n : ℝ) * ‖(N : ℝ)⁻¹ • ∑ i, φ n (sourceRadialClip D (X i t)) -
        ∫ z, φ n (sourceRadialClip D z) ∂μ.map (fun ω => Y ω t)‖ := by
    have hc : Continuous (fun z => φ n (sourceRadialClip D z)) :=
      (hφ n).continuous.comp (sourceRadialClip_continuous D hD)
    rw [integral_map (hY t ht).aemeasurable hc.aestronglyMeasurable]
    simp only [momentResidualTerm, emp, pop, finiteFeatureMean, Fintype.card_fin]
  have hfeq (t : ℝ) (ht : t ∈ S) :
      weightedClippedSampleResidual (μ.map (fun ω => Y ω t)) D w φ (fun i => X i t) =
        momentResidual w emp pop t := by
    apply tsum_congr
    intro n
    exact (heq t ht n).symm
  constructor
  · intro t ht
    simpa only [heq t ht] using momentResidual_summable w emp pop amp amp S hAmp hea hpa t ht
  · have hlip := (momentResidual_lipschitzOn w emp pop amp amp rate rate S
      hAmp hea hpa hRate hel hpl).weaken hbound
    intro t ht u hu
    dsimp only
    rw [hfeq t ht, hfeq u hu]
    exact hlip ht hu

/-- Under an arbitrary original sample-system law, one AE whole-path event
of B-Lipschitz samples gives the exact source clipped-residual time bound,
absolute continuity, and interval integrability on the closed branch. -/
theorem clippedResidualPath_closedBranch_regular_ae
    {Ω' : Type*} [MeasurableSpace Ω']
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ω')
    (Y : Ω → ℝ → E) (X : Ω' → Fin N → ℝ → E)
    (hN : 0 < N) (D : ℝ) (hD : 0 ≤ D) (B : ℝ≥0) (a b : ℝ)
    (w : ℕ → ℝ≥0) (L : ℕ → ℝ) (hL : ∀ n, 0 ≤ L n)
    (φ : ∀ n, E → H n) (hφ : ∀ n, ContDiff ℝ 1 (φ n))
    (hvalue : ∀ n z, ‖φ n z‖ ≤ L n * (1 + ‖z‖ ^ (n + 1)))
    (hderiv : ∀ n z, ‖fderiv ℝ (φ n) z‖ ≤ L n * (1 + ‖z‖ ^ n))
    (hY : ∀ t ∈ uIcc a b, AEStronglyMeasurable (fun ω => Y ω t) μ)
    (hpath : ∀ᵐ ω ∂μ, LipschitzOnWith B (Y ω) (uIcc a b))
    (hX : ∀ᵐ ξ ∂ν, ∀ i, LipschitzOnWith B (X ξ i) (uIcc a b))
    (hA : Summable (fun n => (w n : ℝ) * (L n * (1 + D ^ (n + 1)))))
    (hΛ : Summable (fun n => (w n : ℝ) * (L n * (1 + 2 * D ^ n)))) :
    ∀ᵐ ξ ∂ν,
      let F := fun t => weightedClippedSampleResidual (μ.map (fun ω => Y ω t)) D w φ
        (fun i => X ξ i t)
      LipschitzOnWith (Real.toNNReal
        (2 * (B : ℝ) * ∑' n, (w n : ℝ) * (L n * (1 + 2 * D ^ n)))) F (uIcc a b) ∧
      AbsolutelyContinuousOnInterval F a b ∧ IntervalIntegrable F volume a b := by
  filter_upwards [hX] with ξ hξ
  have hlip := (clippedResidualPath_summable_lipschitzOn μ Y (X ξ) hN D hD B
    (uIcc a b) w L hL φ hφ hvalue hderiv hY hpath hξ hA hΛ).2
  exact ⟨hlip, hlip.absolutelyContinuousOnInterval, hlip.continuousOn.intervalIntegrable⟩

end PaperFormalization.Manuscript
