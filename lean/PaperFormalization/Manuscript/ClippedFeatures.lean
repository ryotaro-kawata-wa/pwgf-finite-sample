import PaperFormalization.Manuscript.RadialClip
import PaperFormalization.Manuscript.HilbertSampleMean
import PaperFormalization.Manuscript.CoordinateMoments

/-! # Concrete clipped feature envelopes

The actual radial map supplies the amplitude and spatial bounds in the source.
Population integrals and sample means keep their original laws. Clipping the
feature is not conditioning on a localized sample event.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace PaperFormalization.Manuscript

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F]

/-- The actual clipped feature has the exact source bounded amplitude. -/
theorem norm_clipped_feature_le (D L : ℝ) (m : ℕ) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (φ : E → F) (hg : ∀ x, ‖φ x‖ ≤ L * (1 + ‖x‖ ^ m)) (x : E) :
    ‖φ (sourceRadialClip D x)‖ ≤ L * (1 + D ^ m) := by
  exact (hg _).trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) (norm_sourceRadialClip_le D hD x) m)) hL)

/-- The clipping error vanishes on the ball and obeys the exact polynomial
population-tail majorant outside. -/
theorem norm_feature_sub_clipped_le (D L : ℝ) (m : ℕ) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (φ : E → F) (hg : ∀ x, ‖φ x‖ ≤ L * (1 + ‖x‖ ^ m)) (x : E) :
    ‖φ x - φ (sourceRadialClip D x)‖ ≤
      if D < ‖x‖ then 2 * L * (1 + ‖x‖ ^ m) else 0 := by
  split_ifs with hx
  · have hp : D ^ m ≤ ‖x‖ ^ m := pow_le_pow_left₀ hD hx.le m
    have hc := norm_clipped_feature_le D L m hD hL φ hg x
    have hn := norm_sub_le (φ x) (φ (sourceRadialClip D x))
    nlinarith [hg x, mul_le_mul_of_nonneg_left hp hL]
  · rw [sourceRadialClip_of_norm_le D x (le_of_not_gt hx), sub_self, norm_zero]

variable [NormedSpace ℝ F]

/-- Mean value on the ball and exact nonexpansiveness prove the clipped
feature's global spatial bound without a derivative of radial clipping. -/
theorem clipped_feature_norm_sub_le (D L : ℝ) (m : ℕ) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (φ : E → F)
    (hφ : ∀ x ∈ Metric.closedBall (0 : E) D, DifferentiableAt ℝ φ x)
    (hder : ∀ x ∈ Metric.closedBall (0 : E) D, ‖fderiv ℝ φ x‖ ≤ L * (1 + ‖x‖ ^ m))
    (x y : E) :
    ‖φ (sourceRadialClip D x) - φ (sourceRadialClip D y)‖ ≤
      L * (1 + D ^ m) * ‖x-y‖ := by
  have hb : ∀ z ∈ Metric.closedBall (0 : E) D, ‖fderiv ℝ φ z‖ ≤ L * (1 + D ^ m) := by
    intro z hz
    have hz' : ‖z‖ ≤ D := by simpa using hz
    exact (hder z hz).trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) hz' m)) hL)
  have hy : sourceRadialClip D y ∈ Metric.closedBall (0 : E) D := by
    simpa using norm_sourceRadialClip_le D hD y
  have hx : sourceRadialClip D x ∈ Metric.closedBall (0 : E) D := by
    simpa using norm_sourceRadialClip_le D hD x
  exact ((convex_closedBall (0 : E) D).norm_image_sub_le_of_norm_fderiv_le
    hφ hb hy hx).trans (mul_le_mul_of_nonneg_left
      (sourceRadialClip_norm_sub_le D hD x y) (by positivity))

section Probability
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [NormedSpace ℝ F] in
/-- Actual clipped coordinates are genuinely L2 under the unchanged finite
population measure, independent of any population support restriction. -/
theorem clipped_feature_memLp_two (μ : Measure E) [IsFiniteMeasure μ]
    (D L : ℝ) (m : ℕ) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (φ : E → F) (hφ : Continuous φ)
    (hg : ∀ x, ‖φ x‖ ≤ L * (1 + ‖x‖ ^ m)) :
    MemLp (fun x => φ (sourceRadialClip D x)) 2 μ := by
  apply MemLp.of_bound (hφ.comp (sourceRadialClip_continuous D hD)).aestronglyMeasurable
    (L * (1 + D ^ m))
  exact Filter.Eventually.of_forall (norm_clipped_feature_le D L m hD hL φ hg)

end Probability

section Sample
variable {Ω H : Type*} [MeasurableSpace Ω]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H]

/-- The actual clipped empirical mean has expected error at most the exact
clipped amplitude divided by sqrt N, under the original common law. -/
theorem expected_clipped_feature_sampleMean_error_le {N : ℕ}
    (μ : Measure E) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (Y : Fin N → Ω → E) (hN : 0 < N)
    (hLaw : ∀ i, ν.map (Y i) = μ)
    (hind : Pairwise (fun i j => IndepFun (Y i) (Y j) ν))
    (D L : ℝ) (m : ℕ) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (φ : E → H) (hφ : Continuous φ)
    (hg : ∀ x, ‖φ x‖ ≤ L * (1 + ‖x‖ ^ m)) :
    (∫ ω, ‖(N : ℝ)⁻¹ • ∑ i, φ (sourceRadialClip D (Y i ω)) -
      ∫ x, φ (sourceRadialClip D x) ∂μ‖ ∂ν) ≤ L * (1 + D ^ m) / Real.sqrt N := by
  let f := fun x => φ (sourceRadialClip D x)
  let A := L * (1 + D ^ m)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hf : Continuous f := hφ.comp (sourceRadialClip_continuous D hD)
  have hm : MemLp f 2 μ := clipped_feature_memLp_two μ D L m hD hL φ hφ hg
  have hY (i : Fin N) : AEMeasurable (Y i) ν :=
    aemeasurable_of_map_neZero (by rw [hLaw i]; infer_instance)
  have hX (i : Fin N) : MemLp (fun ω => f (Y i ω)) 2 ν := by
    have hmap : MemLp f 2 (ν.map (Y i)) := by rw [hLaw i]; exact hm
    exact hmap.comp_of_map (hY i)
  have hs := integral_norm_sampleMean_sub_le ν (fun i ω => f (Y i ω)) hN hX
    (fun i j hij => (hind hij).comp hf.measurable hf.measurable) (∫ x, f x ∂μ)
    (fun i => by rw [← integral_map (hY i) hf.aestronglyMeasurable, hLaw i]) (A ^ 2) (by
      intro i
      calc
        _ ≤ ∫ _ω, A ^ 2 ∂ν := integral_mono ((hX i).integrable_norm_pow (by norm_num))
          (integrable_const _) (fun ω => pow_le_pow_left₀ (norm_nonneg _)
            (norm_clipped_feature_le D L m hD hL φ hg (Y i ω)) 2)
        _ = A ^ 2 := by simp)
  simpa only [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hA] using hs

end Sample

end PaperFormalization.Manuscript
