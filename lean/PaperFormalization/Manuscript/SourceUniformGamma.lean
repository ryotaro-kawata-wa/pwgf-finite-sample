import PaperFormalization.Manuscript.ClippedResidualPathRegularity
import PaperFormalization.Manuscript.ClippedConcentrationThreshold
import PaperFormalization.Manuscript.FiniteBranchConcentration
import PaperFormalization.Manuscript.SourceWeightedPopulationBias

/-! # Actual localized uniform Gamma under one fixed population path law

The fixed-law application derives node concentration, time interpolation and
population bias internally. Branch labels retain distinct endpoint traces.
The original conditional path-law construction remains an external model
obligation; no independence is inferred after sample localization.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal
namespace PaperFormalization.Manuscript
variable {Ω Ξ E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

set_option maxHeartbeats 1600000 in
/-- Original path moments, actual fixed-time iid laws, and common AE path
regularity give the literal localized all-branch source Gamma budget. This
is an outer-measure bound, requiring no measurability premise on a continuum
supremum. No concentration, residual regularity or bias conclusion is assumed. -/
theorem source_uniform_gamma_failure_le
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (L N : ℕ) (hN : 0 < N) (a b : Fin (L+1) → ℝ) (hab : ∀ j, a j ≤ b j)
    (T : ℝ) (hlen : ∀ j, b j-a j ≤ T) (B : ℝ≥0)
    (Y : Fin (L+1) → Ω → ℝ → E) (X : Fin (L+1) → Ξ → Fin N → ℝ → E)
    (C g q alpha K D c₀ K₀ M : ℝ) (hC : 0 ≤ C) (hK : 0 < K) (hD : 0 ≤ D)
    (hc₀ : 0 ≤ c₀) (hK₀ : 0 < K₀) (halpha : 0 ≤ alpha)
    (w : ℕ → ℝ≥0) (φ : ∀ n, E → H n) (hφ : ∀ n, ContDiff ℝ 1 (φ n))
    (hvalue : ∀ n z, ‖φ n z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ (n+1)))
    (hderiv : ∀ n z, ‖fderiv ℝ (φ n) z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ n))
    (hclass : ∀ j t, t ∈ Icc (a j) (b j) →
      μ.map (fun ω => Y j ω t) ∈ sourceMomentClass alpha K)
    (hexp : ∀ j t, t ∈ Icc (a j) (b j) →
      Integrable (fun z => Real.exp (c₀ * (‖z‖/K₀)^alpha)) (μ.map (fun ω => Y j ω t)))
    (hM : ∀ j t, t ∈ Icc (a j) (b j) →
      (∫ z, Real.exp (c₀ * (‖z‖/K₀)^alpha) ∂μ.map (fun ω => Y j ω t)) ≤ M)
    (hpopPath : ∀ j, ∀ᵐ ω ∂μ, LipschitzOnWith B (Y j ω) (Icc (a j) (b j)))
    (hsamplePath : ∀ j, ∀ᵐ ξ ∂ν, ∀ i, LipschitzOnWith B (X j ξ i) (Icc (a j) (b j)))
    (hLaw : ∀ j t, t ∈ Icc (a j) (b j) → ∀ i,
      ν.map (fun ξ => X j ξ i t) = μ.map (fun ω => Y j ω t))
    (hind : ∀ j t, t ∈ Icc (a j) (b j) → iIndepFun (fun i ξ => X j ξ i t) ν)
    (hA : Summable (fun n => (w n : ℝ) * (featureGrowth C g q n * (1 + D ^ (n+1)))))
    (hΛ : Summable (fun n => (w n : ℝ) * (featureGrowth C g q n * (1 + 2 * D ^ n))))
    (hS : Summable (fun n => (w n : ℝ) * sourceCoordinateL2Envelope C g q alpha K n))
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    let A := 2 * ∑' n, (w n : ℝ) * (featureGrowth C g q n * (1 + D ^ (n+1)))
    let Λ := ∑' n, (w n : ℝ) * (featureGrowth C g q n * (1 + 2 * D ^ n))
    let S := ∑' n, (w n : ℝ) * sourceCoordinateL2Envelope C g q alpha K n
    let beta := 2 * S * Real.sqrt M * Real.exp (-(c₀ * (D/K₀)^alpha)/2)
    let Q := (((L+1 : ℕ) : ℝ) * ((N+1 : ℕ) : ℝ))
    ν.real {ξ | (∀ j t, t ∈ Icc (a j) (b j) → ∀ i, ‖X j ξ i t‖ ≤ D) ∧
      ∃ j, ∃ t ∈ Icc (a j) (b j),
        beta + A / Real.sqrt N + A * Real.sqrt (Real.log (Q/p)/(2*N)) +
          2 * (B : ℝ) * T * Λ / N <
        weightedSampleResidual w φ (fun n => ∫ z, φ n z ∂μ.map (fun ω => Y j ω t))
          (fun i => X j ξ i t)} ≤ p := by
  let A := 2 * ∑' n, (w n : ℝ) * (featureGrowth C g q n * (1 + D ^ (n+1)))
  let Λ := ∑' n, (w n : ℝ) * (featureGrowth C g q n * (1 + 2 * D ^ n))
  let S := ∑' n, (w n : ℝ) * sourceCoordinateL2Envelope C g q alpha K n
  let beta := 2 * S * Real.sqrt M * Real.exp (-(c₀ * (D/K₀)^alpha)/2)
  let Q := (((L+1 : ℕ) : ℝ) * ((N+1 : ℕ) : ℝ))
  let r := A / Real.sqrt N + A * Real.sqrt (Real.log (Q/p)/(2*N))
  let F := fun j ξ t => weightedClippedSampleResidual (μ.map (fun ω => Y j ω t)) D w φ (fun i => X j ξ i t)
  let R := fun j ξ t => weightedSampleResidual w φ
    (fun n => ∫ z, φ n z ∂μ.map (fun ω => Y j ω t)) (fun i => X j ξ i t)
  let Good : Set Ξ := {ξ | ∀ j i, LipschitzOnWith B (X j ξ i) (Icc (a j) (b j))}
  let Local : Set Ξ := {ξ | ∀ j t, t ∈ Icc (a j) (b j) → ∀ i, ‖X j ξ i t‖ ≤ D}
  have hgood : ∀ᵐ ξ ∂ν, ξ ∈ Good := ae_all_iff.mpr hsamplePath
  have hL (n : ℕ) : 0 ≤ featureGrowth C g q n := featureGrowth_nonneg C g q hC n
  have hY (j) (t) (ht : t ∈ Icc (a j) (b j)) : AEStronglyMeasurable (fun ω => Y j ω t) μ := by
    haveI : IsProbabilityMeasure (μ.map (fun ω => Y j ω t)) := (hclass j t ht).1
    exact (aemeasurable_of_map_neZero (by infer_instance)).aestronglyMeasurable
  have hΛ0 : 0 ≤ Λ := tsum_nonneg (fun n => mul_nonneg (w n).coe_nonneg (mul_nonneg (hL n) (by positivity)))
  let rate := Real.toNNReal (2 * (B : ℝ) * Λ)
  have hrate : (rate : ℝ) = 2 * (B : ℝ) * Λ := Real.coe_toNNReal _ (by positivity)
  have hF : ∀ j ξ, ξ ∈ Good → LipschitzOnWith rate (F j ξ) (Icc (a j) (b j)) := by
    intro j ξ hξ
    exact (clippedResidualPath_summable_lipschitzOn μ (Y j) (X j ξ) hN D hD B
      (Icc (a j) (b j)) w (featureGrowth C g q) hL φ hφ hvalue hderiv
      (hY j) (hpopPath j) (hξ j) hA hΛ).2
  have hraw : ∀ j ξ, ξ ∈ Good → ξ ∈ Local → ∀ t ∈ Icc (a j) (b j), R j ξ t ≤ F j ξ t + beta := by
    intro j ξ _hgood hloc t ht
    exact source_weighted_unclipping_exp_le hN C g q alpha K D c₀ K₀ M hC hK hD hc₀ hK₀ halpha
      (μ.map (fun ω => Y j ω t)) (hclass j t ht) (hexp j t ht) (hM j t ht)
      w φ (fun n => (hφ n).continuous) hvalue hA hS (fun i => X j ξ i t) (hloc j t ht)
  have hQ1 : 1 ≤ Q := by dsimp [Q]; norm_cast; nlinarith
  have hQ : 0 < Q := lt_of_lt_of_le zero_lt_one hQ1
  have hnode : ∀ j i, ν.real {ξ | r < F j ξ (closedBranchGrid (a j) (b j) N i)} ≤ p/Q := by
    intro j i
    let t := closedBranchGrid (a j) (b j) N i
    have ht : t ∈ Icc (a j) (b j) := closedBranchGrid_mem (a j) (b j) (hab j) hN i
    letI : IsProbabilityMeasure (μ.map (fun ω => Y j ω t)) := (hclass j t ht).1
    exact weightedClippedSampleResidual_iid_source_threshold hN (μ.map (fun ω => Y j ω t)) ν
      (fun i ξ => X j ξ i t) (hLaw j t ht) (hind j t ht) D hD w (featureGrowth C g q)
      (fun n => n+1) hL φ (fun n => (hφ n).continuous) hvalue hA Q p hQ hp (hp1.trans_le hQ1)
  have hb := measureReal_localized_raw_branch_failure_le ν Good Local L N hN a b hab T hlen rate
    F R hF beta r p hraw hnode
  have he : beta + r + (rate : ℝ) * (T/N) =
      beta + A / Real.sqrt N + A * Real.sqrt (Real.log (Q/p)/(2*N)) + 2 * (B : ℝ) * T * Λ/N := by
    rw [hrate]
    dsimp [r]
    ring
  rw [he] at hb
  have hset : {ξ | ξ ∈ Local ∧ ∃ j, ∃ t ∈ Icc (a j) (b j),
      beta + A / Real.sqrt N + A * Real.sqrt (Real.log (Q/p)/(2*N)) + 2 * (B : ℝ) * T * Λ/N < R j ξ t} =ᵐ[ν]
      {ξ | ξ ∈ Good ∧ ξ ∈ Local ∧ ∃ j, ∃ t ∈ Icc (a j) (b j),
      beta + A / Real.sqrt N + A * Real.sqrt (Real.log (Q/p)/(2*N)) + 2 * (B : ℝ) * T * Λ/N < R j ξ t} := by
    filter_upwards [hgood] with ξ hξ
    apply propext
    exact ⟨fun h => ⟨hξ, h⟩, fun h => h.2⟩
  exact (measureReal_congr hset).le.trans hb
end PaperFormalization.Manuscript
