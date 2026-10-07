import PaperFormalization.Manuscript.ConditionalPathMarginal
import PaperFormalization.Manuscript.KernelClippedResidual
import PaperFormalization.Manuscript.EligibleBranchEvent
import PaperFormalization.Manuscript.ClippedResidualPathRegularity
import PaperFormalization.Manuscript.SourceWeightedPopulationBias

/-! # A measurable uniform source Gamma event under the original joint law

Every time marginal is derived from one fixed conditional population path
kernel. Population eligibility restricts hypotheses and failure events,
never the history law or the sample kernel. Actual node concentration, path
regularity and unclipping derive the all-time event; no continuum-event
measurability or uniform concentration conclusion is assumed.
-/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ProbabilityTheory
namespace PaperFormalization.Manuscript
variable {G Ω Ξ E : Type*} [MeasurableSpace G] [MeasurableSpace Ω] [MeasurableSpace Ξ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

set_option maxHeartbeats 1600000 in
/-- One measurable common event under unchanged ρ⊗k controls the actual raw
residual on every labelled branch and localized eligible history. The common
AE model predicate is retained with no extra probability loss. -/
theorem exists_conditional_uniform_gamma_event
    (ρ : Measure G) [IsProbabilityMeasure ρ]
    (k : Kernel G Ξ) [IsMarkovKernel k] (μ : Kernel G Ω) [IsMarkovKernel μ]
    (PopGood : Set G) (hPopGood : MeasurableSet PopGood)
    (Model : G × Ξ → Prop) (hModel : ∀ᵐ z ∂(ρ ⊗ₘ k), Model z)
    (L N : ℕ) (hN : 0 < N) (a b : Fin (L+1) → ℝ) (hab : ∀ j, a j ≤ b j)
    (T : ℝ) (hlen : ∀ j, b j-a j ≤ T) (B : ℝ≥0)
    (Y : Fin (L+1) → G → Ω → ℝ → E)
    (X : Fin (L+1) → G × Ξ → Fin N → ℝ → E)
    (hY : ∀ j t, t ∈ Icc (a j) (b j) →
      Measurable (fun z : G × Ω => Y j z.1 z.2 t))
    (hX : ∀ j t, t ∈ Icc (a j) (b j) → ∀ i,
      Measurable (fun z => X j z i t))
    (C g q alpha K D c₀ K₀ M : ℝ) (hC : 0 ≤ C) (hK : 0 < K) (hD : 0 ≤ D)
    (hc₀ : 0 ≤ c₀) (hK₀ : 0 < K₀) (halpha : 0 ≤ alpha)
    (w : ℕ → ℝ≥0) (φ : ∀ n, E → H n) (hφ : ∀ n, ContDiff ℝ 1 (φ n))
    (hvalue : ∀ n z, ‖φ n z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ (n+1)))
    (hderiv : ∀ n z, ‖fderiv ℝ (φ n) z‖ ≤ featureGrowth C g q n * (1 + ‖z‖ ^ n))
    (hpop : ∀ᵐ h ∂ρ, h ∈ PopGood →
      (∀ j, ∀ᵐ ω ∂μ h, LipschitzOnWith B (Y j h ω) (Icc (a j) (b j))) ∧
      ∀ j t, t ∈ Icc (a j) (b j) →
        (μ h).map (fun ω => Y j h ω t) ∈ sourceMomentClass alpha K ∧
        Integrable (fun z => Real.exp (c₀ * (‖z‖/K₀)^alpha)) ((μ h).map (fun ω => Y j h ω t)) ∧
        (∫ z, Real.exp (c₀ * (‖z‖/K₀)^alpha) ∂(μ h).map (fun ω => Y j h ω t)) ≤ M)
    (hsamplePath : ∀ᵐ z ∂(ρ ⊗ₘ k), z.1 ∈ PopGood →
      ∀ j i, LipschitzOnWith B (X j z i) (Icc (a j) (b j)))
    (hLaw : ∀ j t, t ∈ Icc (a j) (b j) → ∀ᵐ h ∂ρ, h ∈ PopGood → ∀ i,
      (k h).map (fun ξ => X j (h,ξ) i t) = (μ h).map (fun ω => Y j h ω t))
    (hind : ∀ j t, t ∈ Icc (a j) (b j) → ∀ᵐ h ∂ρ, h ∈ PopGood →
      iIndepFun (fun i ξ => X j (h,ξ) i t) (k h))
    (Local : Set (G × Ξ))
    (hlocal : ∀ z ∈ Local, ∀ j t, t ∈ Icc (a j) (b j) → ∀ i, ‖X j z i t‖ ≤ D)
    (hA : Summable (fun n => (w n : ℝ) * (featureGrowth C g q n * (1 + D ^ (n+1)))))
    (hΛ : Summable (fun n => (w n : ℝ) * (featureGrowth C g q n * (1 + 2 * D ^ n))))
    (hS : Summable (fun n => (w n : ℝ) * sourceCoordinateL2Envelope C g q alpha K n))
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    let A := 2 * ∑' n, (w n : ℝ) * (featureGrowth C g q n * (1 + D ^ (n+1)))
    let Λ := ∑' n, (w n : ℝ) * (featureGrowth C g q n * (1 + 2 * D ^ n))
    let S := ∑' n, (w n : ℝ) * sourceCoordinateL2Envelope C g q alpha K n
    let beta := 2 * S * Real.sqrt M * Real.exp (-(c₀ * (D/K₀)^alpha)/2)
    let Q := (((L+1 : ℕ) : ℝ) * ((N+1 : ℕ) : ℝ))
    ∃ Good : Set (G × Ξ), MeasurableSet Good ∧ (ρ ⊗ₘ k).real Goodᶜ ≤ p ∧
      ∀ z ∈ Good, Model z ∧ (z.1 ∈ PopGood → z ∈ Local →
        ∀ j t, t ∈ Icc (a j) (b j) →
          weightedSampleResidual w φ
            (fun n => ∫ x, φ n x ∂(μ z.1).map (fun ω => Y j z.1 ω t)) (fun i => X j z i t) ≤
          beta + A / Real.sqrt N + A * Real.sqrt (Real.log (Q/p)/(2*N)) +
            2 * (B : ℝ) * T * Λ / N) := by
  let A := 2 * ∑' n, (w n : ℝ) * (featureGrowth C g q n * (1 + D ^ (n+1)))
  let Λ := ∑' n, (w n : ℝ) * (featureGrowth C g q n * (1 + 2 * D ^ n))
  let S := ∑' n, (w n : ℝ) * sourceCoordinateL2Envelope C g q alpha K n
  let beta := 2 * S * Real.sqrt M * Real.exp (-(c₀ * (D/K₀)^alpha)/2)
  let Q := (((L+1 : ℕ) : ℝ) * ((N+1 : ℕ) : ℝ))
  let r := A / Real.sqrt N + A * Real.sqrt (Real.log (Q/p)/(2*N))
  let κ := fun j t => conditionalPathMarginal μ (fun h ω => Y j h ω t)
  have hk j t (ht : t ∈ Icc (a j) (b j)) : IsMarkovKernel (κ j t) ∧
      ∀ h, κ j t h = (μ h).map (fun ω => Y j h ω t) :=
    conditionalPathMarginal_properties μ (fun h ω => Y j h ω t) (hY j t ht)
  let F := fun j z t => weightedClippedSampleResidual (κ j t z.1) D w φ (fun i => X j z i t)
  let R := fun j z t => weightedSampleResidual w φ
    (fun n => ∫ x, φ n x ∂(μ z.1).map (fun ω => Y j z.1 ω t)) (fun i => X j z i t)
  let Pop : G → Prop := fun h => h ∈ PopGood →
      (∀ j, ∀ᵐ ω ∂μ h, LipschitzOnWith B (Y j h ω) (Icc (a j) (b j))) ∧
      ∀ j t, t ∈ Icc (a j) (b j) →
        (μ h).map (fun ω => Y j h ω t) ∈ sourceMomentClass alpha K ∧
        Integrable (fun z => Real.exp (c₀ * (‖z‖/K₀)^alpha)) ((μ h).map (fun ω => Y j h ω t)) ∧
        (∫ z, Real.exp (c₀ * (‖z‖/K₀)^alpha) ∂(μ h).map (fun ω => Y j h ω t)) ≤ M
  let Paths : G × Ξ → Prop := fun z => z.1 ∈ PopGood →
      ∀ j i, LipschitzOnWith B (X j z i) (Icc (a j) (b j))
  let Actual : G × Ξ → Prop := fun z => Model z ∧ Pop z.1 ∧ Paths z
  let Eligible : Set (G × Ξ) := {z | z.1 ∈ PopGood}
  have hfst : MeasurePreserving (Prod.fst : G × Ξ → G) (ρ ⊗ₘ k) ρ :=
    ⟨measurable_fst, Measure.fst_compProd ρ k⟩
  have hactual : ∀ᵐ z ∂(ρ ⊗ₘ k), Actual z := by
    filter_upwards [hModel, hfst.quasiMeasurePreserving.ae hpop, hsamplePath] with z hm hp hx
    exact ⟨hm, hp, hx⟩
  have hL (n : ℕ) : 0 ≤ featureGrowth C g q n := featureGrowth_nonneg C g q hC n
  have hΛ0 : 0 ≤ Λ := tsum_nonneg (fun n => mul_nonneg (w n).coe_nonneg
    (mul_nonneg (hL n) (by positivity)))
  let rate := Real.toNNReal (2 * (B : ℝ) * Λ)
  have hrate : (rate : ℝ) = 2 * (B : ℝ) * Λ := Real.coe_toNNReal _ (by positivity)
  have hF : ∀ j z, Actual z → z ∈ Eligible → z ∈ Local →
      LipschitzOnWith rate (F j z) (Icc (a j) (b j)) := by
    intro j z hz he _hl
    have hlip := (clippedResidualPath_summable_lipschitzOn (μ z.1) (Y j z.1) (X j z)
      hN D hD B (Icc (a j) (b j)) w (featureGrowth C g q) hL φ hφ hvalue hderiv
      (fun t ht => ((hY j t ht).comp measurable_prodMk_left).aestronglyMeasurable)
      ((hz.2.1 he).1 j) (hz.2.2 he j) hA hΛ).2
    intro t ht u hu
    dsimp only [F]
    rw [(hk j t ht).2 z.1, (hk j u hu).2 z.1]
    exact hlip ht hu
  have hraw : ∀ j z, Actual z → z ∈ Eligible → z ∈ Local →
      ∀ t ∈ Icc (a j) (b j), R j z t ≤ F j z t + beta := by
    intro j z hz he hl t ht
    obtain ⟨hclass, hexp, hM⟩ := (hz.2.1 he).2 j t ht
    dsimp only [R,F]
    rw [(hk j t ht).2 z.1]
    exact source_weighted_unclipping_exp_le hN C g q alpha K D c₀ K₀ M hC hK hD hc₀ hK₀ halpha
      ((μ z.1).map (fun ω => Y j z.1 ω t)) hclass hexp hM w φ
      (fun n => (hφ n).continuous) hvalue hA hS (fun i => X j z i t) (hlocal z hl j t ht)
  have hQ1 : 1 ≤ Q := by dsimp [Q]; norm_cast; nlinarith
  have hQ : 0 < Q := lt_of_lt_of_le zero_lt_one hQ1
  have hmeas j i : Measurable (fun z => F j z (closedBranchGrid (a j) (b j) N i)) := by
    let t := closedBranchGrid (a j) (b j) N i
    have ht : t ∈ Icc (a j) (b j) := closedBranchGrid_mem (a j) (b j) (hab j) hN i
    exact measurable_kernel_weightedClippedSampleResidual (κ j t) (fun z i => X j z i t)
      (hX j t ht) D hD w φ (fun n => (hφ n).continuous)
  have hnode j i : (ρ ⊗ₘ k).real {z | z ∈ Eligible ∧
      r < F j z (closedBranchGrid (a j) (b j) N i)} ≤ p/Q := by
    let t := closedBranchGrid (a j) (b j) N i
    have ht : t ∈ Icc (a j) (b j) := closedBranchGrid_mem (a j) (b j) (hab j) hN i
    letI : IsMarkovKernel (κ j t) := (hk j t ht).1
    have hlaw : ∀ᵐ h ∂ρ, h ∈ PopGood → ∀ i,
        (k h).map (fun ξ => X j (h,ξ) i t) = κ j t h := by
      filter_upwards [hLaw j t ht] with h hh
      intro he i
      exact (hh he i).trans ((hk j t ht).2 h).symm
    exact joint_kernel_clipped_source_node_budget ρ k (κ j t) PopGood hPopGood
      (fun z i => X j z i t) (hX j t ht) hN hlaw (hind j t ht) D hD w
      (featureGrowth C g q) (fun n => n+1) hL φ (fun n => (hφ n).continuous)
      hvalue hA Q p hQ hp (hp1.trans_le hQ1)
  obtain ⟨Good, hGood, hbudget, hbound⟩ := exists_eligible_finite_branch_event (ρ ⊗ₘ k)
    Eligible Local (hPopGood.preimage measurable_fst) Actual hactual L N hN a b hab T hlen
    rate F R hF beta r p hraw hmeas hnode
  refine ⟨Good, hGood, hbudget, ?_⟩
  intro z hz
  refine ⟨(hbound z hz).1.1, ?_⟩
  intro he hl j t ht
  have hb := (hbound z hz).2 he hl j t ht
  have heq : beta + r + (rate : ℝ) * (T/N) =
      beta + A / Real.sqrt N + A * Real.sqrt (Real.log (Q/p)/(2*N)) +
        2 * (B : ℝ) * T * Λ/N := by
    rw [hrate]
    dsimp [r]
    ring
  exact hb.trans_eq heq
end PaperFormalization.Manuscript
