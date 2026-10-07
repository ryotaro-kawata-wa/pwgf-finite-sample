import PaperFormalization.Manuscript.SourceSampleEnvelope
import PaperFormalization.Manuscript.SourceMomentTail

/-! # The exact source sampled-energy maximum event

The radius and threshold are the literal source R_(N,delta) and tau_(N,delta).
Individual real-order Markov tails and a finite union bound are proved under
the unchanged population and sample laws. Independence is not needed for this
maximum event. Conditional-law identification remains a separate application.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PaperFormalization.Manuscript

/-- The exact sampled-radius choice from the source moment calculation. -/
noncomputable def sourceSampleRadius (N : ℕ) (alpha K delta : ℝ) : ℝ :=
  K * (Real.exp 1 * max alpha 1 * (1 + Real.log (8 * N / delta))) ^ (1 / alpha)

/-- The sampled radius is strictly positive on the source parameter domain. -/
theorem sourceSampleRadius_pos (N : ℕ) (alpha K delta : ℝ)
    (hN : 0 < N) (hK : 0 < K) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    0 < sourceSampleRadius N alpha K delta := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hratio : 1 ≤ 8 * (N : ℝ) / delta :=
    (le_div_iff₀ hdelta).mpr (by nlinarith)
  have hlog : 0 ≤ Real.log (8 * (N : ℝ) / delta) := Real.log_nonneg hratio
  have hmax : 0 < max alpha 1 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  unfold sourceSampleRadius
  exact mul_pos hK (Real.rpow_pos_of_pos (by positivity) _)

section Moment
variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
  [BorelSpace E] [SecondCountableTopology E]

/-- At radius K(er)^(1/alpha), the actual all-real-order moment hypothesis
has the exact tail exp(-r/alpha), with no exponential-moment premise. -/
theorem sourceMomentClass_norm_tail_momentRadius_le
    (alpha K r : ℝ) (hK : 0 < K) (hr : 1 ≤ r)
    (μ : Measure E) (hμ : μ ∈ sourceMomentClass alpha K) :
    μ.real {x | K * (Real.exp 1 * r) ^ (1 / alpha) < ‖x‖} ≤
      Real.exp (-r / alpha) := by
  have hr0 : 0 < r := by linarith
  have hR : 0 < K * (Real.exp 1 * r) ^ (1 / alpha) := by positivity
  have ht := sourceMomentClass_norm_tail_le alpha K _ r hK hR hr μ hμ
  have he : K * r ^ (1 / alpha) / (K * (Real.exp 1 * r) ^ (1 / alpha)) =
      Real.exp (-(1 / alpha)) := by
    rw [Real.mul_rpow (Real.exp_pos _).le hr0.le, Real.exp_one_rpow, Real.exp_neg]
    field_simp
  rw [he, ← Real.exp_mul] at ht
  exact ht.trans_eq (congrArg Real.exp (by ring))

/-- The exact source radius gives the individual original-law tail delta/(8N). -/
theorem sourceMomentClass_norm_tail_sampleRadius_le
    (N : ℕ) (alpha K delta : ℝ) (hN : 0 < N)
    (halpha : 0 < alpha) (hK : 0 < K) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (μ : Measure E) (hμ : μ ∈ sourceMomentClass alpha K) :
    μ.real {x | sourceSampleRadius N alpha K delta < ‖x‖} ≤ delta / (8 * N) := by
  let r := max alpha 1 * (1 + Real.log (8 * (N : ℝ) / delta))
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hratio : 1 ≤ 8 * (N : ℝ) / delta :=
    (le_div_iff₀ hdelta).mpr (by nlinarith)
  have hratio0 : 0 < 8 * (N : ℝ) / delta := lt_of_lt_of_le zero_lt_one hratio
  have hlog : 0 ≤ Real.log (8 * (N : ℝ) / delta) := Real.log_nonneg hratio
  have hr : 1 ≤ r := one_le_mul_of_one_le_of_one_le (le_max_right _ _) (by linarith)
  have hpower : -(r / alpha) ≤ -Real.log (8 * (N : ℝ) / delta) := by
    apply neg_le_neg
    apply (le_div_iff₀ halpha).mpr
    have h := mul_le_mul_of_nonneg_right (le_max_left alpha 1)
      (by linarith : 0 ≤ 1 + Real.log (8 * (N : ℝ) / delta))
    change _ ≤ r
    dsimp [r] at *
    nlinarith
  have ht := sourceMomentClass_norm_tail_momentRadius_le alpha K r hK hr μ hμ
  have hRadius : K * (Real.exp 1 * r) ^ (1 / alpha) = sourceSampleRadius N alpha K delta := by
    dsimp [sourceSampleRadius, r]
    congr 2
    ring
  rw [hRadius] at ht
  calc
    _ ≤ Real.exp (-r / alpha) := ht
    _ ≤ Real.exp (-Real.log (8 * (N : ℝ) / delta)) :=
      Real.exp_le_exp.mpr (by simpa only [neg_div] using hpower)
    _ = delta / (8 * N) := by rw [Real.exp_neg, Real.exp_log hratio0, inv_div]
end Moment

section Source
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

/-- The actual source derivative-energy tail is below delta/(8N) at the
literal source threshold. The implication is derived from actual feature growth. -/
theorem sourceMomentClass_hilbertSchmidt_sampleEnvelope_tail_le
    (N : ℕ) (c C g p q alpha K delta : ℝ) (φ : ∀ n, EuclideanSpace ℝ ι → H n)
    (hN : 0 < N) (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (halpha : 0 < alpha) (hK : 0 < K) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hφ : ∀ n, ContDiff ℝ 2 (φ n))
    (hgrowth : ∀ n x k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) x‖ ≤
      featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1 - k)))
    (μ : Measure (EuclideanSpace ℝ ι)) (hμ : μ ∈ sourceMomentClass alpha K) :
    μ.real {x | sourceSampleHilbertSchmidtEnvelope (Fintype.card ι) c C g p q
      (sourceSampleRadius N alpha K delta) <
        finiteHilbertSchmidtNorm (fderiv ℝ (sourceWeightedFeatureMap c p φ) x) ^ 2} ≤
      delta / (8 * N) := by
  letI : IsProbabilityMeasure μ := hμ.1
  have hR := sourceSampleRadius_pos N alpha K delta hN hK hdelta hdelta1
  have hs : {x | sourceSampleHilbertSchmidtEnvelope (Fintype.card ι) c C g p q
      (sourceSampleRadius N alpha K delta) <
        finiteHilbertSchmidtNorm (fderiv ℝ (sourceWeightedFeatureMap c p φ) x) ^ 2} ⊆
      {x | sourceSampleRadius N alpha K delta < ‖x‖} := by
    intro x hx
    by_contra hn
    exact (not_lt_of_ge (source_hilbertSchmidt_energy_le_sampleEnvelope c C g p q
      (sourceSampleRadius N alpha K delta) φ hc hC hp hq hR.le hφ hgrowth x
      (le_of_not_gt hn))) hx
  exact (measureReal_mono hs).trans
    (sourceMomentClass_norm_tail_sampleRadius_le N alpha K delta hN halpha hK hdelta hdelta1 μ hμ)

/-- Under the original sample-system law, the actual maximum event costs at
most delta/8. Only each particle's genuine common marginal law is needed. -/
theorem source_hilbertSchmidt_sample_max_tail_le
    {Ω : Type*} [MeasurableSpace Ω] (N : ℕ)
    (c C g p q alpha K delta : ℝ) (φ : ∀ n, EuclideanSpace ℝ ι → H n)
    (hN : 0 < N) (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (halpha : 0 < alpha) (hK : 0 < K) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hφ : ∀ n, ContDiff ℝ 2 (φ n))
    (hgrowth : ∀ n x k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) x‖ ≤
      featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1 - k)))
    (μ : Measure (EuclideanSpace ℝ ι)) (hμ : μ ∈ sourceMomentClass alpha K)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (Y : Fin N → Ω → EuclideanSpace ℝ ι)
    (hLaw : ∀ i, ν.map (Y i) = μ) :
    ν.real {ω | ∃ i, sourceSampleHilbertSchmidtEnvelope (Fintype.card ι) c C g p q
      (sourceSampleRadius N alpha K delta) < finiteHilbertSchmidtNorm
        (fderiv ℝ (sourceWeightedFeatureMap c p φ) (Y i ω)) ^ 2} ≤ delta / 8 := by
  letI : IsProbabilityMeasure μ := hμ.1
  let A := fderiv ℝ (sourceWeightedFeatureMap c p φ)
  let tau := sourceSampleHilbertSchmidtEnvelope (Fintype.card ι) c C g p q
    (sourceSampleRadius N alpha K delta)
  have hA : Continuous A :=
    (contDiff_sourceWeightedFeatureMap c C g p q φ hc hC hp hq hφ hgrowth).continuous_fderiv (by norm_num)
  have hmeas : MeasurableSet {x | tau < finiteHilbertSchmidtNorm (A x) ^ 2} :=
    measurableSet_lt measurable_const (continuous_hilbertSchmidt_energy A hA).measurable
  have htail := sourceMomentClass_hilbertSchmidt_sampleEnvelope_tail_le N c C g p q alpha K delta φ
    hN hc hC hp hq halpha hK hdelta hdelta1 hφ hgrowth μ hμ
  have hi (i : Fin N) : ν.real {ω | tau < finiteHilbertSchmidtNorm (A (Y i ω)) ^ 2} ≤
      delta / (8 * N) := by
    have hY : AEMeasurable (Y i) ν :=
      aemeasurable_of_map_neZero (by rw [hLaw i]; infer_instance)
    have he := map_measureReal_apply_of_aemeasurable hY hmeas
    rw [hLaw i] at he
    exact he ▸ htail
  have hunion := measureReal_iUnion_fintype_le (μ := ν)
    (fun i : Fin N => {ω | tau < finiteHilbertSchmidtNorm (A (Y i ω)) ^ 2})
  have hevent : {ω | ∃ i, tau < finiteHilbertSchmidtNorm (A (Y i ω)) ^ 2} =
      ⋃ i : Fin N, {ω | tau < finiteHilbertSchmidtNorm (A (Y i ω)) ^ 2} := by ext ω; simp
  change ν.real {ω | ∃ i, tau < finiteHilbertSchmidtNorm (A (Y i ω)) ^ 2} ≤ _
  rw [hevent]
  calc
    _ ≤ ∑ i : Fin N, ν.real {ω | tau < finiteHilbertSchmidtNorm (A (Y i ω)) ^ 2} := hunion
    _ ≤ ∑ _i : Fin N, delta / (8 * N) := Finset.sum_le_sum (fun i _ => hi i)
    _ = delta / 8 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
      field_simp
end Source

end PaperFormalization.Manuscript
