import PaperFormalization.Manuscript.UniformSourceCoefficients
import PaperFormalization.Manuscript.SourceClippedSeries

/-! # Uniform envelopes for the literal Gamma coefficients

The clipping amplitude and the exact order-2m population bias series are
compared to the source radius. Fixed rescaling of K is accounted for before
K,D are quantified; it is not absorbed into a K-dependent constant.
-/
open scoped NNReal
namespace PaperFormalization.Manuscript

/-- Literal clipped amplitude A is bounded by twice L times the source radius. -/
theorem sourceClippingAmplitude_le_radius (c C g p q K D alpha : ℝ) (L : ℝ≥0)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (hD : 1 ≤ D) :
    2 * (∑' n, (featureResidualWeight c p L n : ℝ) *
      (featureGrowth C g q n * (1 + D ^ (n + 1)))) ≤
      2 * (L : ℝ) * sourceMomentRadius c C g p q K D alpha := by
  have hs := (summable_sourceMomentRadius_summand c C g p q K D alpha hc hp hq hK hD).mul_left (L : ℝ)
  have ht : ∀ n, (featureResidualWeight c p L n : ℝ) *
      (featureGrowth C g q n * (1 + D ^ (n + 1))) ≤
      (L : ℝ) * (featureWeight c C g p q n *
        (2 + D ^ (n + 1) + K ^ (n + 1) *
          ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha))) := by
    intro n
    rw [featureResidualWeight_coe]
    have hw := featureWeight_nonneg c C g p q hC n
    have hpop : 0 ≤ K ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha) := by positivity
    calc
      _ = (L : ℝ) * featureWeight c C g p q n * (1 + D ^ (n + 1)) := by
        unfold featureGrowth featureWeight
        ring
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg L.coe_nonneg hw) hpop]
  have hb := (summable_source_clipped_amplitude c C g p q D L hc hp hq hD).tsum_le_tsum ht hs
  rw [tsum_mul_left] at hb
  unfold sourceMomentRadius
  nlinarith [L.coe_nonneg]

/-- The exact S coefficient uses the original order-2m envelope. The sole
rescaling K*2^(1/alpha) is displayed explicitly. -/
theorem sourceClippingL2Envelope_le_scaled_radius (c C g p q K D alpha : ℝ) (L : ℝ≥0)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (hD : 1 ≤ D) :
    (∑' n, (featureResidualWeight c p L n : ℝ) *
      sourceCoordinateL2Envelope C g q alpha K n) ≤
      (L : ℝ) * sourceMomentRadius c C g p q (K * (2 : ℝ) ^ (1 / alpha)) D alpha := by
  let Ks := K * (2 : ℝ) ^ (1 / alpha)
  have hKs : 0 < Ks := by dsimp [Ks]; positivity
  have hs := (summable_sourceMomentRadius_summand c C g p q Ks D alpha hc hp hq hKs hD).mul_left (L : ℝ)
  have ht : ∀ n, (featureResidualWeight c p L n : ℝ) *
      sourceCoordinateL2Envelope C g q alpha K n ≤
      (L : ℝ) * (featureWeight c C g p q n *
        (2 + D ^ (n + 1) + Ks ^ (n + 1) *
          ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha))) := by
    intro n
    rw [sourceCoordinateL2Envelope_eq_scaled_moment, featureResidualWeight_coe]
    have hw := featureWeight_nonneg c C g p q hC n
    have hpow : 0 ≤ D ^ (n + 1) := pow_nonneg (by linarith) _
    calc
      _ = (L : ℝ) * featureWeight c C g p q n *
          (1 + Ks ^ (n + 1) * ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / alpha)) := by
        unfold featureGrowth featureWeight
        dsimp [Ks]
        ring
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg L.coe_nonneg hw) hpow]
  have hb := (summable_source_clipping_L2_envelope c C g p q alpha K L hc hp hq hK).tsum_le_tsum ht hs
  rw [tsum_mul_left] at hb
  unfold sourceMomentRadius
  change _ ≤ (L : ℝ) * (1 + _)
  nlinarith [L.coe_nonneg]

/-- Chi is monotone on its nonnegative source domain. -/
theorem featureScaleChi_mono_nonneg (p u v : ℝ) (hp : 1 < p) (hu : 0 ≤ u) (huv : u ≤ v) :
    featureScaleChi p u ≤ featureScaleChi p v := by
  apply Real.rpow_le_rpow
  · exact (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_featureScaleLog u hu)
  · exact Real.log_le_log (by positivity) (by linarith)
  · positivity

/-- Any fixed positive rescaling of the population radius retains the
uniform chi(K+D) envelope, with its constant chosen before K,D. -/
theorem exists_uniform_scaled_sourceMomentRadius_bound (c C g p q alpha s : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (halpha : 0 < alpha) (hs : 0 < s) :
    ∃ M : ℝ, 0 < M ∧ ∀ K : ℝ, 0 < K → ∀ D : ℝ, 1 ≤ D →
      sourceMomentRadius c C g p q (s*K) D alpha ≤
        M * Real.exp (M * featureScaleChi p (K+D)) := by
  obtain ⟨A,hA,hbound⟩ := exists_uniform_sourceMomentRadius_bound c C g p q alpha hc hC hp hq halpha
  let B := (1 + Real.log (s + 3)) ^ (p / (p - 1))
  have hB : 0 ≤ B := by
    dsimp [B]
    apply Real.rpow_nonneg
    linarith [Real.log_nonneg (by linarith : 1 ≤ s + 3)]
  let M := 1 + A + A*B
  have hM : 0 < M := by dsimp [M]; positivity
  have hAM : A ≤ M := by dsimp [M]; nlinarith
  have hABM : A*B ≤ M := by dsimp [M]; linarith
  refine ⟨M,hM,?_⟩
  intro K hK D hD
  have hchi0 : 0 ≤ featureScaleChi p (K+D) :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_featureScaleChi p (K+D) hp (by linarith))
  have hchi : featureScaleChi p (s*K+D) ≤ B * featureScaleChi p (K+D) := by
    calc
      _ ≤ featureScaleChi p ((s+1)*(1+(K+D))+1) :=
        featureScaleChi_mono_nonneg p _ _ hp (by positivity) (by nlinarith)
      _ ≤ _ := by simpa only [B, show s+1+2=s+3 by ring] using
        featureScaleChi_scale_le p (s+1) (K+D) hp (by linarith) (by linarith)
  calc
    _ ≤ A * Real.exp (A * featureScaleChi p (s*K+D)) := hbound (s*K) (by positivity) D hD
    _ ≤ A * Real.exp ((A*B) * featureScaleChi p (K+D)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hchi hA.le])) hA.le
    _ ≤ M * Real.exp (M * featureScaleChi p (K+D)) :=
      mul_le_mul hAM (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hABM hchi0)) (Real.exp_pos _).le hM.le


section Objective
variable {E : Type*} [Zero E] {H : ℕ → Type*}
  [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℝ (H n)]

/-- All three literal Gamma coefficients have one uniform source-scale bound.
The nonnegative L parameter may equal the absolute actual comparison envelope;
the conclusion is uniform over every smaller L as well. -/
theorem exists_uniform_source_gamma_coefficients_bound
    (c C g p q alpha C3 : ℝ) (φ : ∀ n, E → H n) (G : lp H 2 → ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (halpha : 0 < alpha) :
    ∃ M : ℝ, 0 < M ∧ ∀ K : ℝ, 0 < K → ∀ D : ℝ, 1 ≤ D → ∀ L : ℝ≥0,
      (L : ℝ) ≤ |sourceComparisonEnvelope c C g p q K D alpha C3 φ G| →
      (2 * ∑' n, (featureResidualWeight c p L n : ℝ) *
        (featureGrowth C g q n * (1 + D ^ (n+1)))) ≤
          M * Real.exp (M * featureScaleChi p (K+D)) ∧
      featureDisplacementLambda c C g p q D L ≤
          M * Real.exp (M * featureScaleChi p (K+D)) ∧
      (∑' n, (featureResidualWeight c p L n : ℝ) *
        sourceCoordinateL2Envelope C g q alpha K n) ≤
          M * Real.exp (M * featureScaleChi p (K+D)) := by
  obtain ⟨A,hA,hRa⟩ := exists_uniform_sourceMomentRadius_bound c C g p q alpha hc hC hp hq halpha
  obtain ⟨B,hB,hRb⟩ := exists_uniform_scaled_sourceMomentRadius_bound
    c C g p q alpha ((2 : ℝ) ^ (1/alpha)) hc hC hp hq halpha (by positivity)
  obtain ⟨J,hJ,hLj⟩ := exists_uniform_sourceComparisonEnvelope_bound
    c C g p q alpha C3 φ G hc hC hp hq halpha
  let U := A+B+J
  have hU : 0 < U := by dsimp [U]; positivity
  have hAU : A ≤ U := by dsimp [U]; linarith
  have hBU : B ≤ U := by dsimp [U]; linarith
  have hJU : J ≤ U := by dsimp [U]; linarith
  let M := 1 + 2*U^2 + 2*U
  have hM : 0 < M := by dsimp [M]; positivity
  have hcoef : 2*U^2 ≤ M := by dsimp [M]; linarith
  have hpower : 2*U ≤ M := by dsimp [M]; nlinarith [sq_nonneg U]
  refine ⟨M,hM,?_⟩
  intro K hK D hD L hL
  have hχ : 0 ≤ featureScaleChi p (K+D) :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_featureScaleChi p (K+D) hp (by linarith))
  have enlarge (a : ℝ) (ha : a ≤ U) :
      a * Real.exp (a * featureScaleChi p (K+D)) ≤
      U * Real.exp (U * featureScaleChi p (K+D)) :=
    mul_le_mul ha (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ha hχ)) (Real.exp_pos _).le hU.le
  have hR : sourceMomentRadius c C g p q K D alpha ≤ U * Real.exp (U * featureScaleChi p (K+D)) :=
    (hRa K hK D hD).trans (enlarge A hAU)
  have hRs : sourceMomentRadius c C g p q (K * (2 : ℝ) ^ (1/alpha)) D alpha ≤
      U * Real.exp (U * featureScaleChi p (K+D)) := by
    simpa only [mul_comm K] using (hRb K hK D hD).trans (enlarge B hBU)
  have hLs : (L : ℝ) ≤ U * Real.exp (U * featureScaleChi p (K+D)) :=
    hL.trans ((hLj K hK D hD).trans (enlarge J hJU))
  have product_bound (R : ℝ) (hR0 : 0 ≤ R)
      (hRb : R ≤ U * Real.exp (U * featureScaleChi p (K+D))) :
      2*(L : ℝ)*R ≤ M * Real.exp (M * featureScaleChi p (K+D)) := by
    calc
      _ ≤ 2*(U * Real.exp (U * featureScaleChi p (K+D))) *
          (U * Real.exp (U * featureScaleChi p (K+D))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hLs (by norm_num)) hRb hR0 (by positivity)
      _ = (2*U^2) * Real.exp ((2*U) * featureScaleChi p (K+D)) := by
        rw [show (2*U) * featureScaleChi p (K+D) =
          U * featureScaleChi p (K+D) + U * featureScaleChi p (K+D) by ring, Real.exp_add]
        ring
      _ ≤ _ := mul_le_mul hcoef (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hpower hχ)) (Real.exp_pos _).le hM.le
  have hR0 : 0 ≤ sourceMomentRadius c C g p q K D alpha :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_sourceMomentRadius c C g p q K D alpha hC hK.le (by linarith))
  have hRs0 : 0 ≤ sourceMomentRadius c C g p q (K * (2 : ℝ) ^ (1/alpha)) D alpha :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_sourceMomentRadius c C g p q _ D alpha hC (by positivity) (by linarith))
  refine ⟨(sourceClippingAmplitude_le_radius c C g p q K D alpha L hc hC hp hq hK hD).trans
    (product_bound _ hR0 hR),
    (featureDisplacementLambda_le_radius c C g p q K D alpha L hc hC hp hq hK hD).trans
    (product_bound _ hR0 hR), ?_⟩
  apply (sourceClippingL2Envelope_le_scaled_radius c C g p q K D alpha L hc hC hp hq hK hD).trans
  exact (show (L : ℝ) * sourceMomentRadius c C g p q (K * (2 : ℝ) ^ (1/alpha)) D alpha ≤
    2*(L : ℝ)*sourceMomentRadius c C g p q (K * (2 : ℝ) ^ (1/alpha)) D alpha by
      nlinarith [mul_nonneg L.coe_nonneg hRs0]).trans (product_bound _ hRs0 hRs)
end Objective
end PaperFormalization.Manuscript
