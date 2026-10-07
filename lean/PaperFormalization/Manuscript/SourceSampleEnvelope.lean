import PaperFormalization.Manuscript.UniformSourceFourthMoment
import PaperFormalization.Manuscript.FeatureRegularityBounds

/-! # The literal derivative-energy threshold at sampled particles

The threshold is exactly max 1 [d sum a_n² L_(n+1)² (1+R^n)²].
Its convergence, actual source derivative domination on the R-ball, and
uniform logarithmic-exponential growth are derived. This deterministic unit
does not assert a sampled or conditional probability law.
-/

open scoped BigOperators

namespace PaperFormalization.Manuscript

/-- The source sampled derivative-energy threshold, at radius R. -/
noncomputable def sourceSampleHilbertSchmidtEnvelope
    (d : ℕ) (c C g p q R : ℝ) : ℝ :=
  max 1 ((d : ℝ) * ∑' n, (sourceFeatureScale c p n) ^ 2 *
    (featureGrowth C g q n) ^ 2 * (1 + R ^ n) ^ 2)

/-- The unsquared derivative-radius majorant is genuinely summable. -/
theorem summable_source_derivative_radius_majorant (c C g p q R : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hR : 0 ≤ R) :
    Summable (fun n => featureWeight c C g p q n * (1 + R ^ n)) := by
  apply (summable_feature_regularity_envelope c C g p q (1 + R) hc hp hq (by linarith)).of_nonneg_of_le
  · intro n
    exact mul_nonneg (featureWeight_nonneg c C g p q hC n) (by positivity)
  · intro n
    apply mul_le_mul_of_nonneg_left _ (featureWeight_nonneg c C g p q hC n)
    have hpow := (pow_le_pow_left₀ hR (by linarith : R ≤ 1 + R) n).trans
      (pow_le_pow_right₀ (by linarith : 1 ≤ 1 + R) (Nat.le_succ n))
    change R ^ n ≤ (1 + R) ^ (n + 1) at hpow
    linarith

/-- The exact squared series in the threshold converges, including R=0. -/
theorem summable_source_derivative_radius_energy (c C g p q R : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hR : 0 ≤ R) :
    Summable (fun n => (sourceFeatureScale c p n) ^ 2 *
      (featureGrowth C g q n) ^ 2 * (1 + R ^ n) ^ 2) := by
  let b := fun n => featureWeight c C g p q n * (1 + R ^ n)
  have hb : Summable b := summable_source_derivative_radius_majorant c C g p q R hc hC hp hq hR
  have hb0 : 0 ≤ b := by
    intro n
    exact mul_nonneg (featureWeight_nonneg c C g p q hC n) (by positivity)
  have hs := (hb.mul_of_nonneg hb hb0 hb0).comp_injective
    (i := fun n : ℕ => (n,n)) (by intro a b h; exact congrArg Prod.fst h)
  apply hs.congr
  intro n
  simp only [Function.comp_def, b, sourceFeatureScale, featureGrowth, featureWeight]
  ring

/-- The sample threshold is always at least one, even in dimension zero. -/
theorem one_le_sourceSampleHilbertSchmidtEnvelope (d : ℕ) (c C g p q R : ℝ) :
    1 ≤ sourceSampleHilbertSchmidtEnvelope d c C g p q R := le_max_left _ _

section Actual
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

/-- Actual derivative energy on the source radius ball is below the literal
sample threshold. Neither an energy bound nor a kernel norm bound is assumed. -/
theorem source_hilbertSchmidt_energy_le_sampleEnvelope
    (c C g p q R : ℝ) (φ : ∀ n, EuclideanSpace ℝ ι → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hR : 0 ≤ R)
    (hφ : ∀ n, ContDiff ℝ 2 (φ n))
    (hgrowth : ∀ n x k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) x‖ ≤
      featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1 - k)))
    (x : EuclideanSpace ℝ ι) (hx : ‖x‖ ≤ R) :
    finiteHilbertSchmidtNorm (fderiv ℝ (sourceWeightedFeatureMap c p φ) x) ^ 2 ≤
      sourceSampleHilbertSchmidtEnvelope (Fintype.card ι) c C g p q R := by
  have hcoord (n : ℕ) : (sourceFeatureScale c p n) ^ 2 *
      finiteHilbertSchmidtNorm (fderiv ℝ (φ n) x) ^ 2 ≤
      (Fintype.card ι : ℝ) * ((sourceFeatureScale c p n) ^ 2 *
        (featureGrowth C g q n) ^ 2 * (1 + R ^ n) ^ 2) := by
    have hD : ‖fderiv ℝ (φ n) x‖ ≤ featureGrowth C g q n * (1 + R ^ n) := by
      have h := hgrowth n x 1 (by omega)
      simp only [norm_iteratedFDeriv_one, Nat.add_sub_cancel] at h
      exact h.trans (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (pow_le_pow_left₀ (norm_nonneg _) hx n))
        (featureGrowth_nonneg C g q hC n))
    have hHS := (finiteHilbertSchmidtNorm_le_sqrt_card_mul (fderiv ℝ (φ n) x)).trans
      (mul_le_mul_of_nonneg_left hD (Real.sqrt_nonneg _))
    have hsq := pow_le_pow_left₀ (finiteHilbertSchmidtNorm_nonneg _) hHS 2
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at hsq
    have h := mul_le_mul_of_nonneg_left hsq (sq_nonneg (sourceFeatureScale c p n))
    exact h.trans_eq (by ring)
  have hs := hasSum_source_fderiv_hilbertSchmidt_energy c C g p q φ hc hC hp hq hφ hgrowth x
  have ht := (summable_source_derivative_radius_energy c C g p q R hc hC hp hq hR).mul_left
    (Fintype.card ι : ℝ)
  have hsum := hs.summable.tsum_le_tsum hcoord ht
  rw [hs.tsum_eq, tsum_mul_left] at hsum
  exact hsum.trans (le_max_right _ _)
end Actual

/-- The unsquared radius series has a uniform chi(R) bound; constants are
chosen before R, using only fixed feature parameters. -/
theorem exists_uniform_sourceDerivativeRadius_series_bound (c C g p q : ℝ)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) :
    ∃ M : ℝ, 0 < M ∧ ∀ R : ℝ, 0 ≤ R →
      (∑' n, featureWeight c C g p q n * (1 + R ^ n)) ≤
        M * Real.exp (M * featureScaleChi p R) := by
  obtain ⟨A, hA, hbound⟩ := exists_uniform_feature_series_bound c C g p q 1
    hc hC hp hq (by norm_num)
  let B : ℝ := (1 + Real.log (1 + 2)) ^ (p / (p - 1))
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Real.rpow_nonneg (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 1 + 2)]) _
  let M : ℝ := A * (B + 1) + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hAM : A ≤ M := by dsimp [M]; nlinarith
  have hABM : A * B ≤ M := by dsimp [M]; nlinarith
  refine ⟨M, hM, ?_⟩
  intro R hR
  have ht (n : ℕ) : featureWeight c C g p q n * (1 + R ^ n) ≤
      featureWeight c C g p q n * (2 + (1 + R) ^ (n + 1) + (1 : ℝ) ^ (n + 1) *
        ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / 1)) := by
    apply mul_le_mul_of_nonneg_left _ (featureWeight_nonneg c C g p q hC n)
    have hpow := (pow_le_pow_left₀ hR (by linarith : R ≤ 1 + R) n).trans
      (pow_le_pow_right₀ (by linarith : 1 ≤ 1 + R) (Nat.le_succ n))
    change R ^ n ≤ (1 + R) ^ (n + 1) at hpow
    have hn : 0 ≤ (1 : ℝ) ^ (n + 1) *
        ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) / 1) := by positivity
    linarith
  have hsum := (summable_source_derivative_radius_majorant c C g p q R hc hC hp hq hR).tsum_le_tsum ht
    (summable_feature_amplitude c C g p q 1 (1 + R) 1 hc hp hq (by norm_num) (by linarith))
  have hchi := featureScaleChi_scale_le p 1 R hp (by norm_num) hR
  change featureScaleChi p (1 * (1 + R) + 1) ≤ B * featureScaleChi p R at hchi
  have hchi0 : 0 ≤ featureScaleChi p R := (by norm_num : (0 : ℝ) ≤ 1).trans
    (one_le_featureScaleChi p R hp hR)
  calc
    _ ≤ A * Real.exp (A * featureScaleChi p (1 + (1 + R))) :=
      hsum.trans (hbound 1 (by norm_num) (1 + R) (by linarith))
    _ ≤ A * Real.exp ((A * B) * featureScaleChi p R) := by
      apply mul_le_mul_of_nonneg_left _ hA.le
      apply Real.exp_le_exp.mpr
      have he : 1 + (1 + R) = 1 * (1 + R) + 1 := by ring
      rw [he]
      nlinarith [mul_le_mul_of_nonneg_left hchi hA.le]
    _ ≤ M * Real.exp (M * featureScaleChi p R) :=
      mul_le_mul hAM (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hABM hchi0))
        (Real.exp_pos _).le hM.le

/-- The literal sample threshold grows uniformly like exp(C chi(R)), with
its dimension factor explicit and its constant fixed before d and R. -/
theorem exists_uniform_sourceSampleHilbertSchmidtEnvelope_dim_bound
    (c C g p q : ℝ) (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) :
    ∃ M : ℝ, 0 < M ∧ ∀ d : ℕ, ∀ R : ℝ, 0 ≤ R →
      sourceSampleHilbertSchmidtEnvelope d c C g p q R ≤
        (1 + (d : ℝ)) * (M * Real.exp (M * featureScaleChi p R)) := by
  obtain ⟨A, hA, hbound⟩ := exists_uniform_sourceDerivativeRadius_series_bound c C g p q hc hC hp hq
  let M : ℝ := 1 + A ^ 2 + 2 * A
  have hM : 0 < M := by dsimp [M]; positivity
  have hM1 : 1 ≤ M := by dsimp [M]; nlinarith [sq_nonneg A]
  have hcoef : A ^ 2 ≤ M := by dsimp [M]; linarith
  have hexp : 2 * A ≤ M := by dsimp [M]; nlinarith [sq_nonneg A]
  refine ⟨M, hM, ?_⟩
  intro d R hR
  let b := fun n => featureWeight c C g p q n * (1 + R ^ n)
  have hb := summable_source_derivative_radius_majorant c C g p q R hc hC hp hq hR
  have hb0 (n : ℕ) : 0 ≤ b n := mul_nonneg (featureWeight_nonneg c C g p q hC n) (by positivity)
  have hS : 0 ≤ ∑' n, b n := tsum_nonneg hb0
  have hsq := tsum_sq_le_sq_tsum_nonneg b hb hb0
  have hid (n : ℕ) : (sourceFeatureScale c p n) ^ 2 * (featureGrowth C g q n) ^ 2 *
      (1 + R ^ n) ^ 2 = b n ^ 2 := by
    dsimp [b, sourceFeatureScale, featureGrowth, featureWeight]
    ring
  have hchi0 : 0 ≤ featureScaleChi p R := (by norm_num : (0 : ℝ) ≤ 1).trans
    (one_le_featureScaleChi p R hp hR)
  have hmain : (∑' n, b n ^ 2) ≤ M * Real.exp (M * featureScaleChi p R) := by
    calc
      _ ≤ (∑' n, b n) ^ 2 := hsq
      _ ≤ (A * Real.exp (A * featureScaleChi p R)) ^ 2 :=
        pow_le_pow_left₀ hS (hbound R hR) 2
      _ = A ^ 2 * Real.exp ((2 * A) * featureScaleChi p R) := by
        simp only [mul_pow, ← Real.exp_nat_mul, Nat.cast_ofNat, mul_assoc]
      _ ≤ _ := mul_le_mul hcoef
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hexp hchi0)) (Real.exp_pos _).le hM.le
  have hupper0 : 0 ≤ M * Real.exp (M * featureScaleChi p R) := by positivity
  have hupper1 : 1 ≤ M * Real.exp (M * featureScaleChi p R) :=
    one_le_mul_of_one_le_of_one_le hM1 (Real.one_le_exp (mul_nonneg hM.le hchi0))
  unfold sourceSampleHilbertSchmidtEnvelope
  simp_rw [hid]
  apply max_le
  · nlinarith [mul_nonneg (Nat.cast_nonneg d) hupper0]
  · have h := mul_le_mul_of_nonneg_left hmain (Nat.cast_nonneg d)
    nlinarith

end PaperFormalization.Manuscript
