import PaperFormalization.Manuscript.SourceDerivativeFourthMoment
import PaperFormalization.Manuscript.SourceDerivativeHilbertSchmidt
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-! # The exact source Hilbert--Schmidt fourth-moment coefficient

The displayed coefficient uses the original population moment scale K and
source m=n+1. Any enlarged scale appears only in a convergence proof. The
actual scalar coordinate energies are summed by finite L2 Minkowski and Fatou.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace PaperFormalization.Manuscript

/-- The literal source derivative-coordinate fourth-moment factor, including m=1. -/
noncomputable def sourceDerivativeL4Factor (alpha K : ℝ) (n : ℕ) : ℝ :=
  1 + K ^ n * (max (4 * (n : ℝ)) 1) ^ ((n : ℝ) / alpha)

/-- The manuscript's exact C_Phi,4, with explicit input dimension d. -/
noncomputable def sourceHilbertSchmidtFourthMoment (d : ℕ) (c C g p q alpha K : ℝ) : ℝ :=
  ((d : ℝ) * ∑' n, (sourceFeatureScale c p n) ^ 2 * (featureGrowth C g q n) ^ 2 *
    (sourceDerivativeL4Factor alpha K n) ^ 2) ^ 2

/-- The previous-order natural-power form is exactly the source max(4n,1)
real-power form; at n=0 both displayed factors are 2. -/
theorem sourceDerivativeL4Factor_eq (alpha K : ℝ) (n : ℕ) :
    sourceDerivativeL4Factor alpha K n = 1 + (K * (4 * (n : ℝ)) ^ (1 / alpha)) ^ n := by
  cases n with
  | zero => simp [sourceDerivativeL4Factor]
  | succ n =>
      have h4 : 1 ≤ 4 * ((n + 1 : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
      rw [sourceDerivativeL4Factor, max_eq_left h4, mul_pow]
      congr 2
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1
      ring

/-- Exact coefficient summability. The pre-existing enlarged scale is used
only to prove convergence, while this series retains the original K. -/
theorem summable_sourceHilbertSchmidtFourth_summands
    (c C g p q alpha K : ℝ) (hc : 0 < c) (hC : 0 ≤ C)
    (hp : 1 < p) (hq : q < p) (halpha : 0 < alpha) (hK : 0 < K) :
    Summable (fun n => (sourceFeatureScale c p n) ^ 2 * (featureGrowth C g q n) ^ 2 *
      (sourceDerivativeL4Factor alpha K n) ^ 2) := by
  let b := fun n => featureWeight c C g p q n *
    (1 + (K * (4 * (n : ℝ)) ^ (1 / alpha)) ^ n)
  have hb : Summable b := summable_source_derivative_L4_majorant c C g p q alpha K
    hc hC hp hq halpha hK
  have hb0 : 0 ≤ b := by
    intro n
    exact mul_nonneg (featureWeight_nonneg c C g p q hC n) (by positivity)
  have hs := (hb.mul_of_nonneg hb hb0 hb0).comp_injective
    (i := fun n : ℕ => (n,n)) (by intro a b h; exact congrArg Prod.fst h)
  apply hs.congr
  intro n
  simp only [Function.comp_def, b, sourceDerivativeL4Factor_eq,
    sourceFeatureScale, featureGrowth, featureWeight]
  ring

/-- Finite L2 Minkowski and Fatou give an exact summable-majorant bound for
an actual pointwise series. No Lp norm bound for its sum is assumed. -/
theorem eLpNorm_two_le_of_hasSum_majorant
    {Ω F : Type*} [MeasurableSpace Ω] [NormedAddCommGroup F]
    (μ : Measure Ω) (f : ℕ → Ω → F) (g : Ω → F) (b : ℕ → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hb0 : ∀ n, 0 ≤ b n) (hb : Summable b)
    (hbound : ∀ n, eLpNorm (f n) 2 μ ≤ ENNReal.ofReal (b n))
    (hsum : ∀ x, HasSum (fun n => f n x) (g x)) :
    eLpNorm g 2 μ ≤ ENNReal.ofReal (∑' n, b n) := by
  apply Lp.eLpNorm_le_of_ae_tendsto
    (f := fun k x => ∑ n ∈ Finset.range k, f n x)
    (hf := fun k => Finset.aestronglyMeasurable_fun_sum _ (fun n _ => hf n))
    (h_tendsto := Filter.Eventually.of_forall (fun x => (hsum x).tendsto_sum_nat))
  filter_upwards with k
  calc
    _ ≤ ∑ n ∈ Finset.range k, eLpNorm (f n) 2 μ := by
      simpa only [Finset.sum_fn] using
        eLpNorm_sum_le (s := Finset.range k) (fun n _ => hf n) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    _ ≤ ∑ n ∈ Finset.range k, ENNReal.ofReal (b n) :=
      Finset.sum_le_sum (fun n _ => hbound n)
    _ = ENNReal.ofReal (∑ n ∈ Finset.range k, b n) :=
      (ENNReal.ofReal_sum_of_nonneg (fun n _ => hb0 n)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hb.sum_le_tsum (Finset.range k) (fun n _ => hb0 n))

/-- Squaring a scalar L4 envelope gives the exact L2 squared envelope. -/
theorem eLpNorm_sq_two_le_of_four
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hf : eLpNorm f 4 μ ≤ ENNReal.ofReal B) :
    eLpNorm (fun x => f x ^ 2) 2 μ ≤ ENNReal.ofReal (B ^ 2) := by
  have he := eLpNorm_norm_rpow (p := 2) (μ := μ) f (by norm_num : (0 : ℝ) < 2)
  have he' : eLpNorm (fun x => f x ^ 2) 2 μ = eLpNorm f 4 μ ^ (2 : ℕ) := by
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs, ENNReal.ofReal_ofNat,
      show (2 : ℝ≥0∞) * 2 = 4 by norm_num, ENNReal.rpow_two] using he
  rw [he', ENNReal.ofReal_pow hB]
  exact pow_le_pow_left₀ (by positivity) hf 2

/-- Multiplying a real L2 envelope by a nonnegative scalar preserves its exact bound. -/
theorem eLpNorm_const_mul_two_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ)
    (a B : ℝ) (ha : 0 ≤ a) (hf : eLpNorm f 2 μ ≤ ENNReal.ofReal B) :
    eLpNorm (fun x => a * f x) 2 μ ≤ ENNReal.ofReal (a * B) := by
  change eLpNorm (a • f) 2 μ ≤ _
  rw [eLpNorm_const_smul, ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ha,
    ENNReal.ofReal_mul ha]
  exact mul_le_mul_right hf _

section Source

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

/-- The squared genuine finite-column norm varies continuously with a
continuous operator family, without a separability assumption on its target. -/
theorem continuous_hilbertSchmidt_energy
    {E F : Type*} [TopologicalSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (A : E → (EuclideanSpace ℝ ι →L[ℝ] F))
    (hA : Continuous A) : Continuous (fun x => finiteHilbertSchmidtNorm (A x) ^ 2) := by
  simp_rw [finiteHilbertSchmidtNorm_sq]
  exact continuous_finsetSum _ (fun j _ =>
    ((hA.clm_apply continuous_const).norm.pow 2))

set_option maxHeartbeats 800000 in
/-- Exact L2 bound for the actual full derivative energy. The coefficient
retains the original population K and the single input-dimension factor. -/
theorem sourceMomentClass_eLpNorm_hilbertSchmidt_energy_two_le
    (c C g p q alpha K : ℝ) (φ : ∀ n, EuclideanSpace ℝ ι → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (halpha : 0 < alpha) (hK : 0 < K)
    (hφ : ∀ n, ContDiff ℝ 2 (φ n))
    (hgrowth : ∀ n x k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) x‖ ≤
      featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1 - k)))
    (μ : Measure (EuclideanSpace ℝ ι)) (hμ : μ ∈ sourceMomentClass alpha K) :
    eLpNorm (fun x => finiteHilbertSchmidtNorm
      (fderiv ℝ (sourceWeightedFeatureMap c p φ) x) ^ 2) 2 μ ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ) * ∑' n,
        (sourceFeatureScale c p n) ^ 2 * (featureGrowth C g q n) ^ 2 *
          (sourceDerivativeL4Factor alpha K n) ^ 2) := by
  let d : ℝ := Fintype.card ι
  let a := sourceFeatureScale c p
  let w := featureWeight c C g p q
  let f : ℕ → EuclideanSpace ℝ ι → ℝ := fun n x =>
    (a n) ^ 2 * finiteHilbertSchmidtNorm (fderiv ℝ (φ n) x) ^ 2
  let b : ℕ → ℝ := fun n => d * ((a n) ^ 2 * (featureGrowth C g q n) ^ 2 *
    (sourceDerivativeL4Factor alpha K n) ^ 2)
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hw (n : ℕ) : 0 ≤ w n := featureWeight_nonneg c C g p q hC n
  have ha (n : ℕ) : 0 ≤ a n := (sourceFeatureScale_pos c p n).le
  have haw (n : ℕ) : a n * featureGrowth C g q n = w n := by
    simp only [a, w, sourceFeatureScale, featureGrowth, featureWeight, mul_assoc]
  have hpoint (n : ℕ) (x : EuclideanSpace ℝ ι) :
      ‖f n x‖ ≤ d * (w n * (1 + ‖x‖ ^ n)) ^ 2 := by
    have hD : ‖fderiv ℝ (φ n) x‖ ≤ featureGrowth C g q n * (1 + ‖x‖ ^ n) := by
      simpa only [norm_iteratedFDeriv_one, Nat.add_sub_cancel] using hgrowth n x 1 (by omega)
    have hHS := finiteHilbertSchmidtNorm_le_sqrt_card_mul (fderiv ℝ (φ n) x)
    have hsq := pow_le_pow_left₀ (finiteHilbertSchmidtNorm_nonneg _) hHS 2
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at hsq
    calc
      _ = (a n) ^ 2 * finiteHilbertSchmidtNorm (fderiv ℝ (φ n) x) ^ 2 :=
        Real.norm_of_nonneg (by positivity)
      _ ≤ (a n) ^ 2 * (d * ‖fderiv ℝ (φ n) x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = d * (a n * ‖fderiv ℝ (φ n) x‖) ^ 2 := by ring
      _ ≤ d * (w n * (1 + ‖x‖ ^ n)) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hd
        apply pow_le_pow_left₀ (mul_nonneg (ha n) (norm_nonneg _))
        calc
          _ ≤ a n * (featureGrowth C g q n * (1 + ‖x‖ ^ n)) :=
            mul_le_mul_of_nonneg_left hD (ha n)
          _ = _ := by rw [← mul_assoc, haw]
  have hf (n : ℕ) : AEStronglyMeasurable (f n) μ := by
    exact (continuous_const.mul (continuous_hilbertSchmidt_energy _
      ((hφ n).continuous_fderiv (by norm_num)))).aestronglyMeasurable
  have hb0 (n : ℕ) : 0 ≤ b n := by dsimp [b]; positivity
  have hb : Summable b :=
    (summable_sourceHilbertSchmidtFourth_summands c C g p q alpha K
      hc hC hp hq halpha hK).mul_left d
  have hbound (n : ℕ) : eLpNorm (f n) 2 μ ≤ ENNReal.ofReal (b n) := by
    have hL4 := sourceMomentClass_eLpNorm_weighted_envelope_four_le
      alpha K hK μ hμ (w n) (hw n) n
    have hL2 := eLpNorm_sq_two_le_of_four μ (fun x => w n * (1 + ‖x‖ ^ n))
      (w n * (1 + (K * (4 * (n : ℝ)) ^ (1 / alpha)) ^ n)) (mul_nonneg (hw n) (by positivity)) hL4
    calc
      _ ≤ eLpNorm (fun x : EuclideanSpace ℝ ι => d * (w n * (1 + ‖x‖ ^ n)) ^ 2) 2 μ :=
        eLpNorm_mono_ae_real (Filter.Eventually.of_forall (hpoint n))
      _ ≤ ENNReal.ofReal (d *
          ((w n * (1 + (K * (4 * (n : ℝ)) ^ (1 / alpha)) ^ n)) ^ 2)) :=
        eLpNorm_const_mul_two_le μ _ d _ hd hL2
      _ = ENNReal.ofReal (b n) := by
        congr 1
        dsimp [b]
        rw [sourceDerivativeL4Factor_eq, ← haw]
        ring
  have hs := eLpNorm_two_le_of_hasSum_majorant μ f _ b hf hb0 hb hbound
    (hasSum_source_fderiv_hilbertSchmidt_energy c C g p q φ hc hC hp hq hφ hgrowth)
  simpa only [b, tsum_mul_left, d] using hs

set_option maxHeartbeats 800000 in
/-- The actual derivative has a genuine fourth Hilbert--Schmidt moment,
bounded by the literal source C_Phi,4 with the original K and input dimension. -/
theorem sourceMomentClass_hilbertSchmidt_fourth_moment_le
    (c C g p q alpha K : ℝ) (φ : ∀ n, EuclideanSpace ℝ ι → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (halpha : 0 < alpha) (hK : 0 < K)
    (hφ : ∀ n, ContDiff ℝ 2 (φ n))
    (hgrowth : ∀ n x k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) x‖ ≤
      featureGrowth C g q n * (1 + ‖x‖ ^ (n + 1 - k)))
    (μ : Measure (EuclideanSpace ℝ ι)) (hμ : μ ∈ sourceMomentClass alpha K) :
    Integrable (fun x => finiteHilbertSchmidtNorm
      (fderiv ℝ (sourceWeightedFeatureMap c p φ) x) ^ 4) μ ∧
      (∫ x, finiteHilbertSchmidtNorm (fderiv ℝ (sourceWeightedFeatureMap c p φ) x) ^ 4 ∂μ) ≤
        sourceHilbertSchmidtFourthMoment (Fintype.card ι) c C g p q alpha K := by
  let e : EuclideanSpace ℝ ι → ℝ := fun x => finiteHilbertSchmidtNorm
    (fderiv ℝ (sourceWeightedFeatureMap c p φ) x) ^ 2
  let B : ℝ := (Fintype.card ι : ℝ) * ∑' n,
    (sourceFeatureScale c p n) ^ 2 * (featureGrowth C g q n) ^ 2 *
      (sourceDerivativeL4Factor alpha K n) ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb : eLpNorm e 2 μ ≤ ENNReal.ofReal B :=
    sourceMomentClass_eLpNorm_hilbertSchmidt_energy_two_le
      c C g p q alpha K φ hc hC hp hq halpha hK hφ hgrowth μ hμ
  have hm : MemLp e 2 μ := ⟨
    (continuous_hilbertSchmidt_energy _
      ((contDiff_sourceWeightedFeatureMap c C g p q φ hc hC hp hq hφ hgrowth).continuous_fderiv
        (by norm_num))).aestronglyMeasurable, hb.trans_lt ENNReal.ofReal_lt_top⟩
  have hid (x : EuclideanSpace ℝ ι) : ‖e x‖ ^ 2 = finiteHilbertSchmidtNorm
      (fderiv ℝ (sourceWeightedFeatureMap c p φ) x) ^ 4 := by
    dsimp [e]
    rw [abs_of_nonneg (sq_nonneg _)]
    ring
  refine ⟨by simpa only [hid] using hm.integrable_norm_pow (by norm_num), ?_⟩
  have hs : Real.sqrt (∫ x, ‖e x‖ ^ 2 ∂μ) ≤ B := by
    rw [hm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)] at hb
    simpa only [ENNReal.toReal_ofNat, one_div, invOf_eq_inv, Real.rpow_two,
      Real.sqrt_eq_rpow, ENNReal.ofReal_le_ofReal_iff hB] using hb
  have hsq := Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg ‖e x‖) :
    0 ≤ ∫ x, ‖e x‖ ^ 2 ∂μ)
  have hle : (∫ x, ‖e x‖ ^ 2 ∂μ) ≤ B ^ 2 := by
    nlinarith [Real.sqrt_nonneg (∫ x, ‖e x‖ ^ 2 ∂μ)]
  simpa only [hid, B, sourceHilbertSchmidtFourthMoment] using hle

end Source

end PaperFormalization.Manuscript
