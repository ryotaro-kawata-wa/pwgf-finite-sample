import PaperFormalization.Manuscript.GaussianSquareMoment
import PaperFormalization.Manuscript.JumpComparison
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Gaussian norm tails from actual scalar Gaussian laws

Finite Jensen and the genuine Gaussian square moment are used; independence
of the scalar coordinates is not needed. Degenerate variances are retained.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace PaperFormalization.Manuscript

/-- Scaling an actual standard Gaussian by sqrt(v) gives its centered law,
including the degenerate zero-variance law. -/
theorem standardGaussian_map_sqrt_mul (v : ℝ≥0) :
    (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt v * x) = gaussianReal 0 v := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · ring
  · ext
    simp only [NNReal.coe_mk, mul_one, Real.sq_sqrt v.coe_nonneg]

/-- Every centered Gaussian variance has its genuine square-exponential
moment, including variance zero. -/
theorem exp_sq_moment_of_centeredGaussian_law
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (v : ℝ≥0)
    (hX : μ.map X = gaussianReal 0 v) (t : ℝ) (ht : 2 * t * (v : ℝ) < 1) :
    Integrable (fun ω => Real.exp (t * (X ω) ^ 2)) μ ∧
      (∫ ω, Real.exp (t * (X ω) ^ 2) ∂μ) = (Real.sqrt (1 - 2 * t * (v : ℝ)))⁻¹ := by
  have hXm : AEMeasurable X μ := aemeasurable_of_map_neZero (by rw [hX]; infer_instance)
  have hmoment : (∫ ω, Real.exp (t * (X ω) ^ 2) ∂μ) =
      (Real.sqrt (1 - 2 * t * (v : ℝ)))⁻¹ := by
    rw [← integral_map (f := fun x : ℝ => Real.exp (t * x ^ 2)) hXm (by fun_prop), hX,
      ← standardGaussian_map_sqrt_mul v,
      integral_map (f := fun x : ℝ => Real.exp (t * x ^ 2)) (by fun_prop) (by fun_prop)]
    simp_rw [mul_pow, Real.sq_sqrt v.coe_nonneg, ← mul_assoc]
    convert integral_exp_sq_standardGaussian (t * v) (by nlinarith) using 1; ring_nf
  have hden : 0 < 1 - 2 * t * (v : ℝ) := by linarith
  exact ⟨Integrable.of_integral_ne_zero (by rw [hmoment]; positivity), hmoment⟩

/-- Zero Gaussian variance means the coordinate is actually zero almost
surely under the unchanged original measure. -/
theorem ae_eq_zero_of_gaussian_zero_law
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ)
    (hX : μ.map X = gaussianReal 0 0) : ∀ᵐ ω ∂μ, X ω = 0 := by
  have hXm : AEMeasurable X μ := aemeasurable_of_map_neZero (by rw [hX]; infer_instance)
  apply ae_of_ae_map (p := fun x : ℝ => x = 0) hXm
  rw [hX, gaussianReal_zero_var]
  simp

/-- Finite Jensen yields the exponential-square bound from actual centered
Gaussian coordinate laws. Coordinates may be correlated and variances zero. -/
theorem finite_gaussian_exp_sum_sq_bound
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (X : ι → Ω → ℝ) (v : ι → ℝ≥0)
    (hX : ∀ i, μ.map (X i) = gaussianReal 0 (v i))
    (t : ℝ) (hS : 0 < ∑ i, (v i : ℝ)) (ht : 2 * t * (∑ i, (v i : ℝ)) < 1) :
    Integrable (fun ω => Real.exp (t * ∑ i, (X i ω) ^ 2)) μ ∧
      (∫ ω, Real.exp (t * ∑ i, (X i ω) ^ 2) ∂μ) ≤
        (Real.sqrt (1 - 2 * t * (∑ i, (v i : ℝ))))⁻¹ := by
  classical
  let S : ℝ := ∑ i, (v i : ℝ)
  let w : ι → ℝ := fun i => (v i : ℝ) / S
  let a : ι → Ω → ℝ := fun i ω => (t * S / (v i : ℝ)) * (X i ω) ^ 2
  let F : Ω → ℝ := fun ω => Real.exp (t * ∑ i, (X i ω) ^ 2)
  let G : Ω → ℝ := fun ω => ∑ i, w i * Real.exp (a i ω)
  have hS0 : S ≠ 0 := hS.ne'
  have hw : ∀ i, 0 ≤ w i := fun i => div_nonneg (v i).coe_nonneg hS.le
  have hwsum : ∑ i, w i = 1 := by
    dsimp [w]
    rw [← Finset.sum_div]
    exact div_self hS0
  have hXm : ∀ i, AEMeasurable (X i) μ := fun i =>
    aemeasurable_of_map_neZero (by rw [hX i]; infer_instance)
  have hzero : ∀ᵐ ω ∂μ, ∀ i, v i = 0 → X i ω = 0 := by
    rw [ae_all_iff]
    intro i
    by_cases hi : v i = 0
    · filter_upwards [ae_eq_zero_of_gaussian_zero_law μ (X i) (by simpa only [hi] using hX i)] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall (fun _ h => (hi h).elim)
  have hentry : ∀ i, Integrable (fun ω => Real.exp (a i ω)) μ := by
    intro i
    apply (exp_sq_moment_of_centeredGaussian_law μ (X i) (v i) (hX i)
      (t * S / (v i : ℝ)) ?_).1
    by_cases hi : v i = 0
    · simp [hi]
    · have hvi : (v i : ℝ) ≠ 0 := by exact_mod_cast hi
      have he : 2 * (t * S / (v i : ℝ)) * (v i : ℝ) = 2 * t * S := by field_simp
      rw [he]
      exact ht
  have hGint : Integrable G μ :=
    integrable_finsetSum _ (fun i _ => (hentry i).const_mul (w i))
  have hGval : (∫ ω, G ω ∂μ) = (Real.sqrt (1 - 2 * t * S))⁻¹ := by
    rw [show (∫ ω, G ω ∂μ) = ∑ i, ∫ ω, w i * Real.exp (a i ω) ∂μ from
      integral_finsetSum _ (fun i _ => (hentry i).const_mul (w i))]
    calc
      _ = ∑ i, w i * (Real.sqrt (1 - 2 * t * S))⁻¹ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_const_mul]
        by_cases hi : v i = 0
        · simp [w, hi]
        · congr 1
          have hvi : (v i : ℝ) ≠ 0 := by exact_mod_cast hi
          have he : 2 * (t * S / (v i : ℝ)) * (v i : ℝ) = 2 * t * S := by field_simp
          have h := (exp_sq_moment_of_centeredGaussian_law μ (X i) (v i) (hX i)
            (t * S / (v i : ℝ)) (by rw [he]; exact ht)).2
          simpa only [a, he] using h
      _ = _ := by rw [← Finset.sum_mul, hwsum, one_mul]
  have hFG : ∀ᵐ ω ∂μ, F ω ≤ G ω := by
    filter_upwards [hzero] with ω hω
    have hsum : ∑ i, w i * a i ω = t * ∑ i, (X i ω) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : v i = 0
      · simp [w, a, hi, hω i hi]
      · have hvi : (v i : ℝ) ≠ 0 := by exact_mod_cast hi
        dsimp [w, a]
        field_simp
    have hJ := convexOn_exp.map_sum_le (t := Finset.univ) (w := w) (p := fun i => a i ω)
      (fun i _ => hw i) hwsum (fun _ _ => mem_univ _)
    simpa only [smul_eq_mul, hsum] using hJ
  have hFmeas : AEStronglyMeasurable F μ := by
    apply AEMeasurable.aestronglyMeasurable
    dsimp [F]
    fun_prop
  have hFint : Integrable F μ := hGint.mono_nonneg hFmeas
    (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)) hFG
  exact ⟨hFint, (integral_mono_ae hFint hGint hFG).trans_eq hGval⟩

/-- The optimized scalar Chernoff factor is bounded by the source Gaussian
exponent; the only estimate is log(q)≤q−1. -/
theorem gaussian_chernoff_factor_le (q : ℝ) (hq : 0 < q) :
    Real.exp (-q * (q - 1) / 2) * Real.sqrt q ≤ Real.exp (-(q - 1) ^ 2 / 2) := by
  have hsqrt : Real.sqrt q ≤ Real.exp ((q - 1) / 2) := by
    calc
      _ = Real.exp (Real.log (Real.sqrt q)) := (Real.exp_log (Real.sqrt_pos.2 hq)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by
        rw [Real.log_sqrt hq.le]
        linarith [Real.log_le_sub_one_of_pos hq])
  calc
    _ ≤ Real.exp (-q * (q - 1) / 2) * Real.exp ((q - 1) / 2) :=
      mul_le_mul_of_nonneg_left hsqrt (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Optimizing the genuine square moment gives the dimension-free quadratic
tail when total variance is positive. -/
theorem finite_gaussian_sum_sq_tail_of_pos
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ι → Ω → ℝ) (v : ι → ℝ≥0)
    (hX : ∀ i, μ.map (X i) = gaussianReal 0 (v i))
    (q : ℝ) (hq : 1 < q) (hS : 0 < ∑ i, (v i : ℝ)) :
    μ.real {ω | q ^ 2 * (∑ i, (v i : ℝ)) < ∑ i, (X i ω) ^ 2} ≤
      Real.exp (-(q - 1) ^ 2 / 2) := by
  let S : ℝ := ∑ i, (v i : ℝ)
  let t : ℝ := (q - 1) / (2 * q * S)
  have hq0 : 0 < q := by linarith
  have hS0 : S ≠ 0 := hS.ne'
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hfactor : 1 - 2 * t * S = q⁻¹ := by dsimp [t]; field_simp; ring
  have hsmall : 2 * t * S < 1 := by linarith [inv_pos.mpr hq0]
  have hmgf := finite_gaussian_exp_sum_sq_bound μ X v hX t hS hsmall
  have hmgf' : mgf (fun ω => ∑ i, (X i ω) ^ 2) μ t ≤ Real.sqrt q := by
    have hbound : mgf (fun ω => ∑ i, (X i ω) ^ 2) μ t ≤ (Real.sqrt (1 - 2 * t * S))⁻¹ := hmgf.2
    simpa only [hfactor, Real.sqrt_inv, inv_inv] using hbound
  have hmarkov := measure_ge_le_exp_mul_mgf (μ := μ) (X := fun ω => ∑ i, (X i ω) ^ 2)
    (q ^ 2 * S) ht hmgf.1
  have hexponent : -t * (q ^ 2 * S) = -q * (q - 1) / 2 := by
    dsimp [t]
    field_simp
  calc
    _ ≤ μ.real {ω | q ^ 2 * S ≤ ∑ i, (X i ω) ^ 2} := measureReal_mono (fun ω (h : q ^ 2 * S < ∑ i, (X i ω) ^ 2) => h.le)
    _ ≤ Real.exp (-t * (q ^ 2 * S)) * mgf (fun ω => ∑ i, (X i ω) ^ 2) μ t := hmarkov
    _ ≤ Real.exp (-q * (q - 1) / 2) * Real.sqrt q := by
      rw [hexponent]
      exact mul_le_mul_of_nonneg_left hmgf' (Real.exp_pos _).le
    _ ≤ _ := gaussian_chernoff_factor_le q hq0

/-- The same quadratic tail retains total-variance zero: then every Gaussian
coordinate is zero almost surely, so the strict failure event is null. -/
theorem finite_gaussian_sum_sq_tail
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ι → Ω → ℝ) (v : ι → ℝ≥0)
    (hX : ∀ i, μ.map (X i) = gaussianReal 0 (v i)) (q : ℝ) (hq : 1 < q) :
    μ.real {ω | q ^ 2 * (∑ i, (v i : ℝ)) < ∑ i, (X i ω) ^ 2} ≤
      Real.exp (-(q - 1) ^ 2 / 2) := by
  have hS : 0 ≤ ∑ i, (v i : ℝ) := Finset.sum_nonneg (fun i _ => (v i).coe_nonneg)
  rcases hS.eq_or_lt with hS | hS
  · have hv : ∀ i, v i = 0 := by
      intro i
      apply NNReal.coe_eq_zero.mp
      have hle : (v i : ℝ) ≤ ∑ j, (v j : ℝ) := Finset.single_le_sum
        (fun j _ => (v j).coe_nonneg) (Finset.mem_univ i)
      exact le_antisymm (by linarith) (v i).coe_nonneg
    have hzero : ∀ᵐ ω ∂μ, ∀ i, X i ω = 0 := by
      rw [ae_all_iff]
      intro i
      exact ae_eq_zero_of_gaussian_zero_law μ (X i) (by simpa only [hv i] using hX i)
    have hevent : μ {ω | q ^ 2 * (∑ i, (v i : ℝ)) < ∑ i, (X i ω) ^ 2} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hzero] with ω hω
      simp only [← hS, mul_zero, hω, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, Finset.sum_const_zero, lt_self_iff_false, not_false_eq_true]
    rw [measureReal_def, hevent, ENNReal.toReal_zero]
    exact (Real.exp_pos _).le
  · exact finite_gaussian_sum_sq_tail_of_pos μ X v hX q hq hS

/-- The source q(u)=1+sqrt(2log(2/u)) has failure probability at most u/2,
derived from the actual Gaussian laws and valid also for zero total variance. -/
theorem finite_gaussian_sum_sq_source_tail
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ι → Ω → ℝ) (v : ι → ℝ≥0)
    (hX : ∀ i, μ.map (X i) = gaussianReal 0 (v i))
    (u : ℝ) (hu : 0 < u) (hu1 : u < 1) :
    μ {ω | (sourceGaussianDeviation u) ^ 2 * (∑ i, (v i : ℝ)) < ∑ i, (X i ω) ^ 2} ≤
      ENNReal.ofReal (u / 2) := by
  have hlog : 0 < Real.log (2 / u) := Real.log_pos ((lt_div_iff₀ hu).mpr (by linarith))
  have hq : 1 < sourceGaussianDeviation u := by
    unfold sourceGaussianDeviation
    linarith [Real.sqrt_pos.2 (by positivity : 0 < 2 * Real.log (2 / u))]
  have h := finite_gaussian_sum_sq_tail μ X v hX (sourceGaussianDeviation u) hq
  have hexp : Real.exp (-(sourceGaussianDeviation u - 1) ^ 2 / 2) = u / 2 := by
    unfold sourceGaussianDeviation
    rw [add_sub_cancel_left, Real.sq_sqrt (by positivity)]
    convert source_gaussian_exponential_half_budget u hu using 1; congr 1; ring
  rw [hexp] at h
  simpa only [ofReal_measureReal (measure_ne_top μ _)] using ENNReal.ofReal_le_ofReal h

/-- The literal Euclidean norm event obeys the source half-budget. Only its
centered Gaussian coordinate laws are needed, so arbitrary covariance and
zero total variance are allowed. -/
theorem finite_gaussian_norm_source_tail
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → EuclideanSpace ℝ ι) (v : ι → ℝ≥0)
    (hX : ∀ i, μ.map (fun ω => X ω i) = gaussianReal 0 (v i))
    (u : ℝ) (hu : 0 < u) (hu1 : u < 1) :
    μ {ω | sourceGaussianDeviation u * Real.sqrt (∑ i, (v i : ℝ)) < ‖X ω‖} ≤
      ENNReal.ofReal (u / 2) := by
  have hS : 0 ≤ ∑ i, (v i : ℝ) := Finset.sum_nonneg (fun i _ => (v i).coe_nonneg)
  have hq : 0 ≤ sourceGaussianDeviation u := (by norm_num : (0 : ℝ) ≤ 1).trans
    (one_le_sourceGaussianDeviation u)
  apply (measure_mono ?_).trans (finite_gaussian_sum_sq_source_tail μ
    (fun i ω => X ω i) v hX u hu hu1)
  intro ω hω
  have hsq := (sq_lt_sq₀ (mul_nonneg hq (Real.sqrt_nonneg _)) (norm_nonneg (X ω))).mpr hω
  simpa only [mem_setOf_eq, mul_pow, Real.sq_sqrt hS, EuclideanSpace.real_norm_sq_eq] using hsq

end PaperFormalization.Manuscript
