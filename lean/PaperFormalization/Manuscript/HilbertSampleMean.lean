import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-! # Actual Hilbert-valued sample mean second moments

These statements are under one fixed probability measure. They may be
applied to each population conditional law but do not change the conditioning
or infer independence after a localization event. Genuine L2 integrability
and actual pairwise independence derive every off-diagonal cancellation.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace PaperFormalization.Manuscript

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H]

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
/-- The inner product of two genuine L2 Hilbert random variables is integrable. -/
theorem integrable_inner_of_memLp_two (μ : Measure Ω) (X Y : Ω → H)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Integrable (fun ω => inner ℝ (X ω) (Y ω)) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hX.toLp X) (hY.toLp Y)).congr
  filter_upwards [hX.coeFn_toLp, hY.coeFn_toLp] with ω hx hy
  rw [hx, hy]

/-- Independence gives the actual factorization of the expected inner
product, with no finite-dimensional or whole-target separability hypothesis. -/
theorem integral_inner_of_independent (μ : Measure Ω) (X Y : Ω → H)
    (hXY : IndepFun X Y μ) (hX : Integrable X μ) (hY : Integrable Y μ) :
    (∫ ω, inner ℝ (X ω) (Y ω) ∂μ) = inner ℝ (∫ ω, X ω ∂μ) (∫ ω, Y ω ∂μ) := by
  exact hXY.integral_bilin hX hY (innerSL ℝ)

omit [MeasurableSpace H] [BorelSpace H] in
/-- Centering a Hilbert-valued L2 variable gives the exact variance identity. -/
theorem integral_norm_sub_mean_sq (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → H) (hX : MemLp X 2 μ) :
    (∫ ω, ‖X ω - ∫ z, X z ∂μ‖ ^ 2 ∂μ) =
      (∫ ω, ‖X ω‖ ^ 2 ∂μ) - ‖∫ ω, X ω ∂μ‖ ^ 2 := by
  have hi : Integrable X μ := hX.integrable (by norm_num)
  have hs : Integrable (fun ω => ‖X ω‖ ^ 2) μ := hX.integrable_norm_pow (by norm_num)
  have hinner : (∫ ω, inner ℝ (X ω) (∫ z, X z ∂μ) ∂μ) = ‖∫ z, X z ∂μ‖ ^ 2 := by
    calc
      _ = ∫ ω, inner ℝ (∫ z, X z ∂μ) (X ω) ∂μ := by
        apply integral_congr_ae
        filter_upwards with ω using real_inner_comm _ _
      _ = _ := by rw [integral_inner hi, real_inner_self_eq_norm_sq]
  have hp : Integrable (fun ω => 2 * inner ℝ (X ω) (∫ z, X z ∂μ)) μ :=
    (hi.inner_const (∫ z, X z ∂μ)).const_mul 2
  have hsub : Integrable (fun ω => ‖X ω‖ ^ 2 - 2 * inner ℝ (X ω) (∫ z, X z ∂μ)) μ := hs.sub hp
  simp_rw [norm_sub_sq_real]
  rw [integral_add hsub (integrable_const _), integral_sub hs hp, integral_const_mul, hinner]
  simp
  ring

/-- Pairwise independent centered Hilbert variables have no off-diagonal
contribution to the mean square of their finite sum. -/
theorem integral_norm_sum_sq_eq_of_independent_centered {N : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin N → Ω → H)
    (hX : ∀ i, MemLp (X i) 2 μ)
    (hind : Pairwise (fun i j => IndepFun (X i) (X j) μ))
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0) :
    (∫ ω, ‖∑ i, X i ω‖ ^ 2 ∂μ) = ∑ i, ∫ ω, ‖X i ω‖ ^ 2 ∂μ := by
  have hinner (i j : Fin N) := integrable_inner_of_memLp_two μ (X i) (X j) (hX i) (hX j)
  have hpoint (ω : Ω) : ‖∑ i, X i ω‖ ^ 2 =
      ∑ i, ∑ j, inner ℝ (X i ω) (X j ω) := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp only [inner_sum]
  simp_rw [hpoint]
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum _ (fun j _ => hinner i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => hinner i j)]
  rw [Finset.sum_eq_single i]
  · simp only [real_inner_self_eq_norm_sq]
  · intro j _ hji
    rw [integral_inner_of_independent μ (X i) (X j) (hind hji.symm)
      ((hX i).integrable (by norm_num)) ((hX j).integrable (by norm_num)), hmean i, hmean j]
    simp
  · simp

/-- The actual centered sample mean has exact N^-2 normalization and the
sum of individual Hilbert variances, even without identical laws. -/
theorem integral_norm_centered_sampleMean_sq {N : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin N → Ω → H)
    (hX : ∀ i, MemLp (X i) 2 μ)
    (hind : Pairwise (fun i j => IndepFun (X i) (X j) μ)) :
    (∫ ω, ‖(N : ℝ)⁻¹ • ∑ i, (X i ω - ∫ z, X i z ∂μ)‖ ^ 2 ∂μ) =
      (N : ℝ)⁻¹ ^ 2 * ∑ i, ((∫ ω, ‖X i ω‖ ^ 2 ∂μ) - ‖∫ ω, X i ω ∂μ‖ ^ 2) := by
  let Z : Fin N → Ω → H := fun i ω => X i ω - ∫ z, X i z ∂μ
  have hZ (i : Fin N) : MemLp (Z i) 2 μ := (hX i).sub (memLp_const _)
  have hZi : Pairwise (fun i j => IndepFun (Z i) (Z j) μ) := by
    intro i j hij
    exact (hind hij).comp (continuous_id.sub continuous_const).measurable
      (continuous_id.sub continuous_const).measurable
  have hZ0 (i : Fin N) : (∫ ω, Z i ω ∂μ) = 0 := by
    dsimp [Z]
    rw [integral_sub ((hX i).integrable (by norm_num)) (integrable_const _)]
    simp
  have hsum := integral_norm_sum_sq_eq_of_independent_centered μ Z hZ hZi hZ0
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [integral_const_mul, hsum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact integral_norm_sub_mean_sq μ (X i) (hX i)

/-- Uniform genuine second moments give the source C/N mean-square rate.
Pairwise independence suffices; identical distribution is not added. -/
theorem integral_norm_centered_sampleMean_sq_le {N : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin N → Ω → H)
    (hN : 0 < N) (hX : ∀ i, MemLp (X i) 2 μ)
    (hind : Pairwise (fun i j => IndepFun (X i) (X j) μ))
    (C : ℝ) (hC : ∀ i, (∫ ω, ‖X i ω‖ ^ 2 ∂μ) ≤ C) :
    (∫ ω, ‖(N : ℝ)⁻¹ • ∑ i, (X i ω - ∫ z, X i z ∂μ)‖ ^ 2 ∂μ) ≤ C / N := by
  rw [integral_norm_centered_sampleMean_sq μ X hX hind]
  have hsum : (∑ i, ((∫ ω, ‖X i ω‖ ^ 2 ∂μ) - ‖∫ ω, X i ω ∂μ‖ ^ 2)) ≤
      (N : ℝ) * C := by
    calc
      _ ≤ ∑ _i : Fin N, C := by
        apply Finset.sum_le_sum
        intro i _
        exact (sub_le_self _ (sq_nonneg _)).trans (hC i)
      _ = _ := by simp
  calc
    _ ≤ (N : ℝ)⁻¹ ^ 2 * ((N : ℝ) * C) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = C / N := by
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp

/-- Under a common actual mean, the centered sum is exactly the usual
empirical average minus that mean; one factor 1/N is retained. -/
theorem integral_norm_sampleMean_sub_sq_le {N : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin N → Ω → H)
    (hN : 0 < N) (hX : ∀ i, MemLp (X i) 2 μ)
    (hind : Pairwise (fun i j => IndepFun (X i) (X j) μ))
    (theta : H) (hmean : ∀ i, (∫ ω, X i ω ∂μ) = theta)
    (C : ℝ) (hC : ∀ i, (∫ ω, ‖X i ω‖ ^ 2 ∂μ) ≤ C) :
    (∫ ω, ‖(N : ℝ)⁻¹ • ∑ i, X i ω - theta‖ ^ 2 ∂μ) ≤ C / N := by
  have hpoint (ω : Ω) : (N : ℝ)⁻¹ • ∑ i, (X i ω - ∫ z, X i z ∂μ) =
      (N : ℝ)⁻¹ • ∑ i, X i ω - theta := by
    simp only [hmean, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_sub, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    rw [inv_mul_cancel₀ (by exact_mod_cast hN.ne' : (N : ℝ) ≠ 0), one_smul]
  simpa only [hpoint] using integral_norm_centered_sampleMean_sq_le μ X hN hX hind C hC

omit [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
/-- The expected norm is bounded by the genuine root second moment. This
uses scalar centering, so no whole-target separability is required. -/
theorem integral_norm_le_sqrt_second_moment (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → H) (hX : MemLp X 2 μ) :
    (∫ ω, ‖X ω‖ ∂μ) ≤ Real.sqrt (∫ ω, ‖X ω‖ ^ 2 ∂μ) := by
  have hvar := integral_norm_sub_mean_sq μ (fun ω => ‖X ω‖) hX.norm
  have hnonneg : 0 ≤ ∫ ω, ‖(‖X ω‖ : ℝ) - ∫ z, ‖X z‖ ∂μ‖ ^ 2 ∂μ :=
    integral_nonneg (fun _ => sq_nonneg _)
  rw [hvar] at hnonneg
  simp only [Real.norm_eq_abs, sq_abs] at hnonneg
  have hsq := Real.sq_sqrt (integral_nonneg (fun ω => sq_nonneg ‖X ω‖) :
    0 ≤ ∫ ω, ‖X ω‖ ^ 2 ∂μ)
  have hs0 := Real.sqrt_nonneg (∫ ω, ‖X ω‖ ^ 2 ∂μ)
  nlinarith

/-- The source expected empirical error is at most sqrt(C/N), under the
same probability law and actual pairwise independence used for C/N. -/
theorem integral_norm_sampleMean_sub_le {N : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Fin N → Ω → H)
    (hN : 0 < N) (hX : ∀ i, MemLp (X i) 2 μ)
    (hind : Pairwise (fun i j => IndepFun (X i) (X j) μ))
    (theta : H) (hmean : ∀ i, (∫ ω, X i ω ∂μ) = theta)
    (C : ℝ) (hC : ∀ i, (∫ ω, ‖X i ω‖ ^ 2 ∂μ) ≤ C) :
    (∫ ω, ‖(N : ℝ)⁻¹ • ∑ i, X i ω - theta‖ ∂μ) ≤ Real.sqrt (C / N) := by
  have hm : MemLp (fun ω => (N : ℝ)⁻¹ • ∑ i, X i ω - theta) 2 μ :=
    ((memLp_finsetSum Finset.univ (fun i _ => hX i)).const_smul (N : ℝ)⁻¹).sub
      (memLp_const theta)
  exact (integral_norm_le_sqrt_second_moment μ _ hm).trans
    (Real.sqrt_le_sqrt (integral_norm_sampleMean_sub_sq_le μ X hN hX hind theta hmean C hC))

end PaperFormalization.Manuscript
