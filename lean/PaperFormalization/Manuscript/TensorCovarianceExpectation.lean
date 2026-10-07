import PaperFormalization.Manuscript.HilbertSampleMean

/-! # Exact second-moment and product estimates for covariance sampling

The scalar energy average and tensor sampling error use the same sample.
Cauchy--Schwarz does not require those two quantities to be independent.
This unit proves the finite-mean and product steps; the actual tensor/law
instantiation and the source's sharp fourth-moment coefficient are separate.
-/

open MeasureTheory
open scoped BigOperators

namespace PaperFormalization.Manuscript

/-- The exact squared-mean Jensen inequality with one reciprocal N. -/
theorem sq_scalar_sampleMean_le_mean_sq {N : ℕ} (hN : 0 < N) (z : Fin N → ℝ) :
    ((N : ℝ)⁻¹ * ∑ i, z i) ^ 2 ≤ (N : ℝ)⁻¹ * ∑ i, z i ^ 2 := by
  have hsum : (∑ i, z i) ^ 2 ≤ (N : ℝ) * ∑ i, z i ^ 2 := by
    simpa using (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin N => (1 : ℝ)) z)
  calc
    _ = (N : ℝ)⁻¹ ^ 2 * (∑ i, z i) ^ 2 := mul_pow _ _ _
    _ ≤ (N : ℝ)⁻¹ ^ 2 * ((N : ℝ) * ∑ i, z i ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = _ := by
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp

/-- The empirical energy's second moment is at most the common coordinate
second-moment bound. Neither independence nor nonnegativity is needed here. -/
theorem integral_sq_scalar_sampleMean_le {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (ν : Measure Ω) (Z : Fin N → Ω → ℝ) (hN : 0 < N)
    (hZ : ∀ i, MemLp (Z i) 2 ν) (C4 : ℝ)
    (hC4 : ∀ i, (∫ ω, Z i ω ^ 2 ∂ν) ≤ C4) :
    (∫ ω, ((N : ℝ)⁻¹ * ∑ i, Z i ω) ^ 2 ∂ν) ≤ C4 := by
  have hm : MemLp (fun ω => (N : ℝ)⁻¹ * ∑ i, Z i ω) 2 ν :=
    (memLp_finsetSum Finset.univ (fun i _ => hZ i)).const_mul _
  have hZi (i : Fin N) : Integrable (fun ω => Z i ω ^ 2) ν := by
    simpa only [Real.norm_eq_abs, sq_abs] using (hZ i).integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hi : Integrable (fun ω => ((N : ℝ)⁻¹ * ∑ i, Z i ω) ^ 2) ν := by
    simpa only [Real.norm_eq_abs, sq_abs] using hm.integrable_norm_pow (by norm_num : 2 ≠ 0)
  calc
    _ ≤ ∫ ω, (N : ℝ)⁻¹ * ∑ i, Z i ω ^ 2 ∂ν :=
      integral_mono hi ((integrable_finsetSum _ (fun i _ => hZi i)).const_mul _)
        (fun ω => sq_scalar_sampleMean_le_mean_sq hN (fun i => Z i ω))
    _ = (N : ℝ)⁻¹ * ∑ i, ∫ ω, Z i ω ^ 2 ∂ν := by
      rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ => hZi i)]
    _ ≤ (N : ℝ)⁻¹ * ∑ _i : Fin N, C4 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hC4 i)) (by positivity)
    _ = C4 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hN.ne' : (N : ℝ) ≠ 0), one_mul]

/-- Two genuine L2 bounds give the exact C4/sqrt N product rate under the
same law. No independence between the energy and error factors is used. -/
theorem integral_nonneg_mul_norm_le_fourth_moment_rate
    {Ω F : Type*} [MeasurableSpace Ω] [NormedAddCommGroup F] {N : ℕ}
    (ν : Measure Ω) (Z : Ω → ℝ) (E : Ω → F)
    (hZ : MemLp Z 2 ν) (hE : MemLp E 2 ν)
    (hZ0 : ∀ᵐ ω ∂ν, 0 ≤ Z ω) (C4 : ℝ)
    (hCZ : (∫ ω, Z ω ^ 2 ∂ν) ≤ C4)
    (hCE : (∫ ω, ‖E ω‖ ^ 2 ∂ν) ≤ C4 / N) :
    Integrable (fun ω => Z ω * ‖E ω‖) ν ∧
      (∫ ω, Z ω * ‖E ω‖ ∂ν) ≤ C4 / Real.sqrt N := by
  refine ⟨hZ.integrable_mul hE.norm, ?_⟩
  have hC4 : 0 ≤ C4 := (integral_nonneg (fun ω => sq_nonneg (Z ω))).trans hCZ
  have hCS : (∫ ω, Z ω * ‖E ω‖ ∂ν) ≤
      Real.sqrt (∫ ω, Z ω ^ 2 ∂ν) * Real.sqrt (∫ ω, ‖E ω‖ ^ 2 ∂ν) := by
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two hZ0
      (Filter.Eventually.of_forall (fun ω => norm_nonneg (E ω)))
      (by simpa using hZ) (by simpa using hE.norm)
    simpa only [Real.rpow_two, one_div, Real.sqrt_eq_rpow] using h
  calc
    _ ≤ Real.sqrt (∫ ω, Z ω ^ 2 ∂ν) * Real.sqrt (∫ ω, ‖E ω‖ ^ 2 ∂ν) := hCS
    _ ≤ Real.sqrt C4 * Real.sqrt (C4 / N) :=
      mul_le_mul (Real.sqrt_le_sqrt hCZ) (Real.sqrt_le_sqrt hCE)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = C4 / Real.sqrt N := by
      rw [Real.sqrt_div hC4, ← mul_div_assoc, ← sq, Real.sq_sqrt hC4]

end PaperFormalization.Manuscript
