import PaperFormalization.Manuscript.TensorCovarianceExpectation
import PaperFormalization.Manuscript.HilbertTensorCovariance

/-! # Actual finite-operator covariance sampling under one unchanged law

The fourth moment is the actual finite Hilbert--Schmidt fourth moment.
Its value is a supplied bound to be instantiated by the source coefficient;
no operator-norm or dimension-inflated envelope replaces it. The energy and
error factors use the same particles and need not be independent.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace PaperFormalization.Manuscript

variable {E Ω H ι : Type*} [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [Fintype ι] [DecidableEq ι] {N : ℕ}

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
/-- Actual finite-column energy is continuous when the operator field is. -/
theorem continuous_finiteOperator_energy
    (A : E → (EuclideanSpace ℝ ι →L[ℝ] H)) (hA : Continuous A) :
    Continuous (fun x => finiteHilbertSchmidtNorm (A x) ^ 2) := by
  simp_rw [finiteHilbertSchmidtNorm_sq]
  exact continuous_finsetSum Finset.univ (fun j _ =>
    (hA.clm_apply continuous_const).norm.pow 2)

set_option maxHeartbeats 800000 in
/-- Genuine actual fourth moments yield both required second-moment bounds:
Jensen controls the sample energy, and independence controls the tensor error.
The common population law is retained without conditioning on localization. -/
theorem actual_tensor_sample_second_moments
    (μ : Measure E) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (A : E → (EuclideanSpace ℝ ι →L[ℝ] H)) (hA : Continuous A)
    (Y : Fin N → Ω → E) (hN : 0 < N)
    (hLaw : ∀ i, ν.map (Y i) = μ)
    (hind : Pairwise (fun i j => IndepFun (Y i) (Y j) ν))
    (C4 : ℝ) (hfour : Integrable (fun x => finiteHilbertSchmidtNorm (A x) ^ 4) μ)
    (hC4 : (∫ x, finiteHilbertSchmidtNorm (A x) ^ 4 ∂μ) ≤ C4) :
    let Zbar := fun ω => (N : ℝ)⁻¹ * ∑ i, finiteHilbertSchmidtNorm (A (Y i ω)) ^ 2
    let Err := fun ω => (N : ℝ)⁻¹ • ∑ i, finiteOperatorCovariance (A (Y i ω)) -
      ∫ x, finiteOperatorCovariance (A x) ∂μ
    MemLp Zbar 2 ν ∧ MemLp Err 2 ν ∧
      (∫ ω, Zbar ω ^ 2 ∂ν) ≤ C4 ∧ (∫ ω, ‖Err ω‖ ^ 2 ∂ν) ≤ C4 / N := by
  let Z := fun x => finiteHilbertSchmidtNorm (A x) ^ 2
  let W := fun x => finiteOperatorCovariance (A x)
  have hZc : Continuous Z := continuous_finiteOperator_energy A hA
  have hWc : Continuous W := continuous_finiteOperatorCovariance.comp hA
  have hZsq : Integrable (fun x => Z x ^ 2) μ := by
    simpa only [Z, ← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num] using hfour
  have hZ : MemLp Z 2 μ := (memLp_two_iff_integrable_sq hZc.aestronglyMeasurable).2 hZsq
  have hW : MemLp W 2 μ := hZ.mono' hWc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => norm_finiteOperatorCovariance_le (A x)))
  have hCz : (∫ x, Z x ^ 2 ∂μ) ≤ C4 := by
    simpa only [Z, ← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num] using hC4
  have hCw : (∫ x, ‖W x‖ ^ 2 ∂μ) ≤ C4 := by
    refine (integral_mono (hW.integrable_norm_pow (by norm_num)) hZsq (fun x => ?_)).trans hCz
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_finiteOperatorCovariance_le (A x)) 2
  have hY (i : Fin N) : AEMeasurable (Y i) ν :=
    aemeasurable_of_map_neZero (by rw [hLaw i]; infer_instance)
  have hZi (i : Fin N) : MemLp (fun ω => Z (Y i ω)) 2 ν := by
    have hm : MemLp Z 2 (ν.map (Y i)) := by rw [hLaw i]; exact hZ
    exact hm.comp_of_map (hY i)
  have hWi (i : Fin N) : MemLp (fun ω => W (Y i ω)) 2 ν := by
    have hm : MemLp W 2 (ν.map (Y i)) := by rw [hLaw i]; exact hW
    exact hm.comp_of_map (hY i)
  refine ⟨(memLp_finsetSum Finset.univ (fun i _ => hZi i)).const_mul _,
    ((memLp_finsetSum Finset.univ (fun i _ => hWi i)).const_smul ((N : ℝ)⁻¹)).sub
      (memLp_const (∫ x, W x ∂μ)), ?_, ?_⟩
  · apply integral_sq_scalar_sampleMean_le ν (fun i ω => Z (Y i ω)) hN hZi C4
    intro i
    have hm : (∫ x, Z x ^ 2 ∂(ν.map (Y i))) = ∫ ω, Z (Y i ω) ^ 2 ∂ν :=
      integral_map (hY i) (hZc.pow 2).aestronglyMeasurable
    rw [← hm, hLaw i]
    exact hCz
  · letI : MeasurableSpace (realHilbertTensor H) := borel (realHilbertTensor H)
    letI : BorelSpace (realHilbertTensor H) := ⟨rfl⟩
    apply integral_norm_sampleMean_sub_sq_le ν (fun i ω => W (Y i ω)) hN hWi
    · intro i j hij
      exact (hind hij).comp hWc.measurable hWc.measurable
    · intro i
      rw [← integral_map (hY i) hWc.aestronglyMeasurable, hLaw i]
    · intro i
      have hm : (∫ x, ‖W x‖ ^ 2 ∂(ν.map (Y i))) = ∫ ω, ‖W (Y i ω)‖ ^ 2 ∂ν :=
        integral_map (hY i) (hWc.norm.pow 2).aestronglyMeasurable
      rw [← hm, hLaw i]
      exact hCw

/-- The actual energy times actual tensor error has the exact C4/sqrt N
expectation bound under the same sample, including their dependence. -/
theorem actual_tensor_sample_energy_error_expectation_le
    (μ : Measure E) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (A : E → (EuclideanSpace ℝ ι →L[ℝ] H)) (hA : Continuous A)
    (Y : Fin N → Ω → E) (hN : 0 < N)
    (hLaw : ∀ i, ν.map (Y i) = μ)
    (hind : Pairwise (fun i j => IndepFun (Y i) (Y j) ν))
    (C4 : ℝ) (hfour : Integrable (fun x => finiteHilbertSchmidtNorm (A x) ^ 4) μ)
    (hC4 : (∫ x, finiteHilbertSchmidtNorm (A x) ^ 4 ∂μ) ≤ C4) :
    let Zbar := fun ω => (N : ℝ)⁻¹ * ∑ i, finiteHilbertSchmidtNorm (A (Y i ω)) ^ 2
    let Err := fun ω => (N : ℝ)⁻¹ • ∑ i, finiteOperatorCovariance (A (Y i ω)) -
      ∫ x, finiteOperatorCovariance (A x) ∂μ
    Integrable (fun ω => Zbar ω * ‖Err ω‖) ν ∧
      (∫ ω, Zbar ω * ‖Err ω‖ ∂ν) ≤ C4 / Real.sqrt N := by
  have hm := actual_tensor_sample_second_moments μ ν A hA Y hN hLaw hind C4 hfour hC4
  exact integral_nonneg_mul_norm_le_fourth_moment_rate ν _ _ hm.1 hm.2.1
    (Filter.Eventually.of_forall (fun ω =>
      mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => sq_nonneg _))))
    C4 hm.2.2.1 hm.2.2.2

/-- A genuine measurable nonnegative residual satisfying the checked pointwise
tensor reduction inherits L² C4/sqrt N. This adapter assumes neither the
expected-error conclusion nor independence between the two sample factors. -/
theorem expected_residual_le_of_actual_tensor_reduction
    (μ : Measure E) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (A : E → (EuclideanSpace ℝ ι →L[ℝ] H)) (hA : Continuous A)
    (Y : Fin N → Ω → E) (hN : 0 < N)
    (hLaw : ∀ i, ν.map (Y i) = μ)
    (hind : Pairwise (fun i j => IndepFun (Y i) (Y j) ν))
    (C4 : ℝ) (hfour : Integrable (fun x => finiteHilbertSchmidtNorm (A x) ^ 4) μ)
    (hC4 : (∫ x, finiteHilbertSchmidtNorm (A x) ^ 4 ∂μ) ≤ C4)
    (L : ℝ) (R : Ω → ℝ) (hRmeas : AEStronglyMeasurable R ν)
    (hR0 : ∀ᵐ ω ∂ν, 0 ≤ R ω)
    (hR : ∀ᵐ ω ∂ν, R ω ≤ L ^ 2 *
      (((N : ℝ)⁻¹ * ∑ i, finiteHilbertSchmidtNorm (A (Y i ω)) ^ 2) *
        ‖(N : ℝ)⁻¹ • ∑ i, finiteOperatorCovariance (A (Y i ω)) -
          ∫ x, finiteOperatorCovariance (A x) ∂μ‖)) :
    Integrable R ν ∧ (∫ ω, R ω ∂ν) ≤ L ^ 2 * C4 / Real.sqrt N := by
  have hp := actual_tensor_sample_energy_error_expectation_le μ ν A hA Y hN hLaw hind C4 hfour hC4
  have hmajor := hp.1.const_mul (L ^ 2)
  have hRi : Integrable R ν := hmajor.mono_nonneg hRmeas hR0 hR
  refine ⟨hRi, ?_⟩
  calc
    _ ≤ ∫ ω, L ^ 2 *
        (((N : ℝ)⁻¹ * ∑ i, finiteHilbertSchmidtNorm (A (Y i ω)) ^ 2) *
          ‖(N : ℝ)⁻¹ • ∑ i, finiteOperatorCovariance (A (Y i ω)) -
            ∫ x, finiteOperatorCovariance (A x) ∂μ‖) ∂ν :=
      integral_mono_ae hRi hmajor hR
    _ = L ^ 2 * ∫ ω,
        ((N : ℝ)⁻¹ * ∑ i, finiteHilbertSchmidtNorm (A (Y i ω)) ^ 2) *
          ‖(N : ℝ)⁻¹ • ∑ i, finiteOperatorCovariance (A (Y i ω)) -
            ∫ x, finiteOperatorCovariance (A x) ∂μ‖ ∂ν := integral_const_mul _ _
    _ ≤ L ^ 2 * (C4 / Real.sqrt N) :=
      mul_le_mul_of_nonneg_left hp.2 (sq_nonneg L)
    _ = _ := (mul_div_assoc _ _ _).symm

end PaperFormalization.Manuscript
