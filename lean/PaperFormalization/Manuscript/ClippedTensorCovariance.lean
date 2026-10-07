import PaperFormalization.Manuscript.ActualTensorSampleMean
import PaperFormalization.Manuscript.ClippingBias

/-! # Actual hard-threshold covariance tensors under an unchanged law

The tensor-valued function is multiplied by the indicator of its actual
finite-column energy being at most tau. This does not restrict the population
measure or condition the sample law. The restoration bias has coefficient one.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PaperFormalization.Manuscript

variable {E H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [Fintype ι] [DecidableEq ι]

/-- The literal source hard cutoff W 1{Z≤tau}, with Z the actual column energy. -/
noncomputable def energyClippedTensor
    (A : E → (EuclideanSpace ℝ ι →L[ℝ] H)) (tau : ℝ) : E → realHilbertTensor H :=
  {x | finiteHilbertSchmidtNorm (A x) ^ 2 ≤ tau}.indicator
    (fun x => finiteOperatorCovariance (A x))

/-- The actual tensor is unchanged when its column energy is within the cutoff. -/
theorem energyClippedTensor_of_energy_le
    (A : E → (EuclideanSpace ℝ ι →L[ℝ] H)) (tau : ℝ) (x : E)
    (hx : finiteHilbertSchmidtNorm (A x) ^ 2 ≤ tau) :
    energyClippedTensor A tau x = finiteOperatorCovariance (A x) := by
  simp only [energyClippedTensor, Set.indicator_apply, Set.mem_setOf_eq, if_pos hx]

/-- Outside the energy cutoff, the actual tensor function is zero. -/
theorem energyClippedTensor_of_energy_gt
    (A : E → (EuclideanSpace ℝ ι →L[ℝ] H)) (tau : ℝ) (x : E)
    (hx : tau < finiteHilbertSchmidtNorm (A x) ^ 2) :
    energyClippedTensor A tau x = 0 := by
  simp only [energyClippedTensor, Set.indicator_apply, Set.mem_setOf_eq, if_neg (not_le.mpr hx)]

/-- The clipped tensor's norm is at most the literal cutoff, with no factor two. -/
theorem norm_energyClippedTensor_le
    (A : E → (EuclideanSpace ℝ ι →L[ℝ] H)) (tau : ℝ) (htau : 0 ≤ tau) (x : E) :
    ‖energyClippedTensor A tau x‖ ≤ tau := by
  by_cases hx : finiteHilbertSchmidtNorm (A x) ^ 2 ≤ tau
  · rw [energyClippedTensor_of_energy_le A tau x hx]
    exact (norm_finiteOperatorCovariance_le (A x)).trans hx
  · rw [energyClippedTensor_of_energy_gt A tau x (lt_of_not_ge hx), norm_zero]
    exact htau

/-- Hard clipping never increases the bound by the actual column energy. -/
theorem norm_energyClippedTensor_le_energy
    (A : E → (EuclideanSpace ℝ ι →L[ℝ] H)) (tau : ℝ) (x : E) :
    ‖energyClippedTensor A tau x‖ ≤ finiteHilbertSchmidtNorm (A x) ^ 2 := by
  by_cases hx : finiteHilbertSchmidtNorm (A x) ^ 2 ≤ tau
  · rw [energyClippedTensor_of_energy_le A tau x hx]
    exact norm_finiteOperatorCovariance_le (A x)
  · rw [energyClippedTensor_of_energy_gt A tau x (lt_of_not_ge hx), norm_zero]
    exact sq_nonneg _

variable [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

noncomputable local instance instMeasurableSpaceEnergyClippedTensor : MeasurableSpace (realHilbertTensor H) := borel _
noncomputable local instance instBorelSpaceEnergyClippedTensor : BorelSpace (realHilbertTensor H) := ⟨rfl⟩

omit [SecondCountableTopology E] in
/-- The actual discontinuous cutoff is Borel measurable; no continuity at its
threshold and no whole-tensor separability is asserted. -/
theorem measurable_energyClippedTensor
    (A : E → (EuclideanSpace ℝ ι →L[ℝ] H)) (hA : Continuous A) (tau : ℝ) :
    Measurable (energyClippedTensor A tau) := by
  exact (continuous_finiteOperatorCovariance.comp hA).measurable.indicator
    (measurableSet_le (continuous_finiteOperator_energy A hA).measurable measurable_const)

/-- The bounded hard cutoff is genuinely L2 under any finite original law.
AE strong measurability follows from the actual continuous image and indicator. -/
theorem memLp_two_energyClippedTensor
    (μ : Measure E) [IsFiniteMeasure μ]
    (A : E → (EuclideanSpace ℝ ι →L[ℝ] H)) (hA : Continuous A)
    (tau : ℝ) (htau : 0 ≤ tau) : MemLp (energyClippedTensor A tau) 2 μ := by
  apply MemLp.of_bound
    ((continuous_finiteOperatorCovariance.comp hA).aestronglyMeasurable.indicator
      (measurableSet_le (continuous_finiteOperator_energy A hA).measurable measurable_const)) tau
  exact Filter.Eventually.of_forall (norm_energyClippedTensor_le A tau htau)

omit [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- On the sample localization event the two actual empirical tensors agree.
This equality changes no law and is used only after concentration is proved. -/
theorem energyClippedTensor_sampleMean_eq {N : ℕ}
    (A : E → (EuclideanSpace ℝ ι →L[ℝ] H)) (tau : ℝ) (Y : Fin N → E)
    (hY : ∀ i, finiteHilbertSchmidtNorm (A (Y i)) ^ 2 ≤ tau) :
    (N : ℝ)⁻¹ • ∑ i, energyClippedTensor A tau (Y i) =
      (N : ℝ)⁻¹ • ∑ i, finiteOperatorCovariance (A (Y i)) := by
  congr 1
  exact Finset.sum_congr rfl (fun i _ => energyClippedTensor_of_energy_le A tau (Y i) (hY i))

set_option maxHeartbeats 800000 in
/-- Restoring the original population mean costs only the square root of its
original tail probability times the genuine fourth-moment bound. The exact
coefficient is one because hard clipping sets the tensor to zero outside. -/
theorem energyClippedTensor_population_bias_le
    (μ : Measure E) [IsFiniteMeasure μ]
    (A : E → (EuclideanSpace ℝ ι →L[ℝ] H)) (hA : Continuous A) (tau C4 : ℝ)
    (hfour : Integrable (fun x => finiteHilbertSchmidtNorm (A x) ^ 4) μ)
    (hC4 : (∫ x, finiteHilbertSchmidtNorm (A x) ^ 4 ∂μ) ≤ C4) :
    ‖(∫ x, finiteOperatorCovariance (A x) ∂μ) - ∫ x, energyClippedTensor A tau x ∂μ‖ ≤
      Real.sqrt C4 * Real.sqrt (μ.real {x | tau < finiteHilbertSchmidtNorm (A x) ^ 2}) := by
  let Z := fun x => finiteHilbertSchmidtNorm (A x) ^ 2
  let W := fun x => finiteOperatorCovariance (A x)
  let s : Set E := {x | tau < Z x}
  have hZc : Continuous Z := continuous_finiteOperator_energy A hA
  have hZsq : Integrable (fun x => Z x ^ 2) μ := by
    simpa only [Z, ← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num] using hfour
  have hZ : MemLp Z 2 μ := (memLp_two_iff_integrable_sq hZc.aestronglyMeasurable).2 hZsq
  have hW : MemLp W 2 μ := hZ.mono'
    (continuous_finiteOperatorCovariance.comp hA).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => norm_finiteOperatorCovariance_le (A x)))
  have hs : MeasurableSet s := measurableSet_lt measurable_const hZc.measurable
  have hkeep : MeasurableSet {x | Z x ≤ tau} := measurableSet_le hZc.measurable measurable_const
  have hclip : Integrable (energyClippedTensor A tau) μ :=
    (hW.indicator hkeep).integrable (by norm_num)
  have hdiff : (fun x => W x - energyClippedTensor A tau x) = s.indicator W := by
    funext x
    by_cases hx : Z x ≤ tau
    · simp only [energyClippedTensor_of_energy_le A tau x hx, W, sub_self,
        Set.indicator_apply, s, Set.mem_setOf_eq, if_neg (not_lt.mpr hx)]
    · simp only [energyClippedTensor_of_energy_gt A tau x (lt_of_not_ge hx), sub_zero,
        Set.indicator_apply, s, Set.mem_setOf_eq, if_pos (lt_of_not_ge hx)]
  have hWfour : (∫ x, ‖W x‖ ^ 2 ∂μ) ≤ C4 := by
    refine (integral_mono (hW.integrable_norm_pow (by norm_num)) hfour (fun x => ?_)).trans hC4
    simpa only [W, ← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num] using
      pow_le_pow_left₀ (norm_nonneg _) (norm_finiteOperatorCovariance_le (A x)) 2
  change ‖(∫ x, W x ∂μ) - ∫ x, energyClippedTensor A tau x ∂μ‖ ≤ _
  rw [← integral_sub (hW.integrable (by norm_num)) hclip, hdiff, integral_indicator hs]
  calc
    _ ≤ ∫ x in s, ‖W x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ Real.sqrt (∫ x, ‖W x‖ ^ 2 ∂μ) * Real.sqrt (μ.real s) :=
      setIntegral_norm_le_sqrt_second_moment μ W hW s
    _ ≤ Real.sqrt C4 * Real.sqrt (μ.real s) :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hWfour) (Real.sqrt_nonneg _)

/-- On the original sample's energy event, clipping restores the raw covariance
error by adding only the proved population bias. No law is conditioned here. -/
theorem covariance_error_le_energyClipped_error_add_bias {N : ℕ}
    (μ : Measure E) [IsFiniteMeasure μ]
    (A : E → (EuclideanSpace ℝ ι →L[ℝ] H)) (hA : Continuous A) (tau C4 : ℝ)
    (hfour : Integrable (fun x => finiteHilbertSchmidtNorm (A x) ^ 4) μ)
    (hC4 : (∫ x, finiteHilbertSchmidtNorm (A x) ^ 4 ∂μ) ≤ C4)
    (Y : Fin N → E) (hY : ∀ i, finiteHilbertSchmidtNorm (A (Y i)) ^ 2 ≤ tau) :
    ‖(N : ℝ)⁻¹ • ∑ i, finiteOperatorCovariance (A (Y i)) -
      ∫ x, finiteOperatorCovariance (A x) ∂μ‖ ≤
      ‖(N : ℝ)⁻¹ • ∑ i, energyClippedTensor A tau (Y i) -
        ∫ x, energyClippedTensor A tau x ∂μ‖ +
      Real.sqrt C4 * Real.sqrt (μ.real {x | tau < finiteHilbertSchmidtNorm (A x) ^ 2}) := by
  have hb := energyClippedTensor_population_bias_le μ A hA tau C4 hfour hC4
  have heq := energyClippedTensor_sampleMean_eq A tau Y hY
  calc
    _ ≤ ‖(N : ℝ)⁻¹ • ∑ i, finiteOperatorCovariance (A (Y i)) -
          ∫ x, energyClippedTensor A tau x ∂μ‖ +
        ‖(∫ x, energyClippedTensor A tau x ∂μ) -
          ∫ x, finiteOperatorCovariance (A x) ∂μ‖ := norm_sub_le_norm_sub_add_norm_sub ..
    _ = ‖(N : ℝ)⁻¹ • ∑ i, energyClippedTensor A tau (Y i) -
          ∫ x, energyClippedTensor A tau x ∂μ‖ +
        ‖(∫ x, finiteOperatorCovariance (A x) ∂μ) -
          ∫ x, energyClippedTensor A tau x ∂μ‖ := by
      rw [← heq, norm_sub_rev (∫ x, energyClippedTensor A tau x ∂μ)
        (∫ x, finiteOperatorCovariance (A x) ∂μ)]
    _ ≤ _ := add_le_add le_rfl hb

end PaperFormalization.Manuscript
