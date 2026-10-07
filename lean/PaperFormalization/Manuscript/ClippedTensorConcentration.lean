import PaperFormalization.Manuscript.ClippedTensorCovariance
import PaperFormalization.Manuscript.BoundedDifferenceFinite

/-! # Concentration of the literal hard-cutoff covariance error

The population law is unchanged. The cutoff is applied to the actual tensor
function before taking its genuine population mean. Full independence is
used only for the finite-product McDiarmid step.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace PaperFormalization.Manuscript

variable {E H ι : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype ι] [DecidableEq ι]
  {N : ℕ}

noncomputable local instance instMeasurableSpaceClippedTensorConcentration :
    MeasurableSpace (realHilbertTensor H) := borel _
noncomputable local instance instBorelSpaceClippedTensorConcentration :
    BorelSpace (realHilbertTensor H) := ⟨rfl⟩

/-- The actual cutoff empirical tensor minus its original-law population mean. -/
noncomputable def energyClippedCovarianceError (μ : Measure E)
    (A : E → (EuclideanSpace ℝ ι →L[ℝ] H)) (tau : ℝ) (X : Fin N → E) : ℝ :=
  ‖(N : ℝ)⁻¹ • ∑ i, energyClippedTensor A tau (X i) -
    ∫ x, energyClippedTensor A tau x ∂μ‖

/-- The hard cutoff need not be continuous at its threshold, but the literal
finite-sample statistic is Borel measurable. -/
theorem measurable_energyClippedCovarianceError (μ : Measure E)
    (A : E → (EuclideanSpace ℝ ι →L[ℝ] H)) (hA : Continuous A) (tau : ℝ) :
    Measurable (energyClippedCovarianceError (N := N) μ A tau) := by
  unfold energyClippedCovarianceError
  have hf : StronglyMeasurable (energyClippedTensor A tau) :=
    (continuous_finiteOperatorCovariance.comp hA).stronglyMeasurable.indicator
      (measurableSet_le (continuous_finiteOperator_energy A hA).measurable measurable_const)
  exact (((Finset.stronglyMeasurable_fun_sum _ (fun i _ =>
    hf.comp_measurable (measurable_pi_apply i))).const_smul ((N : ℝ)⁻¹)).sub
      stronglyMeasurable_const).norm.measurable

omit [NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E] in
/-- Literal one-sample replacement has width 2tau/N. The uniform statistic
bound is 2tau, independently of the particle count and Hilbert dimension. -/
theorem energyClippedCovarianceError_bounded_differences (hN : 0 < N)
    (μ : Measure E) [IsProbabilityMeasure μ]
    (A : E → (EuclideanSpace ℝ ι →L[ℝ] H)) (tau : ℝ) (htau : 0 ≤ tau) :
    (∀ X : Fin N → E, 0 ≤ energyClippedCovarianceError μ A tau X ∧
      energyClippedCovarianceError μ A tau X ≤ 2 * tau) ∧
    (∀ X : Fin N → E, ∀ i y,
      |energyClippedCovarianceError μ A tau X -
        energyClippedCovarianceError μ A tau (Function.update X i y)| ≤ 2 * tau / N) := by
  classical
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hp : ‖∫ x, energyClippedTensor A tau x ∂μ‖ ≤ tau := by
    have hh := norm_integral_le_of_norm_le_const (μ := μ)
      (Filter.Eventually.of_forall (norm_energyClippedTensor_le A tau htau))
    simpa only [probReal_univ, mul_one] using hh
  have hm (X : Fin N → E) : ‖(N : ℝ)⁻¹ • ∑ i, energyClippedTensor A tau (X i)‖ ≤ tau := by
    simpa only [finiteFeatureMean, Fintype.card_fin] using
      norm_finiteFeatureMean_le (fun i => energyClippedTensor A tau (X i)) tau
        (fun i => norm_energyClippedTensor_le A tau htau (X i))
  constructor
  · intro X
    refine ⟨norm_nonneg _, (norm_sub_le _ _).trans ?_⟩
    exact (add_le_add (hm X) hp).trans_eq (by ring)
  · intro X i y
    have hsum : (∑ j, energyClippedTensor A tau (X j)) -
        (∑ j, energyClippedTensor A tau (Function.update X i y j)) =
        energyClippedTensor A tau (X i) - energyClippedTensor A tau y := by
      rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [Function.update_of_ne hji]
      · simp
    have hnorm : ‖energyClippedTensor A tau (X i) - energyClippedTensor A tau y‖ ≤ 2 * tau :=
      (norm_sub_le _ _).trans ((add_le_add (norm_energyClippedTensor_le A tau htau _)
        (norm_energyClippedTensor_le A tau htau _)).trans_eq (by ring))
    unfold energyClippedCovarianceError
    calc
      _ ≤ ‖((N : ℝ)⁻¹ • ∑ j, energyClippedTensor A tau (X j) -
          ∫ x, energyClippedTensor A tau x ∂μ) -
        ((N : ℝ)⁻¹ • ∑ j, energyClippedTensor A tau (Function.update X i y j) -
          ∫ x, energyClippedTensor A tau x ∂μ)‖ := abs_norm_sub_norm_le _ _
      _ = (N : ℝ)⁻¹ * ‖energyClippedTensor A tau (X i) - energyClippedTensor A tau y‖ := by
        rw [sub_sub_sub_cancel_right, ← smul_sub, hsum, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
      _ ≤ (N : ℝ)⁻¹ * (2 * tau) := mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = 2 * tau / N := by ring

set_option maxHeartbeats 800000 in
/-- Actual pairwise independent samples give the original-law root-variance
mean bound. The cutoff second moment is derived from the genuine HS fourth
moment; its bounded amplitude is not substituted for that moment. -/
theorem integrable_expected_energyClippedCovarianceError_le
    {Ω : Type*} [MeasurableSpace Ω] (hN : 0 < N)
    (μ : Measure E) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (Y : Fin N → Ω → E) (hLaw : ∀ i, ν.map (Y i) = μ)
    (hind : Pairwise (fun i j => IndepFun (Y i) (Y j) ν))
    (A : E → (EuclideanSpace ℝ ι →L[ℝ] H)) (hA : Continuous A)
    (tau C4 : ℝ) (htau : 0 ≤ tau)
    (hfour : Integrable (fun x => finiteHilbertSchmidtNorm (A x) ^ 4) μ)
    (hC4 : (∫ x, finiteHilbertSchmidtNorm (A x) ^ 4 ∂μ) ≤ C4) :
    Integrable (fun ω => energyClippedCovarianceError μ A tau (fun i => Y i ω)) ν ∧
      (∫ ω, energyClippedCovarianceError μ A tau (fun i => Y i ω) ∂ν) ≤
        Real.sqrt (C4 / N) := by
  let f := energyClippedTensor A tau
  have hf := measurable_energyClippedTensor A hA tau
  have hmem : MemLp f 2 μ := memLp_two_energyClippedTensor μ A hA tau htau
  have hsecond : (∫ x, ‖f x‖ ^ 2 ∂μ) ≤ C4 := by
    refine (integral_mono (hmem.integrable_norm_pow (by norm_num)) hfour (fun x => ?_)).trans hC4
    simpa only [← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num] using
      pow_le_pow_left₀ (norm_nonneg _) (norm_energyClippedTensor_le_energy A tau x) 2
  have hY (i : Fin N) : AEMeasurable (Y i) ν :=
    aemeasurable_of_map_neZero (by rw [hLaw i]; infer_instance)
  have hmapmem (i : Fin N) : MemLp f 2 (ν.map (Y i)) := by rw [hLaw i]; exact hmem
  have hX (i : Fin N) : MemLp (fun ω => f (Y i ω)) 2 ν :=
    (hmapmem i).comp_of_map (hY i)
  have hm : MemLp (fun ω => (N : ℝ)⁻¹ • ∑ i, f (Y i ω) - ∫ x, f x ∂μ) 2 ν :=
    ((memLp_finsetSum Finset.univ (fun i _ => hX i)).const_smul ((N : ℝ)⁻¹)).sub
      (memLp_const (∫ x, f x ∂μ))
  refine ⟨hm.norm.integrable (by norm_num), ?_⟩
  apply integral_norm_sampleMean_sub_le ν (fun i ω => f (Y i ω)) hN hX
    (fun i j hij => (hind hij).comp hf hf) (∫ x, f x ∂μ)
  · intro i
    rw [← integral_map (hY i) (hmapmem i).aestronglyMeasurable, hLaw i]
  · intro i
    rw [← integral_map (hY i) ((hmapmem i).integrable_norm_pow (by norm_num)).aestronglyMeasurable,
      hLaw i]
    exact hsecond

/-- Product samples have the actual fourth-moment mean bound and the centered
McDiarmid exponent for literal replacement width 2tau/N. -/
theorem energyClippedCovarianceError_pi_concentration (hN : 0 < N)
    (μ : Measure E) [IsProbabilityMeasure μ]
    (A : E → (EuclideanSpace ℝ ι →L[ℝ] H)) (hA : Continuous A)
    (tau C4 : ℝ) (htau : 0 ≤ tau)
    (hfour : Integrable (fun x => finiteHilbertSchmidtNorm (A x) ^ 4) μ)
    (hC4 : (∫ x, finiteHilbertSchmidtNorm (A x) ^ 4 ∂μ) ≤ C4) :
    let f := (energyClippedCovarianceError μ A tau : (Fin N → E) → ℝ)
    let prodLaw := Measure.pi (fun _ : Fin N => μ)
    Integrable f prodLaw ∧ (∫ X, f X ∂prodLaw) ≤ Real.sqrt (C4 / N) ∧
      ∀ t : ℝ, 0 ≤ t → prodLaw.real {X | (∫ Y, f Y ∂prodLaw) + t ≤ f X} ≤
        Real.exp (-2 * N * t ^ 2 / (2 * tau) ^ 2) := by
  let f := (energyClippedCovarianceError μ A tau : (Fin N → E) → ℝ)
  let prodLaw := Measure.pi (fun _ : Fin N => μ)
  let ampNN : ℝ≥0 := .mk (2 * tau) (by positivity)
  have hf : Measurable f := measurable_energyClippedCovarianceError μ A hA tau
  have hb := energyClippedCovarianceError_bounded_differences hN μ A tau htau
  have hind : iIndepFun (fun i : Fin N => fun X : Fin N → E => X i) prodLaw :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have hexp := integrable_expected_energyClippedCovarianceError_le hN μ prodLaw
    (fun i X => X i) (fun i => (measurePreserving_eval (fun _ : Fin N => μ) i).map_eq)
    (fun _ _ hij => hind.indepFun hij) A hA tau C4 htau hfour hC4
  refine ⟨hexp.1, hexp.2, ?_⟩
  intro t ht
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have htail := measure_ge_le_of_pi_bounded_differences N (fun _ => μ) f ampNN
    (fun _ => ampNN / N) hf
    (fun X => by rw [abs_of_nonneg (hb.1 X).1]; exact (hb.1 X).2)
    (fun X i y => by simpa only [NNReal.coe_div, NNReal.coe_natCast, ampNN,
      NNReal.coe_mk, f] using hb.2 X i y) t ht
  have hden : (∑ _i : Fin N, ((ampNN / N : ℝ≥0) : ℝ) ^ 2) = (2 * tau) ^ 2 / N := by
    simp only [NNReal.coe_div, NNReal.coe_natCast, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    change (N : ℝ) * ((2 * tau) / N) ^ 2 = (2 * tau) ^ 2 / N
    field_simp
  have he : -2 * t ^ 2 / ((2 * tau) ^ 2 / N) = -2 * N * t ^ 2 / (2 * tau) ^ 2 := by
    rw [div_div_eq_mul_div]
    ring
  simpa only [hden, he] using htail

/-- Fully independent original samples have the actual product configuration
law, without conditioning on any sample-energy event. -/
theorem energyClippedCovarianceError_iid_concentration
    {Ω : Type*} [MeasurableSpace Ω] (hN : 0 < N)
    (μ : Measure E) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (Y : Fin N → Ω → E) (hLaw : ∀ i, ν.map (Y i) = μ) (hind : iIndepFun Y ν)
    (A : E → (EuclideanSpace ℝ ι →L[ℝ] H)) (hA : Continuous A)
    (tau C4 : ℝ) (htau : 0 ≤ tau)
    (hfour : Integrable (fun x => finiteHilbertSchmidtNorm (A x) ^ 4) μ)
    (hC4 : (∫ x, finiteHilbertSchmidtNorm (A x) ^ 4 ∂μ) ≤ C4) :
    let F := fun ω => energyClippedCovarianceError μ A tau (fun i => Y i ω)
    ν.map (fun ω i => Y i ω) = Measure.pi (fun _ : Fin N => μ) ∧
      Integrable F ν ∧ (∫ ω, F ω ∂ν) ≤ Real.sqrt (C4 / N) ∧
      ∀ t : ℝ, 0 ≤ t → ν.real {ω | (∫ z, F z ∂ν) + t ≤ F ω} ≤
        Real.exp (-2 * N * t ^ 2 / (2 * tau) ^ 2) := by
  let f := (energyClippedCovarianceError μ A tau : (Fin N → E) → ℝ)
  let prodLaw := Measure.pi (fun _ : Fin N => μ)
  have hm (i : Fin N) : AEMeasurable (Y i) ν :=
    aemeasurable_of_map_neZero (by rw [hLaw i]; infer_instance)
  have hconfig : AEMeasurable (fun ω i => Y i ω) ν :=
    aemeasurable_pi_lambda (fun ω i => Y i ω) hm
  have hmap : ν.map (fun ω i => Y i ω) = prodLaw := by
    simpa only [hLaw] using hind.map_fun_eq_pi_map hm
  have hf : Measurable f := measurable_energyClippedCovarianceError μ A hA tau
  have hprod := energyClippedCovarianceError_pi_concentration hN μ A hA tau C4 htau hfour hC4
  have hi : Integrable (fun ω => f (fun i => Y i ω)) ν := by
    have hi' : Integrable f (ν.map (fun ω i => Y i ω)) := hmap ▸ hprod.1
    exact hi'.comp_aemeasurable hconfig
  have hmean : (∫ ω, f (fun i => Y i ω) ∂ν) = ∫ X, f X ∂prodLaw := by
    rw [← hmap]
    exact (integral_map hconfig hf.aestronglyMeasurable).symm
  refine ⟨hmap, hi, ?_, ?_⟩
  · rw [hmean]
    exact hprod.2.1
  · intro t ht
    have hprob := map_measureReal_apply_of_aemeasurable hconfig
      (s := {X | (∫ Z, f Z ∂prodLaw) + t ≤ f X})
      (measurableSet_le measurable_const hf)
    rw [hmap] at hprob
    calc
      _ = prodLaw.real {X | (∫ Z, f Z ∂prodLaw) + t ≤ f X} := by
        rw [hmean]
        exact hprob.symm
      _ ≤ _ := hprod.2.2 t ht

omit [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [Fintype ι] [DecidableEq ι] in
/-- The literal tensor threshold has exactly delta/8 centered failure budget. -/
theorem energyClipped_mcdiarmid_log_threshold (tau delta : ℝ)
    (htau : 0 < tau) (hdelta : 0 < delta) (hdelta8 : delta < 8) (hN : 0 < N) :
    Real.exp (-2 * N * (tau * Real.sqrt (2 * Real.log (8 / delta) / N)) ^ 2 /
      (2 * tau) ^ 2) = delta / 8 := by
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (8 / delta) := Real.log_nonneg
    ((le_div_iff₀ hdelta).mpr (by linarith))
  have hs := Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hlog) hN0.le)
  have he : -2 * N * (tau * Real.sqrt (2 * Real.log (8 / delta) / N)) ^ 2 /
      (2 * tau) ^ 2 = -Real.log (8 / delta) := by
    rw [mul_pow, hs]
    field_simp
  rw [he, Real.exp_neg, Real.exp_log (div_pos (by norm_num) hdelta), inv_div]

/-- The actual clipped tensor error has the exact source delta/8 budget under
original iid samples. Zero cutoff is treated directly, without division by zero. -/
theorem energyClippedCovarianceError_iid_source_threshold
    {Ω : Type*} [MeasurableSpace Ω] (hN : 0 < N)
    (μ : Measure E) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (Y : Fin N → Ω → E) (hLaw : ∀ i, ν.map (Y i) = μ) (hind : iIndepFun Y ν)
    (A : E → (EuclideanSpace ℝ ι →L[ℝ] H)) (hA : Continuous A)
    (tau C4 delta : ℝ) (htau : 0 ≤ tau) (hdelta : 0 < delta) (hdelta8 : delta < 8)
    (hfour : Integrable (fun x => finiteHilbertSchmidtNorm (A x) ^ 4) μ)
    (hC4 : (∫ x, finiteHilbertSchmidtNorm (A x) ^ 4 ∂μ) ≤ C4) :
    ν.real {ω | Real.sqrt (C4 / N) + tau * Real.sqrt (2 * Real.log (8 / delta) / N) <
      energyClippedCovarianceError μ A tau (fun i => Y i ω)} ≤ delta / 8 := by
  by_cases hzero : tau = 0
  · have hz (ω : Ω) : energyClippedCovarianceError μ A tau (fun i => Y i ω) = 0 := by
      have hb := (energyClippedCovarianceError_bounded_differences hN μ A tau htau).1
        (fun i => Y i ω)
      exact le_antisymm (hb.2.trans_eq (by rw [hzero, mul_zero])) hb.1
    have he : {ω | Real.sqrt (C4 / N) + tau * Real.sqrt (2 * Real.log (8 / delta) / N) <
        energyClippedCovarianceError μ A tau (fun i => Y i ω)} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, hz]
      exact iff_false_intro (not_lt.mpr (by positivity))
    rw [he, measureReal_empty]
    positivity
  have htau0 : 0 < tau := lt_of_le_of_ne htau (Ne.symm hzero)
  let F := fun ω => energyClippedCovarianceError μ A tau (fun i => Y i ω)
  let t := tau * Real.sqrt (2 * Real.log (8 / delta) / N)
  have hconc := energyClippedCovarianceError_iid_concentration hN μ ν Y hLaw hind
    A hA tau C4 htau hfour hC4
  have hs : {ω | Real.sqrt (C4 / N) + t < F ω} ⊆
      {ω | (∫ z, F z ∂ν) + t ≤ F ω} := by
    intro ω hω
    exact le_of_lt (lt_of_le_of_lt (add_le_add hconc.2.2.1 le_rfl) hω)
  exact ((measureReal_mono (μ := ν) hs).trans
    (hconc.2.2.2 t (mul_nonneg htau (Real.sqrt_nonneg _)))).trans_eq
      (energyClipped_mcdiarmid_log_threshold tau delta htau0 hdelta hdelta8 hN)

end PaperFormalization.Manuscript
