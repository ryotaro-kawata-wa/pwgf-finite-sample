import PaperFormalization.Manuscript.SourceExponentialMoment
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! # The actual population-kernel exponential grid event

One common history/path law is retained for both clouds and all finite grid
entries. Original unconditional all-real-order marginal bounds imply the
actual conditional exponential bounds by integration and Markov's inequality.
The conditional integrals are genuinely integrable on the resulting event.
Grid construction and identification of the original conditional path kernel
remain separate; no independence or desired conditional moment bound is input.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory
namespace PaperFormalization.Manuscript

variable {S P E ι : Type*} [MeasurableSpace S] [MeasurableSpace P]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Fintype ι]

set_option maxHeartbeats 1400000 in
/-- The source allocation A0=4Q/p0 yields one measurable population event
with failure at most p0. Both clouds share the same original conditional path
law. A joint AE path property is inherited conditionally outside one common
null set, with no measurability or regularity assumption added to that property. -/
theorem exists_population_kernel_exponential_grid_event
    (alpha K Q p0 : ℝ) (halpha : 0 < alpha) (hK : 0 < K)
    (hQ : 0 < Q) (hp0 : 0 < p0) (hcard : (Fintype.card ι : ℝ) ≤ Q)
    (ρ : Measure S) [IsProbabilityMeasure ρ] (κ : Kernel S P) [IsMarkovKernel κ]
    (Z : Fin 2 → ι → S × P → E) (hZ : ∀ c i, Measurable (Z c i))
    (hclass : ∀ c i, (ρ ⊗ₘ κ).map (Z c i) ∈ sourceMomentClass alpha K)
    (Model : S × P → Prop) (hModel : ∀ᵐ z ∂(ρ ⊗ₘ κ), Model z) :
    let b := sourcePopulationExponentialScale alpha K
    let A0 := 4 * Q / p0
    ∃ Good : Set S, MeasurableSet Good ∧ ρ.real Goodᶜ ≤ p0 ∧
      ∀ h ∈ Good,
        (∀ᵐ path ∂κ h, Model (h, path)) ∧
        ∀ c i, Integrable (fun path => Real.exp (‖Z c i (h, path)‖ ^ alpha / b ^ alpha)) (κ h) ∧
          (∫ path, Real.exp (‖Z c i (h, path)‖ ^ alpha / b ^ alpha) ∂κ h) ≤ A0 := by
  classical
  let b := sourcePopulationExponentialScale alpha K
  let A0 := 4 * Q / p0
  let f : E → ℝ := fun x => Real.exp (‖x‖ ^ alpha / b ^ alpha)
  let F : (Fin 2 × ι) → S × P → ℝ := fun j z => f (Z j.1 j.2 z)
  let M : (Fin 2 × ι) → S → ℝ := fun j h => ∫ path, F j (h, path) ∂κ h
  have hf : Measurable f := ((measurable_norm.pow_const alpha).div_const _).exp
  have hFmeas (j : Fin 2 × ι) : Measurable (F j) := hf.comp (hZ j.1 j.2)
  have hFpos (j : Fin 2 × ι) (z : S × P) : 0 ≤ F j z := Real.exp_nonneg _
  have hMpos (j : Fin 2 × ι) (h : S) : 0 ≤ M j h :=
    integral_nonneg (fun path => hFpos j (h, path))
  have hMmeas (j : Fin 2 × ι) : Measurable (M j) :=
    (hFmeas j).stronglyMeasurable.integral_kernel_prod_right'.measurable
  have hinput (j : Fin 2 × ι) : Integrable (F j) (ρ ⊗ₘ κ) ∧
      (∫ z, F j z ∂(ρ ⊗ₘ κ)) ≤ 2 := by
    have hh := sourceMomentClass_integrable_exp_and_integral_le_two alpha K halpha hK
      ((ρ ⊗ₘ κ).map (Z j.1 j.2)) (hclass j.1 j.2)
    have hi : Integrable (F j) (ρ ⊗ₘ κ) :=
      (integrable_map_measure hf.aestronglyMeasurable (hZ j.1 j.2).aemeasurable).mp hh.1
    refine ⟨hi, ?_⟩
    have hhb : (∫ x, f x ∂((ρ ⊗ₘ κ).map (Z j.1 j.2))) ≤ 2 := hh.2
    rw [integral_map (hZ j.1 j.2).aemeasurable hf.aestronglyMeasurable] at hhb
    exact hhb
  have hcond (j : Fin 2 × ι) :=
    (Measure.integrable_compProd_iff (hinput j).1.aestronglyMeasurable).mp (hinput j).1
  have hMint (j : Fin 2 × ι) : Integrable (M j) ρ := by
    have h := (hcond j).2
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hFpos j _)] using h
  have hMbound (j : Fin 2 × ι) : (∫ h, M j h ∂ρ) ≤ 2 := by
    rw [← Measure.integral_compProd (hinput j).1]
    exact (hinput j).2
  have hA : 0 < A0 := by dsimp [A0]; positivity
  have hnode (j : Fin 2 × ι) : ρ.real {h | A0 < M j h} ≤ 2 / A0 := by
    have hm := mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall (hMpos j)) (hMint j) A0
    have hle : ρ.real {h | A0 ≤ M j h} ≤ 2 / A0 := by
      apply (le_div_iff₀ hA).mpr
      nlinarith [hMbound j]
    have hsub : {h | A0 < M j h} ⊆ {h | A0 ≤ M j h} := by
      intro h hh
      change A0 ≤ M j h
      change A0 < M j h at hh
      exact hh.le
    exact (measureReal_mono hsub).trans hle
  let Bad : Set S := ⋃ j : Fin 2 × ι, {h | A0 < M j h}
  have hBad : MeasurableSet Bad := MeasurableSet.iUnion (fun j =>
    measurableSet_lt measurable_const (hMmeas j))
  have hBadBudget : ρ.real Bad ≤ p0 := by
    calc
      _ ≤ ∑ j : Fin 2 × ι, ρ.real {h | A0 < M j h} := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _j : Fin 2 × ι, 2 / A0 := Finset.sum_le_sum (fun j _ => hnode j)
      _ = 4 * (Fintype.card ι : ℝ) / A0 := by simp; ring
      _ ≤ 4 * Q / A0 := div_le_div_of_nonneg_right (by linarith) hA.le
      _ = p0 := by dsimp [A0]; field_simp
  have hall : ∀ᵐ h ∂ρ, (∀ j : Fin 2 × ι, Integrable (fun path => F j (h, path)) (κ h)) ∧
      ∀ᵐ path ∂κ h, Model (h, path) := by
    filter_upwards [ae_all_iff.mpr (fun j => (hcond j).1),
      Measure.ae_ae_of_ae_compProd hModel] with h hi hm
    exact ⟨hi, hm⟩
  obtain ⟨Null, hNullSub, hNullMeas, hNullZero⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hall)
  let Good := Nullᶜ ∩ Badᶜ
  have hbudget : ρ.real Goodᶜ ≤ p0 := by
    dsimp [Good]
    rw [compl_inter, compl_compl, compl_compl]
    have hz : ρ.real Null = 0 := by simp only [measureReal_def, hNullZero, ENNReal.toReal_zero]
    exact (measureReal_union_le Null Bad).trans (by simpa only [hz, zero_add] using hBadBudget)
  refine ⟨Good, hNullMeas.compl.inter hBad.compl, hbudget, ?_⟩
  intro h hh
  have hv : (∀ j : Fin 2 × ι, Integrable (fun path => F j (h, path)) (κ h)) ∧
      ∀ᵐ path ∂κ h, Model (h, path) := by
    by_contra hn
    exact hh.1 (hNullSub hn)
  refine ⟨hv.2, fun c i => ⟨hv.1 (c, i), ?_⟩⟩
  apply le_of_not_gt
  intro hbad
  exact hh.2 (mem_iUnion.mpr ⟨(c, i), hbad⟩)

end PaperFormalization.Manuscript
