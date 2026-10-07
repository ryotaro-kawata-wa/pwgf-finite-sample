import PaperFormalization.Manuscript.KernelNuclearResidual
import PaperFormalization.Manuscript.SourceCovarianceConcentration
import PaperFormalization.Manuscript.JointWhitenedSeed

/-! # An actual source covariance event under the unchanged history kernel

Population eligibility is imposed on the history, never by conditioning or
reweighting the sample law. A measurable version is identified with the
literal source residual on one common AE eligible-history event. Integrating
the proved fixed-law failure bound gives delta/4, with no measurable selection
of history-wise good sets and no global objective smoothness premise.
-/

open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal ProbabilityTheory Matrix.Norms.Frobenius
set_option maxSynthPendingDepth 8

namespace PaperFormalization.Manuscript

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω] {N d : ℕ}
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

noncomputable local instance instContinuousENormSourceConditionalCovarianceMatrix :
    ContinuousENorm (Matrix (Fin N × Fin d) (Fin N × Fin d) ℝ) :=
  SeminormedAddGroup.toContinuousENorm

set_option maxHeartbeats 1600000 in
/-- The actual source normalized nuclear covariance residual is controlled on
one measurable joint event. The original conditional class, iid and common-law
inputs are required only on eligible population histories. The exact source
node budget remains delta, with the stronger proved loss delta/4. -/
theorem exists_conditional_source_covariance_event
    (c C g p q K D alpha C3 delta : ℝ) (φ : ∀ n, EuclideanSpace ℝ (Fin d) → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p)
    (halpha : 0 < alpha) (hK : 0 < K) (hD : 1 ≤ D)
    (hφ : ∀ n, ContDiff ℝ 2 (φ n))
    (hgrowth : ∀ n z k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) z‖ ≤
      featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1 - k)))
    (G : lp H 2 → ℝ) (U : Set (lp H 2)) (hU : IsOpen U)
    (hSU : measureMomentRegion (sourceWeightedFeatureMap c p φ) (sourceMomentClass alpha K) D ⊆ U)
    (hG : ContDiffOn ℝ 3 G U)
    (hthirdG : ∀ theta ∈ measureMomentRegion (sourceWeightedFeatureMap c p φ)
      (sourceMomentClass alpha K) D, ‖iteratedFDeriv ℝ 3 G theta‖ ≤ C3)
    (L : ℝ≥0) (hL : (L : ℝ) = sourceComparisonEnvelope c C g p q K D alpha C3 φ G)
    (ρ : Measure S) [IsProbabilityMeasure ρ]
    (k : Kernel S Ω) [IsMarkovKernel k]
    (κ : Kernel S (EuclideanSpace ℝ (Fin d))) [IsMarkovKernel κ]
    (PopGood : Set S) (hPopGood : MeasurableSet PopGood)
    (X : S × Ω → Fin N → EuclideanSpace ℝ (Fin d))
    (hX : ∀ i, Measurable (fun z => X z i)) (hN : 0 < N)
    (hgood : ∀ᵐ h ∂ρ, h ∈ PopGood →
      κ h ∈ sourceMomentClass alpha K ∧
      (∀ i, (k h).map (fun ω => X (h,ω) i) = κ h) ∧
      iIndepFun (fun i ω => X (h,ω) i) (k h))
    (Model : S × Ω → Prop) (hModel : ∀ᵐ z ∂(ρ ⊗ₘ k), Model z)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) :
    let J := sourceWeightedFeatureMap c p φ
    let C4 := sourceHilbertSchmidtFourthMoment d c C g p q alpha K
    let tau := sourceSampleHilbertSchmidtEnvelope d c C g p q (sourceSampleRadius N alpha K delta)
    ∃ Good : Set (S × Ω), MeasurableSet Good ∧ (ρ ⊗ₘ k).real Goodᶜ ≤ delta / 4 ∧
      ∀ z ∈ Good, Model z ∧ (z.1 ∈ PopGood →
        matrixNuclearValue (populationCovarianceResidual (κ z.1) (X z)
          (fun x => stackedKernelMatrix (fun i =>
            actualMomentKernelMatrix J G (∫ y, J y ∂κ z.1) (X z i) x))) / N ≤
          (L : ℝ) ^ 2 * tau / Real.sqrt N *
            (2 * Real.sqrt C4 + tau * Real.sqrt (2 * Real.log (8 / delta)))) := by
  let J := sourceWeightedFeatureMap c p φ
  let C4 := sourceHilbertSchmidtFourthMoment d c C g p q alpha K
  let tau := sourceSampleHilbertSchmidtEnvelope d c C g p q (sourceSampleRadius N alpha K delta)
  let bound := (L : ℝ) ^ 2 * tau / Real.sqrt N *
    (2 * Real.sqrt C4 + tau * Real.sqrt (2 * Real.log (8 / delta)))
  let R := fun z : S × Ω => matrixNuclearValue (populationCovarianceResidual (κ z.1) (X z)
    (fun x => stackedKernelMatrix (fun i =>
      actualMomentKernelMatrix J G (∫ y, J y ∂κ z.1) (X z i) x))) / N
  let V := kernelNuclearResidualVersion κ X J G U (J 0)
  have hJ : ContDiff ℝ 2 J :=
    contDiff_sourceWeightedFeatureMap c C g p q φ hc hC hp hq hφ hgrowth
  have hG2 : ContDiffOn ℝ 2 G U := hG.of_le (by norm_num)
  have hanchor : J 0 ∈ U := hSU
    (zero_anchor_mem_measureMomentRegion J (sourceMomentClass alpha K) D (by linarith))
  have hV : Measurable V := measurable_kernelNuclearResidualVersion κ X hX J hJ.continuous
    (hJ.continuous_fderiv (by norm_num)) G U hU hG2 (J 0) hanchor
  have heq (h : S) (hclass : κ h ∈ sourceMomentClass alpha K) (ω : Ω) : V (h,ω) = R (h,ω) := by
    have htheta : (∫ x, J x ∂κ h) ∈ U := hSU
      (population_integral_mem_measureMomentRegion J (sourceMomentClass alpha K) D (κ h) hclass)
    have hW := (sourceMomentClass_integrable_tensorCovariance_and_norm_sq
      c C g p q alpha K φ hc hC hp hq halpha hK hφ hgrowth (κ h) hclass).1
    exact kernelNuclearResidualVersion_eq_actual κ X J G U hU hG2 (J 0) (h,ω) htheta hW
  let Bad : Set (S × Ω) := {z | z.1 ∈ PopGood ∧ bound < V z}
  have hBad : MeasurableSet Bad := (hPopGood.preimage measurable_fst).inter
    (measurableSet_lt measurable_const hV)
  have hnode : ∀ᵐ h ∂ρ, k h (Prod.mk h ⁻¹' Bad) ≤ ENNReal.ofReal (delta / 4) := by
    filter_upwards [hgood] with h hh
    by_cases heligible : h ∈ PopGood
    · have hdata := hh heligible
      have hb := source_nuclear_covariance_residual_failure_le
        c C g p q K D alpha C3 delta φ hc hC hp hq halpha hK hD hφ hgrowth
        G U hU hSU hG hthirdG L hL (κ h) hdata.1 (k h) (fun i ω => X (h,ω) i)
        hN hdata.2.1 hdata.2.2 hdelta hdelta1
      have he : Prod.mk h ⁻¹' Bad = {ω | bound < R (h,ω)} := by
        ext ω
        simp only [Bad, mem_preimage, mem_setOf_eq, heligible, true_and, heq h hdata.1 ω]
      rw [he, ← ofReal_measureReal (μ := k h)]
      exact ENNReal.ofReal_le_ofReal hb
    · have he : Prod.mk h ⁻¹' Bad = ∅ := by
        ext ω
        simp only [Bad, mem_preimage, mem_setOf_eq, heligible, false_and, mem_empty_iff_false]
      rw [he, measure_empty]
      exact bot_le
  have hj := joint_kernel_failure_budget ρ k Bad hBad (fun _ => ENNReal.ofReal (delta / 4)) hnode
  have hj' : (ρ ⊗ₘ k) Bad ≤ ENNReal.ofReal (delta / 4) := by simpa using hj
  have hbudgetBad : (ρ ⊗ₘ k).real Bad ≤ delta / 4 := by
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hj'
    simpa only [measureReal_def, ENNReal.toReal_ofReal (div_nonneg hdelta.le (by norm_num : (0 : ℝ) ≤ 4))] using ht
  have hfst : MeasurePreserving (Prod.fst : S × Ω → S) (ρ ⊗ₘ k) ρ :=
    ⟨measurable_fst, Measure.fst_compProd ρ k⟩
  have hactual : ∀ᵐ z ∂(ρ ⊗ₘ k), Model z ∧ (z.1 ∈ PopGood → V z = R z) := by
    filter_upwards [hModel, hfst.quasiMeasurePreserving.ae hgood] with z hm hh
    exact ⟨hm, fun he => heq z.1 (hh he).1 z.2⟩
  obtain ⟨Null, hNullSub, hNullMeas, hNullZero⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hactual)
  let Good := Nullᶜ ∩ Badᶜ
  refine ⟨Good, hNullMeas.compl.inter hBad.compl, ?_, ?_⟩
  · change (ρ ⊗ₘ k).real (Nullᶜ ∩ Badᶜ)ᶜ ≤ _
    rw [compl_inter, compl_compl, compl_compl]
    have hz : (ρ ⊗ₘ k).real Null = 0 := by simp only [measureReal_def, hNullZero, ENNReal.toReal_zero]
    exact (measureReal_union_le Null Bad).trans (by simpa only [hz, zero_add] using hbudgetBad)
  · intro z hz
    have ha : Model z ∧ (z.1 ∈ PopGood → V z = R z) := by
      by_contra hn
      exact hz.1 (hNullSub hn)
    refine ⟨ha.1, ?_⟩
    intro heligible
    change R z ≤ bound
    rw [← ha.2 heligible]
    exact le_of_not_gt (fun hb => hz.2 ⟨heligible, hb⟩)

end PaperFormalization.Manuscript
