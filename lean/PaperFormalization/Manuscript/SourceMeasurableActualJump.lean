import PaperFormalization.Manuscript.KernelActualJumpEvent
import PaperFormalization.Manuscript.SourceTensorCovarianceIntegrability

/-! # Actual conditional jump comparison without an assumed measurable failure

A measurable version is constructed from the actual paths and population
kernel. On one AE eligible-history event it equals the literal failure set.
The original seed law and updates are retained, never conditioned on sample
localization. A common AE model condition costs no additional probability.
-/
open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.Frobenius MatrixOrder ProbabilityTheory
set_option maxSynthPendingDepth 8
namespace PaperFormalization.Manuscript
variable {N d : ℕ} {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]
noncomputable local instance instMeasurableSpaceSourceMeasurableJumpParticles :
    MeasurableSpace (PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d)) := borel _
local instance instBorelSpaceSourceMeasurableJumpParticles :
    BorelSpace (PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩

variable (c C g p q K D alpha C3 : ℝ) (φ : ∀ n, EuclideanSpace ℝ (Fin d) → H n)
    (hc : 0 < c) (hC : 0 ≤ C) (hp : 1 < p) (hq : q < p) (hK : 0 < K) (hD : 1 ≤ D)
    (hφ : ∀ n, ContDiff ℝ 2 (φ n))
    (hgrowth : ∀ n z k, k ≤ 2 → ‖iteratedFDeriv ℝ k (φ n) z‖ ≤
      featureGrowth C g q n * (1 + ‖z‖ ^ (n + 1 - k)))
    (G : lp H 2 → ℝ) (U : Set (lp H 2)) (hU : IsOpen U)
    (hSU : measureMomentRegion (sourceWeightedFeatureMap c p φ) (sourceMomentClass alpha K) D ⊆ U)
    (hG : ContDiffOn ℝ 3 G U)
    (hthirdG : ∀ theta ∈ measureMomentRegion (sourceWeightedFeatureMap c p φ)
      (sourceMomentClass alpha K) D, ‖iteratedFDeriv ℝ 3 G theta‖ ≤ C3)
    (L : ℝ≥0) (hL : (L : ℝ) = sourceComparisonEnvelope c C g p q K D alpha C3 φ G)
    (halpha : 0 < alpha)
    (ρ : Measure S) (k : Kernel S Ω) [IsMarkovKernel k]
    (PopGood : Set S) (κ : Kernel S (EuclideanSpace ℝ (Fin d)))
    (X Y : S → PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d))
    (Xpost Ypost : S → Ω → PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d))
    (seed : S → Ω → EuclideanSpace ℝ (Fin N × Fin d))
    (hN : 0 < N) (eta u : ℝ) (heta : 0 ≤ eta) (hu : 0 < u) (hu1 : u < 1)
    (hgood : ∀ᵐ h ∂ρ, h ∈ PopGood →
      κ h ∈ sourceMomentClass alpha K ∧
      (k h).map (seed h) = stdGaussian (EuclideanSpace ℝ (Fin N × Fin d)) ∧
      ∀ hloc : (∀ i, ‖X h i‖ ≤ D) ∧ (∀ i, ‖Y h i‖ ≤ D),
        let J := sourceWeightedFeatureMap c p φ
        let A := fun z => stackedKernelMatrix (fun i =>
          actualMomentKernelMatrix J G (∫ x, J x ∂(κ h)) (Y h i) z)
        let Cov := populationGramCovariance (κ h) A
        let hMY := sourceEmpiricalKernelFactor_isHermitian c p K D alpha φ G U hU hSU
          (hG.of_le (by norm_num)) (Y h) hN hloc.2
        ∀ᵐ ω ∂k h,
          particleFlatten (Xpost h ω) = particleFlatten (X h) +
            eta • matrixEuclideanOperator (sourceEmpiricalKernelFactor c p φ G (X h)) (seed h ω) ∧
          particleFlatten (Ypost h ω) = particleFlatten (Y h) +
            eta • matrixEuclideanOperator (alignedCovarianceFactor hMY Cov) (seed h ω))

include hc hC hp hq hK hD hφ hgrowth hU hSU hG hthirdG hL halpha hN heta hu hu1 hgood

set_option maxHeartbeats 1600000 in
/-- Actual measurable pre/post particle maps, primitive source assumptions
and the unchanged conditional standard seed law produce a measurable common
jump-comparison event. No measurability hypothesis for the failure is supplied. -/
theorem exists_measurable_actual_source_jump_event [IsProbabilityMeasure ρ]
    (hPopGood : MeasurableSet PopGood) (hX : Measurable X) (hY : Measurable Y)
    (hXpost : Measurable (fun z : S × Ω => Xpost z.1 z.2))
    (hYpost : Measurable (fun z : S × Ω => Ypost z.1 z.2))
    (Model : S × Ω → Prop) (hModel : ∀ᵐ z ∂(ρ ⊗ₘ k), Model z) :
    ∃ Good : Set (S × Ω), MeasurableSet Good ∧ (ρ ⊗ₘ k).real Goodᶜ ≤ u ∧
      ∀ z ∈ Good, Model z ∧ z ∉ actualSourceJumpFailure c C g p q D φ G L
        PopGood (fun h => κ h) X Y Xpost Ypost eta u := by
  let J := sourceWeightedFeatureMap c p φ
  let Bad := kernelActualJumpFailureVersion c C g p q D φ G L PopGood κ
    X Y Xpost Ypost U (J 0) eta u
  let Actual := actualSourceJumpFailure c C g p q D φ G L PopGood
    (fun h => κ h) X Y Xpost Ypost eta u
  have hJ : ContDiff ℝ 2 J :=
    contDiff_sourceWeightedFeatureMap c C g p q φ hc hC hp hq hφ hgrowth
  have hG2 : ContDiffOn ℝ 2 G U := hG.of_le (by norm_num)
  have hanchor : J 0 ∈ U := hSU
    (zero_anchor_mem_measureMomentRegion J (sourceMomentClass alpha K) D (by linarith))
  have hBad : MeasurableSet Bad := measurableSet_kernelActualJumpFailureVersion
    c C g p q D φ (fun n => (hφ n).continuous) hJ.continuous
    (hJ.continuous_fderiv (by norm_num)) G L PopGood hPopGood κ X Y hX hY
    Xpost Ypost hXpost hYpost U hU hG2 (J 0) hanchor eta u
  have heq (h : S) (hc : h ∈ PopGood → κ h ∈ sourceMomentClass alpha K) (ω : Ω) :
      (h,ω) ∈ Bad ↔ (h,ω) ∈ Actual := by
    by_cases hh : h ∈ PopGood
    · have hclass := hc hh
      have ht : (∫ x, J x ∂κ h) ∈ U := hSU
        (population_integral_mem_measureMomentRegion J (sourceMomentClass alpha K) D (κ h) hclass)
      have hW := (sourceMomentClass_integrable_tensorCovariance_and_norm_sq
        c C g p q alpha K φ (by assumption) hC hp hq halpha hK hφ hgrowth (κ h) hclass).1
      exact kernelActualJumpFailureVersion_iff_actual c C g p q D φ G L PopGood κ X Y Xpost Ypost
        U hU hG2 (J 0) eta u h ht hW ω
    · simp only [Bad,Actual,kernelActualJumpFailureVersion,actualSourceJumpFailure,
        mem_setOf_eq,hh,false_and]
  have hcond := conditional_actual_source_jump_failure_bound c C g p q K D alpha C3 φ
    hc hC hp hq hK hD hφ hgrowth G U hU hSU hG hthirdG L hL halpha
    ρ k PopGood (fun h => κ h) X Y Xpost Ypost seed hN eta u heta hu hu1 hgood
  have hb : ∀ᵐ h ∂ρ, k h (Prod.mk h ⁻¹' Bad) ≤ ENNReal.ofReal u := by
    filter_upwards [hgood,hcond] with h hh hb
    have hs : Prod.mk h ⁻¹' Bad = {ω | (h,ω) ∈ Actual} := by
      ext ω
      exact heq h (fun hx => (hh hx).1) ω
    rw [hs]
    exact hb
  have hj := joint_kernel_failure_budget ρ k Bad hBad (fun _ => ENNReal.ofReal u) hb
  have hj' : (ρ ⊗ₘ k) Bad ≤ ENNReal.ofReal u := by simpa using hj
  have hbudget : (ρ ⊗ₘ k).real Bad ≤ u := by
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hj'
    simpa only [measureReal_def,ENNReal.toReal_ofReal hu.le] using ht
  have hfst : MeasurePreserving (Prod.fst : S × Ω → S) (ρ ⊗ₘ k) ρ :=
    ⟨measurable_fst,Measure.fst_compProd ρ k⟩
  have hmodel : ∀ᵐ z ∂(ρ ⊗ₘ k), Model z ∧ (z ∈ Bad ↔ z ∈ Actual) := by
    filter_upwards [hModel,hfst.quasiMeasurePreserving.ae hgood] with z hm hh
    exact ⟨hm,heq z.1 (fun hx => (hh hx).1) z.2⟩
  obtain ⟨Null,hNullSub,hNullMeas,hNullZero⟩ := exists_measurable_superset_of_null (ae_iff.mp hmodel)
  refine ⟨Nullᶜ ∩ Badᶜ,hNullMeas.compl.inter hBad.compl,?_,?_⟩
  · rw [compl_inter,compl_compl,compl_compl]
    have hz : (ρ ⊗ₘ k).real Null = 0 := by simp only [measureReal_def,hNullZero,ENNReal.toReal_zero]
    exact (measureReal_union_le Null Bad).trans (by simpa only [hz,zero_add] using hbudget)
  · intro z hz
    have hm : Model z ∧ (z ∈ Bad ↔ z ∈ Actual) := by
      by_contra hn
      exact hz.1 (hNullSub hn)
    exact ⟨hm.1,fun ha => hz.2 (hm.2.mpr ha)⟩
end PaperFormalization.Manuscript
