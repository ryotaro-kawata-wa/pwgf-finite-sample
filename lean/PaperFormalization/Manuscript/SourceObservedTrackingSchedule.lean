import PaperFormalization.Manuscript.SourceObservedCovarianceSchedule
import PaperFormalization.Manuscript.SourceObservedJumpSchedule

/-! # Joint covariance and Gaussian-jump events on the unchanged original law

M13o declarations checked with the pinned toolchain; see verification/latest.json.
The two families of observations may use different history and innovation spaces.
The event is an intersection under the original measure, never a reconditioning.
No independence between observations, steps, or the two families is used.
The covariance conclusion retains its population-eligibility implication.
-/
open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal ProbabilityTheory Matrix.Norms.Frobenius
namespace PaperFormalization.Manuscript

variable {O : Type*} [MeasurableSpace O] {N d : ℕ}
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

set_option maxHeartbeats 2000000 in
/-- One original-law event supplies both observed schedule estimates with exact
combined complement budget J/(J+1) * (5 p / 32). Model is an AE condition only. -/
theorem exists_source_observed_tracking_schedule_event
    (J : ℕ) (c C g p q K D alpha C3 : ℝ) (φ : ∀ n, EuclideanSpace ℝ (Fin d) → H n)
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
    (hN : 0 < N) (ν : Measure O) [IsProbabilityMeasure ν]
    (SC VC SJ VJ : Fin J → Type*)
    [∀ j, MeasurableSpace (SC j)] [∀ j, MeasurableSpace (VC j)]
    [∀ j, MeasurableSpace (SJ j)] [∀ j, MeasurableSpace (VJ j)]
    (covView : ∀ j, SourceObservedCovarianceView N d alpha K ν (SC j) (VC j))
    (jumpView : ∀ j, SourceObservedJumpView c p K D alpha φ G U hU hSU
      (hG.of_le (by norm_num)) hN ν (SJ j) (VJ j))
    (pTotal : ℝ) (hpTotal : 0 < pTotal) (hpTotal1 : pTotal < 1)
    (Model : O → Prop) (hModel : ∀ᵐ ω ∂ν, Model ω) :
    let F := sourceWeightedFeatureMap c p φ
    ∃ Good : Set O, MeasurableSet Good ∧
      ν.real Goodᶜ ≤ ((J : ℝ) / ((J : ℝ) + 1)) * (5 * pTotal / 32) ∧
      ν.real Goodᶜ < pTotal / 4 ∧
      ∀ ω ∈ Good, Model ω ∧ (∀ j,
        let z := (covView j).observation ω
        z.1 ∈ (covView j).PopGood →
        matrixNuclearValue (populationCovarianceResidual ((covView j).κ z.1) ((covView j).X z)
          (fun x => stackedKernelMatrix (fun i =>
            actualMomentKernelMatrix F G (∫ y, F y ∂(covView j).κ z.1) ((covView j).X z i) x))) / N ≤
          sourcePrescribedCovarianceEnvelope J N d c C g p q alpha K L pTotal) ∧ ∀ j,
        (jumpView j).observation ω ∉ actualSourceJumpFailure c C g p q D φ G L
          (jumpView j).PopGood (fun h => (jumpView j).κ h) (jumpView j).X (jumpView j).Y
          (jumpView j).Xpost (jumpView j).Ypost (jumpView j).eta (pTotal / (8 * ((J : ℝ) + 1))) := by
  obtain ⟨GC, hGC, hCBudget, _, hCValid⟩ :=
    exists_source_observed_covariance_schedule_event
      J c C g p q K D alpha C3 φ hc hC hp hq halpha hK hD hφ hgrowth
      G U hU hSU hG hthirdG L hL hN ν SC VC covView pTotal hpTotal hpTotal1 Model hModel
  obtain ⟨GJ, hGJ, hJBudget, _, hJValid⟩ :=
    exists_source_observed_jump_schedule_event
      J c C g p q K D alpha C3 φ hc hC hp hq hK hD hφ hgrowth
      G U hU hSU hG hthirdG L hL halpha hN ν SJ VJ jumpView
      pTotal hpTotal hpTotal1 Model hModel
  have hbudget : ν.real (GC ∩ GJ)ᶜ ≤
      ((J : ℝ) / ((J : ℝ) + 1)) * (5 * pTotal / 32) := by
    rw [compl_inter]
    calc
      _ ≤ ν.real GCᶜ + ν.real GJᶜ := measureReal_union_le _ _
      _ ≤ ((J : ℝ) / ((J : ℝ) + 1)) * (pTotal / 32) +
          ((J : ℝ) / ((J : ℝ) + 1)) * (pTotal / 8) :=
        add_le_add hCBudget hJBudget
      _ = _ := by ring
  have hf : (J : ℝ) / ((J : ℝ) + 1) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith)
  have hstrict : ((J : ℝ) / ((J : ℝ) + 1)) * (5 * pTotal / 32) < pTotal / 4 := by
    nlinarith [mul_le_mul_of_nonneg_right hf (by positivity : 0 ≤ 5 * pTotal / 32)]
  refine ⟨GC ∩ GJ, hGC.inter hGJ, hbudget, hbudget.trans_lt hstrict, ?_⟩
  intro ω hω
  exact ⟨(hCValid ω hω.1).1, (hCValid ω hω.1).2, (hJValid ω hω.2).2⟩
end PaperFormalization.Manuscript
