import PaperFormalization.Manuscript.SourceConditionalCovariance
import PaperFormalization.Manuscript.SourceCovarianceJumpBudget

/-! # Conditional prescribed-pretrace covariance budgets

Each pretrace has its own original population kernel and eligible-history
set. All node events live under one unchanged history/sample joint law.
The printed node allocation p/(8(J+1)) is retained, and the derived delta/4
node bound yields the sharper total loss J/(J+1)*p/32. No independence across
pretraces or measurable choice of history-wise good sets is required.
This unit uses the same history/sample kernel for every trace. Identifying
trace-dependent original prehistory observation kernels is separate; the
common population-environment characteristic product is a suitable route,
while Gaussian prehistory coupling uses its own conditioning.
-/

open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal ProbabilityTheory Matrix.Norms.Frobenius
set_option maxSynthPendingDepth 8

namespace PaperFormalization.Manuscript

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω] {N d : ℕ}
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

noncomputable local instance instContinuousENormSourceConditionalCovarianceBudgetMatrix :
    ContinuousENorm (Matrix (Fin N × Fin d) (Fin N × Fin d) ℝ) :=
  SeminormedAddGroup.toContinuousENorm

set_option maxHeartbeats 1600000 in
/-- The literal source residuals at all prescribed pretraces share one
measurable event with the printed total-budget allocation. Population
eligibility may differ by trace; the original joint law is never restricted. -/
theorem exists_conditional_source_prescribed_covariance_event
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
    (ρ : Measure S) [IsProbabilityMeasure ρ]
    (k : Kernel S Ω) [IsMarkovKernel k]
    (κ : Fin J → Kernel S (EuclideanSpace ℝ (Fin d))) [∀ j, IsMarkovKernel (κ j)]
    (PopGood : Fin J → Set S) (hPopGood : ∀ j, MeasurableSet (PopGood j))
    (X : Fin J → S × Ω → Fin N → EuclideanSpace ℝ (Fin d))
    (hX : ∀ j i, Measurable (fun z => X j z i)) (hN : 0 < N)
    (hgood : ∀ j, ∀ᵐ h ∂ρ, h ∈ PopGood j →
      κ j h ∈ sourceMomentClass alpha K ∧
      (∀ i, (k h).map (fun ω => X j (h,ω) i) = κ j h) ∧
      iIndepFun (fun i ω => X j (h,ω) i) (k h))
    (Model : S × Ω → Prop) (hModel : ∀ᵐ z ∂(ρ ⊗ₘ k), Model z)
    (pTotal : ℝ) (hpTotal : 0 < pTotal) (hpTotal1 : pTotal < 1) :
    let F := sourceWeightedFeatureMap c p φ
    ∃ Good : Set (S × Ω), MeasurableSet Good ∧
      (ρ ⊗ₘ k).real Goodᶜ ≤ ((J : ℝ) / ((J : ℝ) + 1)) * (pTotal / 32) ∧
      (ρ ⊗ₘ k).real Goodᶜ < pTotal / 8 ∧
      ∀ z ∈ Good, Model z ∧ ∀ j, z.1 ∈ PopGood j →
        matrixNuclearValue (populationCovarianceResidual (κ j z.1) (X j z)
          (fun x => stackedKernelMatrix (fun i =>
            actualMomentKernelMatrix F G (∫ y, F y ∂κ j z.1) (X j z i) x))) / N ≤
          sourcePrescribedCovarianceEnvelope J N d c C g p q alpha K L pTotal := by
  classical
  let F := sourceWeightedFeatureMap c p φ
  let u := pTotal / (8 * ((J : ℝ) + 1))
  let bound := sourcePrescribedCovarianceEnvelope J N d c C g p q alpha K L pTotal
  let R : Fin J → S × Ω → ℝ := fun j z =>
    matrixNuclearValue (populationCovarianceResidual (κ j z.1) (X j z)
      (fun x => stackedKernelMatrix (fun i =>
        actualMomentKernelMatrix F G (∫ y, F y ∂κ j z.1) (X j z i) x))) / N
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    apply (div_le_one (by positivity : 0 < 8 * ((J : ℝ) + 1))).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) J]
  have hnode (j : Fin J) : ∃ Good : Set (S × Ω), MeasurableSet Good ∧
      (ρ ⊗ₘ k).real Goodᶜ ≤ u / 4 ∧
      ∀ z ∈ Good, z.1 ∈ PopGood j → R j z ≤ bound := by
    obtain ⟨Good, hmeas, hb, hr⟩ := exists_conditional_source_covariance_event
      c C g p q K D alpha C3 u φ hc hC hp hq halpha hK hD hφ hgrowth
      G U hU hSU hG hthirdG L hL ρ k (κ j) (PopGood j) (hPopGood j) (X j) (hX j) hN
      (hgood j) (fun _ => True) (Filter.Eventually.of_forall (fun _ => trivial)) hu hu1
    exact ⟨Good, hmeas, hb, fun z hz => (hr z hz).2⟩
  choose Good hGoodMeas hGoodBudget hGoodBound using hnode
  let Fail : Set (S × Ω) := ⋃ j, (Good j)ᶜ
  have hFailMeas : MeasurableSet Fail := MeasurableSet.iUnion (fun j => (hGoodMeas j).compl)
  have hFail : (ρ ⊗ₘ k).real Fail ≤ ((J : ℝ) / ((J : ℝ) + 1)) * (pTotal / 32) := by
    calc
      _ ≤ ∑ j : Fin J, (ρ ⊗ₘ k).real (Good j)ᶜ := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _j : Fin J, u / 4 := Finset.sum_le_sum (fun j _ => hGoodBudget j)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        dsimp [u]
        field_simp
        ring
  have hstrict : ((J : ℝ) / ((J : ℝ) + 1)) * (pTotal / 32) < pTotal / 8 := by
    have hfrac : (J : ℝ) / ((J : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity : 0 < (J : ℝ) + 1)).mpr (by linarith)
    have hh := mul_le_mul_of_nonneg_right hfrac (by positivity : 0 ≤ pTotal / 32)
    nlinarith
  obtain ⟨Null, hNullSub, hNullMeas, hNullZero⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hModel)
  let AllGood := Nullᶜ ∩ Failᶜ
  have hbudget : (ρ ⊗ₘ k).real AllGoodᶜ ≤ ((J : ℝ) / ((J : ℝ) + 1)) * (pTotal / 32) := by
    dsimp [AllGood]
    rw [compl_inter, compl_compl, compl_compl]
    have hz : (ρ ⊗ₘ k).real Null = 0 := by simp only [measureReal_def, hNullZero, ENNReal.toReal_zero]
    exact (measureReal_union_le Null Fail).trans (by simpa only [hz, zero_add] using hFail)
  refine ⟨AllGood, hNullMeas.compl.inter hFailMeas.compl, hbudget, hbudget.trans_lt hstrict, ?_⟩
  intro z hz
  have hm : Model z := by
    by_contra hn
    exact hz.1 (hNullSub hn)
  refine ⟨hm, ?_⟩
  intro j heligible
  apply hGoodBound j z _ heligible
  by_contra hn
  exact hz.2 (mem_iUnion.mpr ⟨j, hn⟩)

end PaperFormalization.Manuscript
