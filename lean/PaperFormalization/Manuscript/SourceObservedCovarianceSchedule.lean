import PaperFormalization.Manuscript.SourceConditionalCovarianceBudget

/-! # Actual covariance observations under one original law

The conditional views may have different history and sample spaces. Each
original observation law is retained explicitly; the finite union never
requires independence between jumps, or conditioning on the good event.
-/
open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal ProbabilityTheory Matrix.Norms.Frobenius
namespace PaperFormalization.Manuscript

/-- One actual conditional iid pretrace view, with its unchanged joint law. -/
structure SourceObservedCovarianceView (N d : ℕ) (alpha K : ℝ)
    {O : Type*} [MeasurableSpace O] (ν : Measure O)
    (S Ω : Type*) [MeasurableSpace S] [MeasurableSpace Ω] where
  ρ : Measure S
  probability : IsProbabilityMeasure ρ
  k : Kernel S Ω
  markov : IsMarkovKernel k
  κ : Kernel S (EuclideanSpace ℝ (Fin d))
  population_markov : IsMarkovKernel κ
  PopGood : Set S
  measurable_popGood : MeasurableSet PopGood
  X : S × Ω → Fin N → EuclideanSpace ℝ (Fin d)
  measurable_X : ∀ i, Measurable (fun z => X z i)
  source_model : ∀ᵐ h ∂ρ, h ∈ PopGood →
    κ h ∈ sourceMomentClass alpha K ∧
    (∀ i, (k h).map (fun ω => X (h,ω) i) = κ h) ∧
    iIndepFun (fun i ω => X (h,ω) i) (k h)
  observation : O → S × Ω
  measurable_observation : Measurable observation
  observation_law : ν.map observation = ρ ⊗ₘ k

variable {O : Type*} [MeasurableSpace O] {N d : ℕ}
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

set_option maxHeartbeats 1600000 in
/-- Distinct actual observed iid views yield the exact prescribed covariance
budget on the original system. No event or concentration bound is an input. -/
theorem exists_source_observed_covariance_schedule_event
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
    (S Ω : Fin J → Type*) [∀ j, MeasurableSpace (S j)] [∀ j, MeasurableSpace (Ω j)]
    (view : ∀ j, SourceObservedCovarianceView N d alpha K ν (S j) (Ω j))
    (pTotal : ℝ) (hpTotal : 0 < pTotal) (hpTotal1 : pTotal < 1)
    (Model : O → Prop) (hModel : ∀ᵐ ω ∂ν, Model ω) :
    let F := sourceWeightedFeatureMap c p φ
    ∃ Good : Set O, MeasurableSet Good ∧
      ν.real Goodᶜ ≤ ((J : ℝ)/((J : ℝ)+1))*(pTotal/32) ∧
      ν.real Goodᶜ < pTotal/8 ∧
      ∀ ω ∈ Good, Model ω ∧ ∀ j,
        let z := (view j).observation ω
        z.1 ∈ (view j).PopGood →
        matrixNuclearValue (populationCovarianceResidual ((view j).κ z.1) ((view j).X z)
          (fun x => stackedKernelMatrix (fun i =>
            actualMomentKernelMatrix F G (∫ y, F y ∂(view j).κ z.1) ((view j).X z i) x))) / N ≤
          sourcePrescribedCovarianceEnvelope J N d c C g p q alpha K L pTotal := by
  classical
  let F := sourceWeightedFeatureMap c p φ
  let u := pTotal/(8*((J : ℝ)+1))
  let bound := sourcePrescribedCovarianceEnvelope J N d c C g p q alpha K L pTotal
  let R (j : Fin J) (z : S j × Ω j) :=
    matrixNuclearValue (populationCovarianceResidual ((view j).κ z.1) ((view j).X z)
      (fun x => stackedKernelMatrix (fun i =>
        actualMomentKernelMatrix F G (∫ y, F y ∂(view j).κ z.1) ((view j).X z i) x))) / N
  have hu : 0 < u := by dsimp [u];positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    apply (div_le_one (by positivity : 0 < 8*((J : ℝ)+1))).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) J]
  have hnode (j : Fin J) : ∃ Good : Set (S j × Ω j), MeasurableSet Good ∧
      ((view j).ρ ⊗ₘ (view j).k).real Goodᶜ ≤ u/4 ∧
      ∀ z ∈ Good, z.1 ∈ (view j).PopGood → R j z ≤ bound := by
    letI := (view j).probability
    letI := (view j).markov
    letI := (view j).population_markov
    obtain ⟨Good,hm,hb,hv⟩ := exists_conditional_source_covariance_event
      c C g p q K D alpha C3 u φ hc hC hp hq halpha hK hD hφ hgrowth
      G U hU hSU hG hthirdG L hL (view j).ρ (view j).k (view j).κ
      (view j).PopGood (view j).measurable_popGood (view j).X (view j).measurable_X hN
      (view j).source_model (fun _ => True) (by simp) hu hu1
    exact ⟨Good,hm,hb,fun z hz => (hv z hz).2⟩
  choose Node hNodeMeas hNodeBudget hNodeValid using hnode
  let Fail : Set O := ⋃ j, (view j).observation ⁻¹' (Node j)ᶜ
  have hFailMeas : MeasurableSet Fail := MeasurableSet.iUnion (fun j =>
    (hNodeMeas j).compl.preimage (view j).measurable_observation)
  have hEach (j : Fin J) : ν.real ((view j).observation ⁻¹' (Node j)ᶜ) ≤ u/4 := by
    have heq : ν ((view j).observation ⁻¹' (Node j)ᶜ) =
        ((view j).ρ ⊗ₘ (view j).k) ((Node j)ᶜ) := by
      rw [← (view j).observation_law,
        Measure.map_apply (view j).measurable_observation (hNodeMeas j).compl]
    simpa only [measureReal_def,heq] using hNodeBudget j
  have hFail : ν.real Fail ≤ ((J : ℝ)/((J : ℝ)+1))*(pTotal/32) := by
    calc
      _ ≤ ∑ j : Fin J, ν.real ((view j).observation ⁻¹' (Node j)ᶜ) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _j : Fin J, u/4 := Finset.sum_le_sum (fun j _ => hEach j)
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        dsimp [u]
        field_simp
        ring
  have hstrict : ((J : ℝ)/((J : ℝ)+1))*(pTotal/32) < pTotal/8 := by
    have hf : (J : ℝ)/((J : ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hf (by positivity : 0 ≤ pTotal/32)]
  obtain ⟨Null,hNullSub,hNullMeas,hNullZero⟩ := exists_measurable_superset_of_null (ae_iff.mp hModel)
  let Good := Nullᶜ ∩ Failᶜ
  have hbudget : ν.real Goodᶜ ≤ ((J : ℝ)/((J : ℝ)+1))*(pTotal/32) := by
    dsimp [Good]
    rw [compl_inter,compl_compl,compl_compl]
    have hz : ν.real Null=0 := by simp only [measureReal_def,hNullZero,ENNReal.toReal_zero]
    exact (measureReal_union_le Null Fail).trans (by simpa only [hz,zero_add] using hFail)
  refine ⟨Good,hNullMeas.compl.inter hFailMeas.compl,hbudget,hbudget.trans_lt hstrict,?_⟩
  intro ω hω
  have hm : Model ω := by
    by_contra hn
    exact hω.1 (hNullSub hn)
  refine ⟨hm,?_⟩
  intro j
  apply hNodeValid j
  by_contra hn
  exact hω.2 (mem_iUnion.mpr ⟨j,hn⟩)
end PaperFormalization.Manuscript
