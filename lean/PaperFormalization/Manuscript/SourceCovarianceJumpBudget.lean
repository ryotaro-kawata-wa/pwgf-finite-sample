import PaperFormalization.Manuscript.SourceCovarianceConcentration

/-! # The actual source covariance event at prescribed pre-jump traces

The total theorem budget is p, with the printed allocation u=p/(8(J+1)).
Each literal source nuclear residual has the already-proved sharper u/4
failure bound. Their finite union costs J/(J+1)*p/32, below the allocated p/8.
All observations share the same original sample law; no independence between
traces is required. A measurable hull handles merely AE measurable samples.
This fixed-law unit does not identify actual pre-traces or conditional laws.
-/

open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal Matrix.Norms.Frobenius
set_option maxSynthPendingDepth 8

namespace PaperFormalization.Manuscript

/-- The literal shared source HS envelope, using the total-budget allocation
p/(8(J+1)) at each of the J prescribed jump traces. -/
noncomputable def sourcePrescribedCovarianceEnvelope (J N d : ℕ)
    (c C g p q alpha K : ℝ) (L : ℝ≥0) (pTotal : ℝ) : ℝ :=
  let u := pTotal / (8 * ((J : ℝ) + 1))
  let tau := sourceSampleHilbertSchmidtEnvelope d c C g p q (sourceSampleRadius N alpha K u)
  (L : ℝ) ^ 2 * tau / Real.sqrt N *
    (2 * Real.sqrt (sourceHilbertSchmidtFourthMoment d c C g p q alpha K) +
      tau * Real.sqrt (2 * Real.log (8 / u)))

variable {N d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

noncomputable local instance instContinuousENormSourcePrescribedCovariance :
    ContinuousENorm (Matrix (Fin N × Fin d) (Fin N × Fin d) ℝ) :=
  SeminormedAddGroup.toContinuousENorm

set_option maxHeartbeats 1600000 in
/-- Original source hypotheses give one measurable event controlling every
literal nuclear residual at the prescribed traces. Each trace has its actual
population law, while the sample law is common and unchanged. No node-budget,
residual bound, residual measurability or between-trace independence is assumed.
The AE model predicate is retained with no additional probability loss. -/
theorem exists_source_prescribed_covariance_event
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
    (μ : Fin J → Measure (EuclideanSpace ℝ (Fin d)))
    (hμ : ∀ j, μ j ∈ sourceMomentClass alpha K)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (Y : Fin J → Fin N → Ω → EuclideanSpace ℝ (Fin d))
    (hN : 0 < N) (hLaw : ∀ j i, ν.map (Y j i) = μ j) (hind : ∀ j, iIndepFun (Y j) ν)
    (pTotal : ℝ) (hpTotal : 0 < pTotal) (hpTotal1 : pTotal < 1)
    (Model : Ω → Prop) (hModel : ∀ᵐ ω ∂ν, Model ω) :
    let F := sourceWeightedFeatureMap c p φ
    ∃ Good : Set Ω, MeasurableSet Good ∧
      ν.real Goodᶜ ≤ ((J : ℝ) / ((J : ℝ) + 1)) * (pTotal / 32) ∧
      ν.real Goodᶜ < pTotal / 8 ∧
      ∀ ω ∈ Good, Model ω ∧ ∀ j,
        matrixNuclearValue (populationCovarianceResidual (μ j) (fun i => Y j i ω)
          (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix F G
            (∫ x, F x ∂μ j) (Y j i ω) z))) / N ≤
          sourcePrescribedCovarianceEnvelope J N d c C g p q alpha K L pTotal := by
  let F := sourceWeightedFeatureMap c p φ
  let u := pTotal / (8 * ((J : ℝ) + 1))
  let bound := sourcePrescribedCovarianceEnvelope J N d c C g p q alpha K L pTotal
  let R : Fin J → Ω → ℝ := fun j ω =>
    matrixNuclearValue (populationCovarianceResidual (μ j) (fun i => Y j i ω)
      (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix F G
        (∫ x, F x ∂μ j) (Y j i ω) z))) / N
  let Bad : Fin J → Set Ω := fun j => {ω | bound < R j ω}
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by
    dsimp [u]
    apply (div_le_one (by positivity : 0 < 8 * ((J : ℝ) + 1))).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) J]
  have hnode (j : Fin J) : ν.real (Bad j) ≤ u / 4 := by
    exact source_nuclear_covariance_residual_failure_le
      c C g p q K D alpha C3 u φ hc hC hp hq halpha hK hD hφ hgrowth
      G U hU hSU hG hthirdG L hL (μ j) (hμ j) ν (Y j) hN (hLaw j) (hind j) hu hu1
  let Fail : Set Ω := ⋃ j, Bad j
  have hFail : ν.real Fail ≤ ((J : ℝ) / ((J : ℝ) + 1)) * (pTotal / 32) := by
    calc
      _ ≤ ∑ j : Fin J, ν.real (Bad j) := measureReal_iUnion_fintype_le Bad
      _ ≤ ∑ _j : Fin J, u / 4 := Finset.sum_le_sum (fun j _ => hnode j)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        dsimp [u]
        field_simp
        ring
  have hstrict : ((J : ℝ) / ((J : ℝ) + 1)) * (pTotal / 32) < pTotal / 8 := by
    have hfrac : (J : ℝ) / ((J : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity : 0 < (J : ℝ) + 1)).mpr (by linarith)
    have hsmall := mul_le_mul_of_nonneg_right hfrac (by positivity : 0 ≤ pTotal / 32)
    nlinarith
  obtain ⟨Null, hNullSub, hNullMeas, hNullZero⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hModel)
  let Cover := toMeasurable ν Fail
  have hCover : MeasurableSet Cover := measurableSet_toMeasurable _ _
  have hCoverReal : ν.real Cover = ν.real Fail := by
    simp only [Cover, measureReal_def, measure_toMeasurable]
  let Good := Nullᶜ ∩ Coverᶜ
  have hbudget : ν.real Goodᶜ ≤ ((J : ℝ) / ((J : ℝ) + 1)) * (pTotal / 32) := by
    dsimp [Good]
    rw [compl_inter, compl_compl, compl_compl]
    have hNullReal : ν.real Null = 0 := by simp only [measureReal_def, hNullZero, ENNReal.toReal_zero]
    exact (measureReal_union_le Null Cover).trans
      (by simpa only [hNullReal, zero_add, hCoverReal] using hFail)
  refine ⟨Good, hNullMeas.compl.inter hCover.compl, hbudget, hbudget.trans_lt hstrict, ?_⟩
  intro ω hω
  have hm : Model ω := by
    by_contra hn
    exact hω.1 (hNullSub hn)
  refine ⟨hm, ?_⟩
  intro j
  exact le_of_not_gt (fun hj => hω.2 (subset_toMeasurable ν Fail (mem_iUnion.mpr ⟨j, hj⟩)))

end PaperFormalization.Manuscript
