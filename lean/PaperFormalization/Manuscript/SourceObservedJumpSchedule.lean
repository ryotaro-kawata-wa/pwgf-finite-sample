import PaperFormalization.Manuscript.SourceMeasurableActualJump

/-! # Actual source jump events observed from one original law

Each jump has its own history space, conditional sample space and population
kernel. Its measurable observation from the original system is explicitly
assumed to have the corresponding history-kernel joint law. This unit derives
source node events and their finite budget; it does not construct those views.
No independence across jumps and no desired recursion or event bound is input.
-/

open Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.Frobenius MatrixOrder ProbabilityTheory
set_option maxSynthPendingDepth 8
namespace PaperFormalization.Manuscript

variable {N d : ℕ} {O : Type*} [MeasurableSpace O]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

noncomputable local instance instMeasurableSpaceObservedJumpParticles :
    MeasurableSpace (PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d)) := borel _
local instance instBorelSpaceObservedJumpParticles :
    BorelSpace (PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩

/-- Primitive source data for one jump viewed from the original law. The
conditional seed is standard Gaussian under its unchanged kernel, and the
actual updates use the source empirical and aligned population factors. -/
structure SourceObservedJumpView
    (c p K D alpha : ℝ) (φ : ∀ n, EuclideanSpace ℝ (Fin d) → H n)
    (G : lp H 2 → ℝ) (U : Set (lp H 2)) (hU : IsOpen U)
    (hSU : measureMomentRegion (sourceWeightedFeatureMap c p φ)
      (sourceMomentClass alpha K) D ⊆ U)
    (hG : ContDiffOn ℝ 2 G U) (hN : 0 < N)
    (ν : Measure O) (S Ω : Type*) [MeasurableSpace S] [MeasurableSpace Ω] where
  ρ : Measure S
  probability : IsProbabilityMeasure ρ
  k : Kernel S Ω
  markov : IsMarkovKernel k
  κ : Kernel S (EuclideanSpace ℝ (Fin d))
  PopGood : Set S
  measurable_popGood : MeasurableSet PopGood
  X : S → PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d)
  Y : S → PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d)
  Xpost : S → Ω → PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d)
  Ypost : S → Ω → PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d)
  measurable_X : Measurable X
  measurable_Y : Measurable Y
  measurable_Xpost : Measurable (fun z : S × Ω => Xpost z.1 z.2)
  measurable_Ypost : Measurable (fun z : S × Ω => Ypost z.1 z.2)
  seed : S → Ω → EuclideanSpace ℝ (Fin N × Fin d)
  eta : ℝ
  eta_nonneg : 0 ≤ eta
  source_model : ∀ᵐ h ∂ρ, h ∈ PopGood →
    κ h ∈ sourceMomentClass alpha K ∧
    (k h).map (seed h) = stdGaussian (EuclideanSpace ℝ (Fin N × Fin d)) ∧
    ∀ hloc : (∀ i, ‖X h i‖ ≤ D) ∧ (∀ i, ‖Y h i‖ ≤ D),
      let F := sourceWeightedFeatureMap c p φ
      let A := fun z => stackedKernelMatrix (fun i =>
        actualMomentKernelMatrix F G (∫ x, F x ∂κ h) (Y h i) z)
      let Cov := populationGramCovariance (κ h) A
      let hMY := sourceEmpiricalKernelFactor_isHermitian c p K D alpha φ G U hU hSU
        hG (Y h) hN hloc.2
      ∀ᵐ ω ∂k h,
        particleFlatten (Xpost h ω) = particleFlatten (X h) +
          eta • matrixEuclideanOperator (sourceEmpiricalKernelFactor c p φ G (X h)) (seed h ω) ∧
        particleFlatten (Ypost h ω) = particleFlatten (Y h) +
          eta • matrixEuclideanOperator (alignedCovarianceFactor hMY Cov) (seed h ω)
  observation : O → S × Ω
  measurable_observation : Measurable observation
  observation_law : ν.map observation = ρ ⊗ₘ k

set_option maxHeartbeats 1800000 in
/-- Primitive source views give one measurable event on the original system
controlling every actual jump failure. The exact allocation u=p/[8(J+1)]
costs at most J/(J+1)*p/8, and an arbitrary AE model condition costs nothing.
Eligibility and localization remain exactly inside each literal source event.
The trace-dependent observation laws remain explicit hypotheses. -/
theorem exists_source_observed_jump_schedule_event
    (J : ℕ) (c C g p q K D alpha C3 : ℝ) (φ : ∀ n, EuclideanSpace ℝ (Fin d) → H n)
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
    (halpha : 0 < alpha) (hN : 0 < N)
    (ν : Measure O) [IsProbabilityMeasure ν]
    (S Ω : Fin J → Type*) [∀ j, MeasurableSpace (S j)] [∀ j, MeasurableSpace (Ω j)]
    (view : ∀ j, SourceObservedJumpView c p K D alpha φ G U hU hSU
      (hG.of_le (by norm_num)) hN ν (S j) (Ω j))
    (pTotal : ℝ) (hpTotal : 0 < pTotal) (hpTotal1 : pTotal < 1)
    (Model : O → Prop) (hModel : ∀ᵐ ω ∂ν, Model ω) :
    let u := pTotal / (8 * ((J : ℝ) + 1))
    ∃ Good : Set O, MeasurableSet Good ∧
      ν.real Goodᶜ ≤ ((J : ℝ) / ((J : ℝ) + 1)) * (pTotal / 8) ∧
      ν.real Goodᶜ < pTotal / 8 ∧
      ∀ ω ∈ Good, Model ω ∧ ∀ j,
        (view j).observation ω ∉ actualSourceJumpFailure c C g p q D φ G L
          (view j).PopGood (fun h => (view j).κ h) (view j).X (view j).Y
          (view j).Xpost (view j).Ypost (view j).eta u := by
  let u := pTotal / (8 * ((J : ℝ) + 1))
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u < 1 := by
    dsimp [u]
    apply (div_lt_one (by positivity : 0 < 8 * ((J : ℝ) + 1))).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) J]
  have hnode (j : Fin J) : ∃ Good : Set (S j × Ω j), MeasurableSet Good ∧
      ((view j).ρ ⊗ₘ (view j).k).real Goodᶜ ≤ u ∧
      ∀ z ∈ Good, z ∉ actualSourceJumpFailure c C g p q D φ G L
        (view j).PopGood (fun h => (view j).κ h) (view j).X (view j).Y
        (view j).Xpost (view j).Ypost (view j).eta u := by
    letI := (view j).probability
    letI := (view j).markov
    obtain ⟨Good, hmeas, hbudget, hvalid⟩ := exists_measurable_actual_source_jump_event
      c C g p q K D alpha C3 φ hc hC hp hq hK hD hφ hgrowth G U hU hSU hG hthirdG
      L hL halpha (view j).ρ (view j).k (view j).PopGood (view j).κ
      (view j).X (view j).Y (view j).Xpost (view j).Ypost (view j).seed hN
      (view j).eta u (view j).eta_nonneg hu hu1 (view j).source_model
      (view j).measurable_popGood (view j).measurable_X (view j).measurable_Y
      (view j).measurable_Xpost (view j).measurable_Ypost (fun _ => True) (by simp)
    exact ⟨Good, hmeas, hbudget, fun z hz => (hvalid z hz).2⟩
  choose Node hNodeMeas hNodeBudget hNodeValid using hnode
  let Fail : Set O := ⋃ j, (view j).observation ⁻¹' (Node j)ᶜ
  have hFailMeas : MeasurableSet Fail := MeasurableSet.iUnion (fun j =>
    (hNodeMeas j).compl.preimage (view j).measurable_observation)
  have hEach (j : Fin J) : ν.real ((view j).observation ⁻¹' (Node j)ᶜ) ≤ u := by
    have heq : ν ((view j).observation ⁻¹' (Node j)ᶜ) =
        ((view j).ρ ⊗ₘ (view j).k) ((Node j)ᶜ) := by
      rw [← (view j).observation_law,
        Measure.map_apply (view j).measurable_observation (hNodeMeas j).compl]
    simpa only [measureReal_def, heq] using hNodeBudget j
  have hFail : ν.real Fail ≤ ((J : ℝ) / ((J : ℝ) + 1)) * (pTotal / 8) := by
    calc
      _ ≤ ∑ j : Fin J, ν.real ((view j).observation ⁻¹' (Node j)ᶜ) :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ _j : Fin J, u := Finset.sum_le_sum (fun j _ => hEach j)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        dsimp [u]
        field_simp
  have hstrict : ((J : ℝ) / ((J : ℝ) + 1)) * (pTotal / 8) < pTotal / 8 := by
    have hfrac : (J : ℝ) / ((J : ℝ) + 1) < 1 :=
      (div_lt_one (by positivity : 0 < (J : ℝ) + 1)).mpr (by linarith)
    simpa using mul_lt_mul_of_pos_right hfrac (by positivity : 0 < pTotal / 8)
  obtain ⟨Null, hNullSub, hNullMeas, hNullZero⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hModel)
  let Good := Nullᶜ ∩ Failᶜ
  have hbudget : ν.real Goodᶜ ≤ ((J : ℝ) / ((J : ℝ) + 1)) * (pTotal / 8) := by
    dsimp [Good]
    rw [compl_inter, compl_compl, compl_compl]
    have hz : ν.real Null = 0 := by simp only [measureReal_def, hNullZero, ENNReal.toReal_zero]
    exact (measureReal_union_le Null Fail).trans (by simpa only [hz, zero_add] using hFail)
  refine ⟨Good, hNullMeas.compl.inter hFailMeas.compl, hbudget, hbudget.trans_lt hstrict, ?_⟩
  intro ω hω
  have hm : Model ω := by
    by_contra hn
    exact hω.1 (hNullSub hn)
  refine ⟨hm, ?_⟩
  intro j
  apply hNodeValid j
  by_contra hn
  exact hω.2 (mem_iUnion.mpr ⟨j, hn⟩)

end PaperFormalization.Manuscript
