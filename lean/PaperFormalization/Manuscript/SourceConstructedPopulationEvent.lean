import PaperFormalization.Manuscript.SourcePopulationPathSpace
import PaperFormalization.Manuscript.OriginalConditionalPathLaw
import PaperFormalization.Manuscript.OriginalPopulationEvent

/-! # Population localization from an actually constructed original path law

M13o declarations checked with the pinned toolchain; see verification/latest.json.
Inputs are raw original-system branches, their measurable point evaluations,
original-law grid moments, and one AE Lipschitz condition. A measurable common
path version and its regular conditional law are constructed internally.
No conditional moment inequality, joint-law identity, or localization event is
assumed. Both the environment event and an original-system pullback are returned.
This does NOT identify this population environment with any jump prehistory.
-/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal ProbabilityTheory
namespace PaperFormalization.Manuscript

set_option maxHeartbeats 2400000 in
/-- Construct the common conditional path law and derive the original source
all-time population event, including genuine integrability and exact scales. -/
theorem exists_source_constructed_population_event
    {O S : Type*} [MeasurableSpace O] [MeasurableSpace S]
    (nu : Measure O) [IsProbabilityMeasure nu]
    (environment : O → S) (henvironment : Measurable environment)
    (J d : ℕ) (T : ℝ) (a btime : Fin (J+1) → ℝ) (B : ℝ≥0)
    (hab : ∀ j, a j ≤ btime j) (hlen : ∑ j, (btime j-a j) ≤ T)
    (alpha K p0 : ℝ) (halpha : 0 < alpha) (hK : 0 < K)
    (hp0 : 0 < p0) (hp01 : p0 ≤ 1)
    (Z : Fin 2 → Fin (J+1) → O → ℝ → EuclideanSpace ℝ (Fin d))
    (hZ : ∀ c j t, Measurable (fun x => Z c j x t))
    (hclass : ∀ c (i : PopulationGridLabel B J a btime),
      nu.map (fun x => Z c i.1 x (populationGridTime B J a btime i)) ∈ sourceMomentClass alpha K)
    (hLip : ∀ᵐ x ∂nu, ∀ c j, LipschitzOnWith B (Z c j x) (Icc (a j) (btime j)))
    (Model : O → Prop) (hModel : ∀ᵐ x ∂nu, Model x) :
    ∃ paths : O → SourcePopulationPathSpace J d a btime, Measurable paths ∧
      (∀ᵐ x ∂nu, ∀ c j t, t ∈ Icc (a j) (btime j) →
        sourcePopulationPathEval (paths x) c j t = Z c j x t) ∧
      let law := originalConditionalPathLaw nu environment paths
      let b := sourcePopulationExponentialScale alpha K
      let A0 := 4 * (populationGridBudget B J T : ℝ) / p0
      let kpop := sourcePopulationNormalizedScale alpha b A0
      let Kpop := sourceExponentialMomentCoefficient alpha * kpop
      nu.map (fun x => (environment x, paths x)) = (nu.map environment) ⊗ₘ law ∧
      ∃ PopGood : Set S, MeasurableSet PopGood ∧ (nu.map environment).real PopGoodᶜ ≤ p0 ∧
        (∀ h ∈ PopGood, ∀ c j t, t ∈ Icc (a j) (btime j) →
          Integrable (fun path => Real.exp (‖sourcePopulationPathEval path c j t‖ ^ alpha /
            (sourcePopulationFlowFactor alpha * b ^ alpha))) (law h) ∧
          (∫ path, Real.exp (‖sourcePopulationPathEval path c j t‖ ^ alpha /
            (sourcePopulationFlowFactor alpha * b ^ alpha)) ∂law h) ≤ A0 * Real.exp (b ^ (-alpha)) ∧
          Integrable (fun path => Real.exp ((‖sourcePopulationPathEval path c j t‖ / kpop) ^ alpha)) (law h) ∧
          (∫ path, Real.exp ((‖sourcePopulationPathEval path c j t‖ / kpop) ^ alpha) ∂law h) ≤ 2 ∧
          (law h).map (fun path => sourcePopulationPathEval path c j t) ∈ sourceMomentClass alpha Kpop) ∧
        ∃ OriginalGood : Set O, MeasurableSet OriginalGood ∧ nu.real OriginalGoodᶜ ≤ p0 ∧
          ∀ x ∈ OriginalGood, Model x ∧ environment x ∈ PopGood := by
  classical
  obtain ⟨paths, hpaths, hversion⟩ := exists_source_population_path_version
    nu a btime B hab Z hZ hLip
  let law := originalConditionalPathLaw nu environment paths
  let Eval := fun c j (z : S × SourcePopulationPathSpace J d a btime) t =>
    sourcePopulationPathEval z.2 c j t
  letI : IsProbabilityMeasure (nu.map environment) :=
    Measure.isProbabilityMeasure_map henvironment.aemeasurable
  have hEval : ∀ c j t, Measurable (fun z => Eval c j z t) := by
    intro c j t
    exact (sourcePopulationPathEval_measurable c j t).comp measurable_snd
  have hobs : Measurable (fun x => (environment x, paths x)) := henvironment.prodMk hpaths
  have hjoint : nu.map (fun x => (environment x, paths x)) =
      (nu.map environment) ⊗ₘ law :=
    originalConditionalPathLaw_joint nu environment paths hpaths
  have hclass' : ∀ c (i : PopulationGridLabel B J a btime),
      ((nu.map environment) ⊗ₘ law).map
        (fun z => Eval c i.1 z (populationGridTime B J a btime i)) ∈ sourceMomentClass alpha K := by
    intro c i
    let t := populationGridTime B J a btime i
    have ht : t ∈ Icc (a i.1) (btime i.1) := populationGridTime_mem B J a btime hab i
    have heq : (fun x => sourcePopulationPathEval (paths x) c i.1 t) =ᵐ[nu]
        (fun x => Z c i.1 x t) := hversion.mono (fun x hx => hx c i.1 t ht)
    have hm : ((nu.map environment) ⊗ₘ law).map (fun z => Eval c i.1 z t) =
        nu.map (fun x => Z c i.1 x t) := by
      calc
        _ = nu.map (fun x => sourcePopulationPathEval (paths x) c i.1 t) := by
          rw [← hjoint]
          exact Measure.map_map (hEval c i.1 t) hobs
        _ = _ := Measure.map_congr heq
    rw [hm]
    exact hclass c i
  have hLipOriginal : ∀ᵐ x ∂nu, ∀ c j,
      LipschitzOnWith B (fun t => sourcePopulationPathEval (paths x) c j t)
        (Icc (a j) (btime j)) := by
    filter_upwards [hLip, hversion] with x hx heq
    intro c j
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    rw [heq c j s hs, heq c j t ht]
    exact (hx c j).dist_le_mul s hs t ht
  have hsupport : ∀ᵐ z ∂((nu.map environment) ⊗ₘ law),
      z.2 ∈ sourcePopulationPathLipschitz B := by
    rw [← hjoint]
    apply (ae_map_iff hobs.aemeasurable
      ((sourcePopulationPathLipschitz_isClosed (J := J) (d := d) (a := a) (b := btime) B).measurableSet.preimage
        measurable_snd)).mpr
    exact hLipOriginal.mono (fun x hx => (sourcePopulationPathLipschitz_iff B (paths x)).mpr hx)
  have hLipJoint : ∀ᵐ z ∂((nu.map environment) ⊗ₘ law),
      ∀ c j, LipschitzOnWith B (Eval c j z) (Icc (a j) (btime j)) :=
    hsupport.mono (fun z hz => (sourcePopulationPathLipschitz_iff B z.2).mp hz)
  obtain ⟨PopGood, hPopGood, hbudget, hvalid⟩ :=
    exists_source_population_kernel_localization_event
      J T a btime B hab hlen alpha K p0 halpha hK hp0 hp01
      (nu.map environment) law Eval hEval hclass' hLipJoint (fun _ => True) (by simp)
  obtain ⟨OriginalGood, hOriginalGood, hOriginalBudget, hOriginalValid⟩ :=
    exists_original_population_event nu (nu.map environment) environment henvironment rfl
      PopGood hPopGood p0 hbudget Model hModel
  refine ⟨paths, hpaths, hversion, hjoint, PopGood, hPopGood, hbudget, ?_,
    OriginalGood, hOriginalGood, hOriginalBudget, hOriginalValid⟩
  intro h hh
  exact (hvalid h hh).2
end PaperFormalization.Manuscript
