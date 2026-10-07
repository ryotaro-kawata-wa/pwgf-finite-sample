import PaperFormalization.Manuscript.OriginalCharacteristicEvent
import PaperFormalization.Manuscript.SourceRadiusChoice

/-! # One original-system event for characteristic concentration and localization

The previously constructed measurable characteristic event is pulled back
using the actual original independent-seed joint law. The population failure
budget and actual two-cloud radius theorem are combined under that same law.
A measurable cover of the continuum radius failure has exactly its outer
measure; no continuum-event measurability or localization independence is used.
-/
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators ProbabilityTheory
namespace PaperFormalization.Manuscript
variable {Env Seed Path Ω E : Type*} [MeasurableSpace Env] [MeasurableSpace Seed]
  [MeasurableSpace Path] [MeasurableSpace Ω] [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

set_option maxHeartbeats 800000 in
/-- Population, actual-radius, and derived characteristic-event budgets p/3
produce one measurable original-system event of total loss at most p. An AE
identification of the actual reference cloud with the common characteristic
paths is retained, so the resulting radius bound applies to their evaluations. -/
theorem exists_original_characteristic_population_radius_event
    (alpha K₀ CD : ℝ) (halpha : 0 < alpha) (hK₀ : 0 < K₀)
    (hCD : 2*Real.exp 1*K₀*(1+Real.log (4+2/(Real.exp 1*K₀)))^(1/alpha) ≤ CD)
    (J N : ℕ) (T p : ℝ) (B : ℝ≥0) (hN : 0 < N) (hT : 0 ≤ T) (hp : 0 < p) (hp1 : p ≤ 1)
    (a b : Fin (J+1) → ℝ) (hab : ∀ j, a j ≤ b j) (hlen : ∑ j, (b j-a j) ≤ T)
    (ν : Measure Ω) [IsProbabilityMeasure ν] (μ₀ : Measure Seed) [IsProbabilityMeasure μ₀]
    (V : Ω → Env) (U : Fin N → Ω → Seed) (hV : Measurable V) (hU : ∀ i, Measurable (U i))
    (hind : iIndepFun U ν) (henv : IndepFun V (fun ω i => U i ω) ν)
    (hlaw : ∀ i, ν.map (U i) = μ₀)
    (Φ : Env → Seed → Path) (hΦ : Measurable (fun z : Env × Seed => Φ z.1 z.2))
    (Z : Fin 2 → Fin N → Fin (J+1) → Ω → ℝ → E)
    (hLip : ∀ᵐ ω ∂ν, ∀ c i j, LipschitzOnWith B (Z c i j ω) (Icc (a j) (b j)))
    (hMarginal : ∀ c i j t, t ∈ Icc (a j) (b j) →
      ν.map (fun ω => Z c i j ω t) ∈ sourceMomentClass alpha K₀)
    (Y : Fin (J+1) → Env → Path → ℝ → E)
    (hRef : ∀ᵐ ω ∂ν, ∀ j i t, t ∈ Icc (a j) (b j) →
      Z 1 i j ω t = Y j (V ω) (Φ (V ω) (U i ω)) t)
    (PopGood : Set Env) (hPopGood : MeasurableSet PopGood)
    (hpopBudget : (ν.map V).real PopGoodᶜ ≤ p/3)
    (Good : Set (Env × (Fin N → Path))) (hGood : MeasurableSet Good)
    (hbudget : ((ν.map V) ⊗ₘ characteristicProductKernel (ι := Fin N) μ₀ Φ).real Goodᶜ ≤ p/3)
    (Model : Ω → Prop) (hModel : ∀ᵐ ω ∂ν, Model ω) :
    let D := CD*(1+Real.log (sourceGammaScale N J T B p))^(1/alpha)
    2*Real.exp 1*K₀ ≤ D ∧
    ∃ OriginalGood : Set Ω, MeasurableSet OriginalGood ∧ ν.real OriginalGoodᶜ ≤ p ∧
      ∀ ω ∈ OriginalGood, Model ω ∧ V ω ∈ PopGood ∧
        (V ω, fun i => Φ (V ω) (U i ω)) ∈ Good ∧
        (∀ c i j t, t ∈ Icc (a j) (b j) → ‖Z c i j ω t‖ ≤ D) ∧
        (∀ j i t, t ∈ Icc (a j) (b j) → ‖Y j (V ω) (Φ (V ω) (U i ω)) t‖ ≤ D) := by
  let D := CD*(1+Real.log (sourceGammaScale N J T B p))^(1/alpha)
  have hr := source_two_cloud_fixed_radius_tail_le alpha K₀ CD halpha hK₀ hCD
    J N T p B hN hT hp hp1 a b hab hlen ν Z hLip hMarginal
  let Bad : Set Ω := {ω | ∃ c i j t, t ∈ Icc (a j) (b j) ∧ D < ‖Z c i j ω t‖}
  let Cover := toMeasurable ν Bad
  have hCover : MeasurableSet Cover := measurableSet_toMeasurable ν Bad
  have hCoverBudget : ν.real Cover ≤ p/3 := by
    simpa only [Cover, measureReal_def, measure_toMeasurable] using hr.2
  have hmodel : ∀ᵐ ω ∂ν, Model ω ∧ ∀ j i t, t ∈ Icc (a j) (b j) →
      Z 1 i j ω t = Y j (V ω) (Φ (V ω) (U i ω)) t := by
    filter_upwards [hModel,hRef] with ω hm href
    exact ⟨hm,href⟩
  obtain ⟨Base,hBase,hBaseBudget,hBaseValid⟩ := exists_original_characteristic_event
    ν μ₀ V U hV hU hind henv hlaw Φ hΦ Good hGood (p/3) hbudget
    (fun ω => Model ω ∧ ∀ j i t, t ∈ Icc (a j) (b j) →
      Z 1 i j ω t = Y j (V ω) (Φ (V ω) (U i ω)) t) hmodel
  have hPop : MeasurableSet (V ⁻¹' PopGood) := hPopGood.preimage hV
  have hPopBudget : ν.real ((V ⁻¹' PopGood)ᶜ) ≤ p/3 := by
    rw [← preimage_compl, ← map_measureReal_apply hV hPopGood.compl]
    exact hpopBudget
  refine ⟨hr.1, (Base ∩ (V ⁻¹' PopGood)) ∩ Coverᶜ, (hBase.inter hPop).inter hCover.compl, ?_, ?_⟩
  · rw [compl_inter, compl_inter, compl_compl]
    calc
      _ ≤ ν.real (Baseᶜ ∪ (V ⁻¹' PopGood)ᶜ) + ν.real Cover := measureReal_union_le _ _
      _ ≤ (ν.real Baseᶜ + ν.real ((V ⁻¹' PopGood)ᶜ)) + ν.real Cover :=
        add_le_add (measureReal_union_le _ _) le_rfl
      _ ≤ p := by linarith
  · intro ω hω
    have hv := hBaseValid ω hω.1.1
    have hnorm : ∀ c i j t, t ∈ Icc (a j) (b j) → ‖Z c i j ω t‖ ≤ D := by
      intro c i j t ht
      apply le_of_not_gt
      intro hbad
      exact hω.2 (subset_toMeasurable ν Bad ⟨c,i,j,t,ht,hbad⟩)
    refine ⟨hv.1.1,hω.1.2,hv.2,hnorm,?_⟩
    intro j i t ht
    rw [← hv.1.2 j i t ht]
    exact hnorm 1 i j t ht
end PaperFormalization.Manuscript
