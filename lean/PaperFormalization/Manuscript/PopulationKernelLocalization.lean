import PaperFormalization.Manuscript.PopulationKernelExponentialGrid
import PaperFormalization.Manuscript.PopulationExponentialMarginal
import PaperFormalization.Manuscript.PopulationTimeGrid

/-! # Actual conditional population moments over all closed branches

Finite joint marginal moment bounds and one actual AE branch-Lipschitz path
model imply one population-measurable event. Under its unchanged conditional
path kernel, the fixed-scale exponential bound, exact normalized exponential
bound, and original all-real-order marginal class hold simultaneously at all
branch times and their endpoint traces. The supplied common path kernel and
its interpretation as the original conditional law are not constructed here.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal ProbabilityTheory
namespace PaperFormalization.Manuscript

variable {S P E ι : Type*} [MeasurableSpace S] [MeasurableSpace P]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Fintype ι]

set_option maxHeartbeats 1600000 in
/-- A finite same-branch mesh and the actual AE branch-Lipschitz model give
all-time conditional moments. The mesh is geometric data, not a desired
conditional inequality; a source-specific mesh is instantiated separately. -/
theorem exists_population_kernel_localization_of_mesh
    (J : ℕ) (a btime : Fin (J+1) → ℝ) (B : ℝ≥0)
    (branch : ι → Fin (J+1)) (node : ι → ℝ)
    (hnode : ∀ i, node i ∈ Icc (a (branch i)) (btime (branch i)))
    (hcover : ∀ j t, t ∈ Icc (a j) (btime j) →
      ∃ i, branch i = j ∧ (B : ℝ) * |t-node i| ≤ 1)
    (alpha K Q p0 : ℝ) (halpha : 0 < alpha) (hK : 0 < K)
    (hQ : 1 ≤ Q) (hp0 : 0 < p0) (hp01 : p0 ≤ 1) (hcard : (Fintype.card ι : ℝ) ≤ Q)
    (ρ : Measure S) [IsProbabilityMeasure ρ] (κ : Kernel S P) [IsMarkovKernel κ]
    (Z : Fin 2 → Fin (J+1) → S × P → ℝ → E)
    (hZ : ∀ c j t, Measurable (fun z => Z c j z t))
    (hclass : ∀ c i, (ρ ⊗ₘ κ).map (fun z => Z c (branch i) z (node i)) ∈ sourceMomentClass alpha K)
    (hLip : ∀ᵐ z ∂(ρ ⊗ₘ κ), ∀ c j, LipschitzOnWith B (Z c j z) (Icc (a j) (btime j)))
    (Model : S × P → Prop) (hModel : ∀ᵐ z ∂(ρ ⊗ₘ κ), Model z) :
    let b := sourcePopulationExponentialScale alpha K
    let A0 := 4 * Q / p0
    let kpop := sourcePopulationNormalizedScale alpha b A0
    let Kpop := sourceExponentialMomentCoefficient alpha * kpop
    ∃ Good : Set S, MeasurableSet Good ∧ ρ.real Goodᶜ ≤ p0 ∧
      ∀ h ∈ Good, (∀ᵐ path ∂κ h, Model (h,path)) ∧
        ∀ c j t, t ∈ Icc (a j) (btime j) →
          Integrable (fun path => Real.exp (‖Z c j (h,path) t‖ ^ alpha /
            (sourcePopulationFlowFactor alpha * b ^ alpha))) (κ h) ∧
          (∫ path, Real.exp (‖Z c j (h,path) t‖ ^ alpha /
            (sourcePopulationFlowFactor alpha * b ^ alpha)) ∂κ h) ≤ A0 * Real.exp (b ^ (-alpha)) ∧
          Integrable (fun path => Real.exp ((‖Z c j (h,path) t‖ / kpop) ^ alpha)) (κ h) ∧
          (∫ path, Real.exp ((‖Z c j (h,path) t‖ / kpop) ^ alpha) ∂κ h) ≤ 2 ∧
          (κ h).map (fun path => Z c j (h,path) t) ∈ sourceMomentClass alpha Kpop := by
  let b := sourcePopulationExponentialScale alpha K
  let A0 := 4 * Q / p0
  let kpop := sourcePopulationNormalizedScale alpha b A0
  have hb1 : 1 ≤ b := le_max_left _ _
  have hb : 0 < b := by linarith
  have hA : 2 ≤ A0 := by
    apply (le_div_iff₀ hp0).mpr
    nlinarith
  have hk : 0 < kpop := (sourcePopulationNormalizedScale_pow alpha b A0 halpha hb hA).1
  have hfull : ∀ᵐ z ∂(ρ ⊗ₘ κ), Model z ∧
      ∀ c j, LipschitzOnWith B (Z c j z) (Icc (a j) (btime j)) := by
    filter_upwards [hModel,hLip] with z hm hl
    exact ⟨hm,hl⟩
  obtain ⟨Good,hGood,hbudget,hvalid⟩ := exists_population_kernel_exponential_grid_event
    alpha K Q p0 halpha hK (by linarith) hp0 hcard ρ κ
    (fun c i z => Z c (branch i) z (node i)) (fun c i => hZ c (branch i) (node i))
    hclass (fun z => Model z ∧ ∀ c j, LipschitzOnWith B (Z c j z) (Icc (a j) (btime j))) hfull
  refine ⟨Good,hGood,hbudget,?_⟩
  intro h hh
  have hv := hvalid h hh
  refine ⟨hv.1.mono (fun _ hx => hx.1),?_⟩
  intro c j t ht
  obtain ⟨i,hij,hnear⟩ := hcover j t ht
  have hnodej : node i ∈ Icc (a j) (btime j) := by simpa only [hij] using hnode i
  have hshift : ∀ᵐ path ∂κ h, ‖Z c j (h,path) t‖ ≤ ‖Z c (branch i) (h,path) (node i)‖ + 1 := by
    filter_upwards [hv.1] with path hp
    have hd := (hp.2 c j).dist_le_mul t ht (node i) hnodej
    have hn : ‖Z c j (h,path) t-Z c j (h,path) (node i)‖ ≤ (B : ℝ)*|t-node i| := by
      simpa only [dist_eq_norm, Real.norm_eq_abs] using hd
    have ht := norm_le_norm_add_norm_sub (Z c j (h,path) (node i)) (Z c j (h,path) t)
    rw [norm_sub_rev] at ht
    rw [hij]
    linarith
  have hmeas : Measurable (fun path => Z c j (h,path) t) :=
    (hZ c j t).comp measurable_prodMk_left
  have hflow := integrable_exp_population_flow (κ h)
    (fun path => Z c j (h,path) t) (fun path => Z c (branch i) (h,path) (node i))
    b alpha A0 hb halpha hmeas hshift (hv.2 c i).1 (hv.2 c i).2
  have hnormal := integrable_exp_population_normalized (κ h)
    (fun path => Z c j (h,path) t) b alpha A0 hb halpha hA hmeas hflow.1 hflow.2
  have hmoment := sourceMomentClass_map_of_exponential_moment (κ h)
    (fun path => Z c j (h,path) t) kpop alpha hk halpha hmeas hnormal.1 hnormal.2
  exact ⟨hflow.1,hflow.2,hnormal.1,hnormal.2,hmoment⟩

set_option maxHeartbeats 1800000 in
/-- The actual labelled source mesh supplies all geometric inputs internally.
Its exact Q=ceil((1+B)T)+2(J+1) controls one common population event, on which
both conditional marginals have the exact source exponential and moment scales
at every closed branch time, including both endpoint labels. -/
theorem exists_source_population_kernel_localization_event
    (J : ℕ) (T : ℝ) (a btime : Fin (J+1) → ℝ) (B : ℝ≥0)
    (hab : ∀ j, a j ≤ btime j) (hlen : ∑ j, (btime j-a j) ≤ T)
    (alpha K p0 : ℝ) (halpha : 0 < alpha) (hK : 0 < K)
    (hp0 : 0 < p0) (hp01 : p0 ≤ 1)
    (ρ : Measure S) [IsProbabilityMeasure ρ] (κ : Kernel S P) [IsMarkovKernel κ]
    (Z : Fin 2 → Fin (J+1) → S × P → ℝ → E)
    (hZ : ∀ c j t, Measurable (fun z => Z c j z t))
    (hclass : ∀ c (i : PopulationGridLabel B J a btime),
      (ρ ⊗ₘ κ).map (fun z => Z c i.1 z (populationGridTime B J a btime i)) ∈ sourceMomentClass alpha K)
    (hLip : ∀ᵐ z ∂(ρ ⊗ₘ κ), ∀ c j, LipschitzOnWith B (Z c j z) (Icc (a j) (btime j)))
    (Model : S × P → Prop) (hModel : ∀ᵐ z ∂(ρ ⊗ₘ κ), Model z) :
    let b := sourcePopulationExponentialScale alpha K
    let A0 := 4 * (populationGridBudget B J T : ℝ) / p0
    let kpop := sourcePopulationNormalizedScale alpha b A0
    let Kpop := sourceExponentialMomentCoefficient alpha * kpop
    ∃ Good : Set S, MeasurableSet Good ∧ ρ.real Goodᶜ ≤ p0 ∧
      ∀ h ∈ Good, (∀ᵐ path ∂κ h, Model (h,path)) ∧
        ∀ c j t, t ∈ Icc (a j) (btime j) →
          Integrable (fun path => Real.exp (‖Z c j (h,path) t‖ ^ alpha /
            (sourcePopulationFlowFactor alpha * b ^ alpha))) (κ h) ∧
          (∫ path, Real.exp (‖Z c j (h,path) t‖ ^ alpha /
            (sourcePopulationFlowFactor alpha * b ^ alpha)) ∂κ h) ≤ A0 * Real.exp (b ^ (-alpha)) ∧
          Integrable (fun path => Real.exp ((‖Z c j (h,path) t‖ / kpop) ^ alpha)) (κ h) ∧
          (∫ path, Real.exp ((‖Z c j (h,path) t‖ / kpop) ^ alpha) ∂κ h) ≤ 2 ∧
          (κ h).map (fun path => Z c j (h,path) t) ∈ sourceMomentClass alpha Kpop := by
  have hcover : ∀ j t, t ∈ Icc (a j) (btime j) →
      ∃ i : PopulationGridLabel B J a btime,
        i.1 = j ∧ (B : ℝ) * |t-populationGridTime B J a btime i| ≤ 1 := by
    intro j t ht
    obtain ⟨i,hi⟩ := exists_closedBranchGrid_near (a j) (btime j) (hab j)
      (populationBranchSubdivisions_pos B (a j) (btime j)) t ht
    refine ⟨⟨j,i⟩,rfl,?_⟩
    have htime := hi.trans (populationBranchSubdivisions_mesh_le B (a j) (btime j))
    have hm := mul_le_mul_of_nonneg_left htime B.coe_nonneg
    have hb : (B : ℝ)/(1+(B : ℝ)) ≤ 1 :=
      (div_le_one (by positivity : 0 < 1+(B : ℝ))).mpr (by linarith)
    have hm' : (B : ℝ) * |t-populationGridTime B J a btime ⟨j,i⟩| ≤ (B : ℝ)/(1+(B : ℝ)) := by
      simpa only [populationGridTime, Real.dist_eq, mul_one_div] using hm
    exact hm'.trans hb
  have hQ : 1 ≤ (populationGridBudget B J T : ℝ) := by
    exact_mod_cast (show 1 ≤ populationGridBudget B J T from
      (by omega : 1 ≤ 2).trans (populationGridBudget_two_le B J T))
  have hcard : (Fintype.card (PopulationGridLabel B J a btime) : ℝ) ≤ populationGridBudget B J T := by
    exact_mod_cast populationGridLabel_card_le B J T a btime hab hlen
  exact exists_population_kernel_localization_of_mesh J a btime B
    (fun i : PopulationGridLabel B J a btime => i.1) (populationGridTime B J a btime)
    (populationGridTime_mem B J a btime hab) hcover alpha K (populationGridBudget B J T) p0
    halpha hK hQ hp0 hp01 hcard ρ κ Z hZ hclass hLip Model hModel

end PaperFormalization.Manuscript
