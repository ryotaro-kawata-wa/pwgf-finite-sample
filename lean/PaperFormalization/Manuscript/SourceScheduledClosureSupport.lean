import PaperFormalization.Manuscript.SourceFinalReferenceTransport
import PaperFormalization.Manuscript.SourceCombinedEventBudget

/-! # Exact source scales and unchanged original inputs on the final extension
M13s verified unit; see CODEX_HANDOFF_M13S.md. The three p/8 allocations and the actual covariance/jump
allocation are retained. Independence is pulled back before any good event is
formed. Only finite intersections are used for the iid pullback argument.
-/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal ProbabilityTheory
namespace PaperFormalization.Manuscript

noncomputable def sourceFinalPopulationScale (J : Nat) (T alpha K0 pTotal : Real) (B : NNReal) : Real :=
  sourcePopulationNormalizedScale alpha (sourcePopulationExponentialScale alpha K0)
    (4*(populationGridBudget B J T : Real)/(pTotal/8))

noncomputable def sourceFinalMomentScale (J : Nat) (T alpha K0 pTotal : Real) (B : NNReal) : Real :=
  sourceExponentialMomentCoefficient alpha * sourceFinalPopulationScale J T alpha K0 pTotal B

noncomputable def sourceFinalGammaThreshold
    (J N : Nat) (T alpha K0 D pTotal c C g p q : Real) (B L : NNReal) : Real :=
  let b := sourcePopulationExponentialScale alpha K0
  let A0 := 4*(populationGridBudget B J T : Real)/(pTotal/8)
  sourceOriginalGammaThreshold J N T B L c C g p q alpha
    (sourceFinalMomentScale J T alpha K0 pTotal B) D
    (sourcePopulationFlowFactor alpha)⁻¹ b (A0*Real.exp (b^(-alpha))) (pTotal/8)

noncomputable def sourceFinalJumpCoefficient (J d : Nat) (c C g p q D pTotal : Real) (L : NNReal) : Real :=
  sourceJumpCoefficient d (featureDisplacementLambda c C g p q D L) L *
    sourceGaussianDeviation (pTotal/(8*((J : Real)+1)))

theorem sourceFinalScales_positive (J : Nat) (T alpha K0 pTotal : Real) (B : NNReal)
    (halpha : 0 < alpha) (hp : 0 < pTotal) (hp1 : pTotal < 1) :
    0 < sourceFinalPopulationScale J T alpha K0 pTotal B ∧
    0 < sourceFinalMomentScale J T alpha K0 pTotal B := by
  have hb : 0 < sourcePopulationExponentialScale alpha K0 :=
    lt_of_lt_of_le (by norm_num : (0:Real) < 1) (le_max_left _ _)
  have hQ : 1 ≤ (populationGridBudget B J T : Real) := by
    exact_mod_cast (show 1 ≤ populationGridBudget B J T from
      (by omega : 1 ≤ 2).trans (populationGridBudget_two_le B J T))
  have hA : 2 ≤ 4*(populationGridBudget B J T : Real)/(pTotal/8) := by
    apply (le_div_iff₀ (by positivity : 0 < pTotal/8)).mpr
    nlinarith
  have hk := (sourcePopulationNormalizedScale_pow alpha _ _ halpha hb hA).1
  refine ⟨hk,?_⟩
  unfold sourceFinalMomentScale
  apply mul_pos _ hk
  unfold sourceExponentialMomentCoefficient
  positivity

/-- An iid family remains iid on a measure-preserving extension. This is not
conditioning on any event. The proof uses only exact original probabilities. -/
theorem source_iIndepFun_pullback
    {O S E I : Type*} [MeasurableSpace O] [MeasurableSpace S] [MeasurableSpace E]
    (nu : Measure O) (rho : Measure S) (project : S -> O)
    (hp : MeasurePreserving project rho nu)
    (X : I -> O -> E) (hX : ∀ i, Measurable (X i)) (hiid : iIndepFun X nu) :
    iIndepFun (fun i z => X i (project z)) rho := by
  classical
  have hmeasure (A : Set O) (hA : MeasurableSet A) : rho (project ⁻¹' A) = nu A := by
    rw [<- hp.map_eq, Measure.map_apply hp.measurable hA]
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro s sets hsets
  have hA : MeasurableSet (⋂ i ∈ s, X i ⁻¹' sets i) := by
    apply s.measurableSet_biInter
    intro i hi
    exact hX i (hsets i hi)
  calc
    _ = rho (project ⁻¹' (⋂ i ∈ s, X i ⁻¹' sets i)) := by
      congr 1
      ext z
      simp only [mem_iInter,mem_preimage]
    _ = nu (⋂ i ∈ s, X i ⁻¹' sets i) := hmeasure _ hA
    _ = ∏ i ∈ s, nu (X i ⁻¹' sets i) := hiid.measure_inter_preimage_eq_mul s hsets
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (hmeasure _ (hX i (hsets i hi))).symm

/-- Every original random variable keeps its exact marginal on the tower. -/
theorem source_final_original_marginal
    {O A E : Type*} [MeasurableSpace O] [MeasurableSpace A] [MeasurableSpace E]
    (nu : Measure O) [IsProbabilityMeasure nu]
    (lambda : Measure A) [IsProbabilityMeasure lambda]
    (f : O -> E) (hf : Measurable f) (J : Nat) :
    (sourceAuxiliaryMeasure nu lambda J).map (fun z => f (sourceAuxiliaryOriginal J z)) = nu.map f := by
  rw [<- Function.comp_def, <- Measure.map_map hf (sourceAuxiliaryOriginal_preserving nu lambda J).measurable,
    (sourceAuxiliaryOriginal_preserving nu lambda J).map_eq]
end PaperFormalization.Manuscript
