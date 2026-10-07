import PaperFormalization.Manuscript.SourceFiniteConditionalScale
import PaperFormalization.Manuscript.SourceReferencePathLaw

/-! # Identify full-history coefficient mixtures with original reference marginals

M13q verified unit (see CODEX_HANDOFF_M13Q.md). The full history can include the initial sample.
Its coefficient is a function of the population prefix only; it is NOT claimed
to be the conditional law of a sample given that full history. Mixing the
coefficient recovers the ORIGINAL reference marginal by original independence.
-/
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
namespace PaperFormalization.Manuscript
variable {O S Env Seed E : Type*} [MeasurableSpace O] [MeasurableSpace S]
  [MeasurableSpace Env] [MeasurableSpace Seed] [MeasurableSpace E]

/-- Marginalize the exact characteristic joint law. No real integral is used. -/
theorem source_characteristic_mixture
    (rho : Measure S) [IsProbabilityMeasure rho]
    (mu0 : Measure Seed) [IsProbabilityMeasure mu0]
    (Phi : S -> Seed -> E) (hPhi : Measurable (fun z : S × Seed => Phi z.1 z.2)) :
    (rho ⊗ₘ characteristicKernel mu0 Phi).map (Prod.snd : S × E -> E) =
      (rho.prod mu0).map (fun z => Phi z.1 z.2) := by
  rw [← single_characteristic_product_joint_law rho mu0 Phi hPhi,
    Measure.map_map measurable_snd (measurable_fst.prodMk hPhi)]
  rfl

/-- Although history can reveal the initial sample, its population coefficient
mixture is the unchanged reference law because the coefficient uses only past.
This is NOT a conditional-iid assertion for the larger sigma-field. -/
theorem source_full_history_coefficient_mixture
    (nu : Measure O) [IsProbabilityMeasure nu]
    (mu0 : Measure Seed) [IsProbabilityMeasure mu0]
    (history : O -> S) (past : S -> Env) (initial : O -> Seed)
    (hH : Measurable history) (hpast : Measurable past) (hinit : Measurable initial)
    (hind : IndepFun (past ∘ history) initial nu) (hlaw : nu.map initial = mu0)
    (Phi : Env -> Seed -> E) (hPhi : Measurable (fun z : Env × Seed => Phi z.1 z.2)) :
    ((nu.map history) ⊗ₘ characteristicKernel mu0 (fun h u => Phi (past h) u)).map
      (Prod.snd : S × E -> E) =
      nu.map (fun o => Phi (past (history o)) (initial o)) := by
  letI : IsProbabilityMeasure (nu.map history) := Measure.isProbabilityMeasure_map hH.aemeasurable
  have hfull : Measurable (fun z : S × Seed => Phi (past z.1) z.2) :=
    hPhi.comp ((hpast.comp measurable_fst).prodMk measurable_snd)
  have hjoint := hind.map_prod_eq_prod_map_map (hpast.comp hH).aemeasurable hinit.aemeasurable
  rw [hlaw] at hjoint
  change nu.map (fun o => (past (history o), initial o)) =
    (nu.map (past ∘ history)).prod mu0 at hjoint
  have hpair : Measurable (fun o => (past (history o), initial o)) :=
    (hpast.comp hH).prodMk hinit
  have hproj : ((nu.map history).prod mu0).map (Prod.map past (id : Seed -> Seed)) =
      (nu.map (past ∘ history)).prod mu0 := by
    rw [← Measure.map_prod_map (nu.map history) mu0 hpast measurable_id,
      Measure.map_map hpast hH, Measure.map_id]
  calc
    _ = ((nu.map history).prod mu0).map (fun z => Phi (past z.1) z.2) :=
      source_characteristic_mixture _ mu0 _ hfull
    _ = (((nu.map history).prod mu0).map (Prod.map past (id : Seed -> Seed))).map
        (fun z => Phi z.1 z.2) := by
      rw [Measure.map_map hPhi (by fun_prop)]
      rfl
    _ = ((nu.map (past ∘ history)).prod mu0).map (fun z => Phi z.1 z.2) := by rw [hproj]
    _ = (nu.map (fun o => (past (history o), initial o))).map (fun z => Phi z.1 z.2) := by
      rw [hjoint]
    _ = _ := by
      rw [Measure.map_map hPhi hpair]
      rfl

/-- The manuscript's unconditional reference moment bound supplies the finite
random scales required by actual Gram regularity, even for the full history. -/
theorem source_full_history_finite_scales_of_reference_moments
    [NormedAddCommGroup E] [BorelSpace E] [SecondCountableTopology E]
    (nu : Measure O) [IsProbabilityMeasure nu]
    (mu0 : Measure Seed) [IsProbabilityMeasure mu0]
    (history : O -> S) (past : S -> Env) (initial : O -> Seed)
    (hH : Measurable history) (hpast : Measurable past) (hinit : Measurable initial)
    (hind : IndepFun (past ∘ history) initial nu) (hlaw : nu.map initial = mu0)
    (Phi : Env -> Seed -> E) (hPhi : Measurable (fun z : Env × Seed => Phi z.1 z.2))
    (alpha K0 : Real) (halpha : 0 < alpha) (hK0 : 0 < K0)
    (hMoment : nu.map (fun o => Phi (past (history o)) (initial o)) ∈ sourceMomentClass alpha K0) :
    ∀ᵐ h ∂ nu.map history, ∃ K : Real, 0 < K ∧
      characteristicKernel mu0 (fun h u => Phi (past h) u) h ∈ sourceMomentClass alpha K := by
  letI : IsProbabilityMeasure (nu.map history) := Measure.isProbabilityMeasure_map hH.aemeasurable
  have hfull : Measurable (fun z : S × Seed => Phi (past z.1) z.2) :=
    hPhi.comp ((hpast.comp measurable_fst).prodMk measurable_snd)
  letI : IsMarkovKernel (characteristicKernel mu0 (fun h u => Phi (past h) u)) :=
    (characteristicKernel_properties mu0 _ hfull).1
  apply source_ae_finite_scale_of_mixture_class (nu.map history) _ alpha K0 halpha hK0
  rw [source_full_history_coefficient_mixture nu mu0 history past initial hH hpast hinit hind hlaw Phi hPhi]
  exact hMoment
end PaperFormalization.Manuscript
