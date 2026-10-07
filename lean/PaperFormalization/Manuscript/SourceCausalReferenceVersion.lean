import PaperFormalization.Manuscript.SourceReferencePathIdentification

/-! # Causal reference paths without all-history continuity assumptions

M13p verified unit (see CODEX_HANDOFF_M13P.md). This is the AE version used for the manuscript
model. The optional pointwise-continuous bundling theorem is not required.
Branch Lipschitz regularity is assumed only under the ORIGINAL product law of
population innovations and one independent initial seed. Measurable null-set
repair is simultaneous across all branches and times.
-/
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ProbabilityTheory
namespace PaperFormalization.Manuscript
variable {Env W : Type*} [MeasurableSpace Env] [MeasurableSpace W] {J d : ℕ}

/-- Construct the measurable causal characteristic PATH from the raw recursive
branches on their original law, allowing arbitrary behavior on a null set. -/
theorem exists_source_causal_reference_path_version
    (ρ : Measure Env) (mu0 : Measure (EuclideanSpace ℝ (Fin d)))
    (a b : Fin (J+1) -> ℝ) (hab : ∀ j, a j ≤ b j) (B : ℝ≥0) (tau : ℕ -> ℝ)
    (flow : (n : ℕ) -> (Fin n -> W) -> ℝ -> EuclideanSpace ℝ (Fin d) -> EuclideanSpace ℝ (Fin d))
    (jump : (n : ℕ) -> (Fin n -> W) -> W -> EuclideanSpace ℝ (Fin d) -> EuclideanSpace ℝ (Fin d))
    (hflow : ∀ n t, Measurable (fun z : (Fin n -> W) × EuclideanSpace ℝ (Fin d) => flow n z.1 t z.2))
    (hjump : ∀ n, Measurable (fun z : ((Fin n -> W) × W) × EuclideanSpace ℝ (Fin d) => jump n z.1.1 z.1.2 z.2))
    (past : (j : Fin (J+1)) -> Env -> Fin j.val -> W) (hpast : ∀ j, Measurable (past j))
    (hLip : ∀ᵐ z ∂ρ.prod mu0, ∀ j,
      LipschitzOnWith B (sourceReferenceBranch tau flow jump j.val (past j z.1) z.2) (Icc (a j) (b j))) :
    ∃ Phi : Env -> EuclideanSpace ℝ (Fin d) -> SourceReferencePathSpace J d a b,
      Measurable (fun z : Env × EuclideanSpace ℝ (Fin d) => Phi z.1 z.2) ∧
      ∀ᵐ z ∂ρ.prod mu0, ∀ j t, t ∈ Icc (a j) (b j) ->
        sourceReferencePathEval (Phi z.1 z.2) j t = sourceReferenceBranch tau flow jump j.val (past j z.1) z.2 t := by
  let Z := fun (_ : Fin 2) (j : Fin (J+1)) (z : Env × EuclideanSpace ℝ (Fin d)) t =>
    sourceReferenceBranch tau flow jump j.val (past j z.1) z.2 t
  have hZ : ∀ c j t, Measurable (fun z => Z c j z t) := by
    intro c j t
    exact (sourceReferenceBranch_measurable tau flow jump hflow hjump j.val t).comp
      ((hpast j).comp measurable_fst |>.prodMk measurable_snd)
  have hL : ∀ᵐ z ∂ρ.prod mu0, ∀ c j, LipschitzOnWith B (Z c j z) (Icc (a j) (b j)) := by
    filter_upwards [hLip] with z hz
    exact fun _ j => hz j
  obtain ⟨paths, hpaths, heq⟩ := exists_source_population_path_version (ρ.prod mu0) a b B hab Z hZ hL
  refine ⟨fun e u => paths (e,u) 0, (measurable_pi_apply 0).comp hpaths, ?_⟩
  filter_upwards [heq] with z hz
  intro j t ht
  simpa only [sourceReferencePathEval, sourcePopulationPathEval, dif_pos ht] using hz 0 j t ht

/-- The repaired characteristic agrees with every actual initial coordinate on
one original-law event. Only finitely many particles are intersected; the time
quantifier is already INSIDE the AE product-law identity. -/
theorem source_independent_seed_path_agreement
    {O Seed : Type*} [MeasurableSpace O] [MeasurableSpace Seed]
    {I : Type*} [Countable I]
    (nu : Measure O) [IsProbabilityMeasure nu] (mu0 : Measure Seed) [IsProbabilityMeasure mu0]
    (environment : O -> Env) (initial : I -> O -> Seed)
    (henv : Measurable environment) (hinit : ∀ i, Measurable (initial i))
    (hind : IndepFun environment (fun w i => initial i w) nu)
    (hlaw : ∀ i, nu.map (initial i) = mu0)
    (Property : Env -> Seed -> Prop)
    (hProperty : ∀ᵐ z ∂(nu.map environment).prod mu0, Property z.1 z.2) :
    ∀ᵐ w ∂nu, ∀ i, Property (environment w) (initial i w) := by
  apply ae_all_iff.mpr
  intro i
  have hi := original_environment_independent_initial_coordinate nu environment initial hind i
  have hjoint := hi.map_prod_eq_prod_map_map henv.aemeasurable (hinit i).aemeasurable
  rw [hlaw i] at hjoint
  apply ae_of_ae_map (μ := nu) (p := fun z : Env × Seed => Property z.1 z.2)
    (henv.prodMk (hinit i)).aemeasurable
  rw [hjoint]
  exact hProperty


/-- Fubini is applied to one all-time agreement event. Thus every actual raw
marginal equals the measurable characteristic marginal on one environment set,
without separately intersecting time-indexed exceptional sets. -/
theorem source_reference_version_all_marginal_laws
    {Seed E I : Type*} [MeasurableSpace Seed] [MeasurableSpace E]
    (ρ : Measure Env) [IsProbabilityMeasure ρ]
    (mu0 : Measure Seed) [IsProbabilityMeasure mu0]
    (represented raw : Env -> Seed -> I -> E)
    (hAgreement : ∀ᵐ z ∂ρ.prod mu0, ∀ i, represented z.1 z.2 i = raw z.1 z.2 i) :
    ∀ᵐ e ∂ρ, ∀ i,
      mu0.map (fun u => represented e u i) = mu0.map (fun u => raw e u i) := by
  have hj : ∀ᵐ z ∂(ρ ⊗ₘ Kernel.const Env mu0), ∀ i,
      represented z.1 z.2 i = raw z.1 z.2 i := by
    simpa only [Measure.compProd_const] using hAgreement
  have hf := Measure.ae_ae_of_ae_compProd hj
  filter_upwards [hf] with e he
  intro i
  apply Measure.map_congr
  filter_upwards [he] with u hu
  exact hu i

end PaperFormalization.Manuscript
