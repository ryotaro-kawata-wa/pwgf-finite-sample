import PaperFormalization.Manuscript.SourceScheduledCovariance
import PaperFormalization.Manuscript.SourceOriginalJumpView
import PaperFormalization.Manuscript.SourceAuxiliaryTower
import PaperFormalization.Manuscript.SourceGluedTrackingPaths
import PaperFormalization.Manuscript.SourceOriginalReferenceGamma
import PaperFormalization.Manuscript.SourceCausalReferenceVersion

/-! M13p boundary diagnostics; compiled and axiom-audited. See CODEX_HANDOFF_M13P.md. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ProbabilityTheory NNReal
open PaperFormalization.Manuscript

#check PaperFormalization.Manuscript.source_compProd_auxiliary_associate
#print axioms PaperFormalization.Manuscript.source_compProd_auxiliary_associate
#check PaperFormalization.Manuscript.source_original_auxiliary_observation_law
#print axioms PaperFormalization.Manuscript.source_original_auxiliary_observation_law
#check PaperFormalization.Manuscript.source_original_auxiliary_preserves
#print axioms PaperFormalization.Manuscript.source_original_auxiliary_preserves
#check PaperFormalization.Manuscript.sourceCovarianceView_lift_auxiliary
#print axioms PaperFormalization.Manuscript.sourceCovarianceView_lift_auxiliary
#check PaperFormalization.Manuscript.SourceAuxiliarySpace
#print axioms PaperFormalization.Manuscript.SourceAuxiliarySpace
#check PaperFormalization.Manuscript.sourceAuxiliaryMeasurable
#print axioms PaperFormalization.Manuscript.sourceAuxiliaryMeasurable
#check PaperFormalization.Manuscript.sourceAuxiliaryMeasure
#print axioms PaperFormalization.Manuscript.sourceAuxiliaryMeasure
#check PaperFormalization.Manuscript.sourceAuxiliaryMeasure_probability
#print axioms PaperFormalization.Manuscript.sourceAuxiliaryMeasure_probability
#check PaperFormalization.Manuscript.sourceAuxiliaryProjection
#print axioms PaperFormalization.Manuscript.sourceAuxiliaryProjection
#check PaperFormalization.Manuscript.sourceAuxiliaryProjection_preserving
#print axioms PaperFormalization.Manuscript.sourceAuxiliaryProjection_preserving
#check PaperFormalization.Manuscript.sourceAuxiliaryOriginal
#print axioms PaperFormalization.Manuscript.sourceAuxiliaryOriginal
#check PaperFormalization.Manuscript.sourceAuxiliaryOriginal_preserving
#print axioms PaperFormalization.Manuscript.sourceAuxiliaryOriginal_preserving
#check PaperFormalization.Manuscript.sourceAuxiliaryProjection_original
#print axioms PaperFormalization.Manuscript.sourceAuxiliaryProjection_original
#check PaperFormalization.Manuscript.exists_source_auxiliary_prefix
#print axioms PaperFormalization.Manuscript.exists_source_auxiliary_prefix
#check PaperFormalization.Manuscript.sourceCovarianceView_on_auxiliaryTower
#print axioms PaperFormalization.Manuscript.sourceCovarianceView_on_auxiliaryTower
#check PaperFormalization.Manuscript.sourceCovarianceView_on_auxiliaryTower_observation
#print axioms PaperFormalization.Manuscript.sourceCovarianceView_on_auxiliaryTower_observation
#check PaperFormalization.Manuscript.sourceJumpView_pullback
#print axioms PaperFormalization.Manuscript.sourceJumpView_pullback
#check PaperFormalization.Manuscript.exists_source_jump_views_on_common_auxiliary_tower
#print axioms PaperFormalization.Manuscript.exists_source_jump_views_on_common_auxiliary_tower
#check PaperFormalization.Manuscript.sourceGlue
#print axioms PaperFormalization.Manuscript.sourceGlue
#check PaperFormalization.Manuscript.source_jumpCount_on_branch
#print axioms PaperFormalization.Manuscript.source_jumpCount_on_branch
#check PaperFormalization.Manuscript.sourceGlue_on_branch
#print axioms PaperFormalization.Manuscript.sourceGlue_on_branch
#check PaperFormalization.Manuscript.sourceGlue_at_jump
#print axioms PaperFormalization.Manuscript.sourceGlue_at_jump
#check PaperFormalization.Manuscript.sourceGlue_eventuallyEq
#print axioms PaperFormalization.Manuscript.sourceGlue_eventuallyEq
#check PaperFormalization.Manuscript.sourceGlue_hasDerivAt
#print axioms PaperFormalization.Manuscript.sourceGlue_hasDerivAt
#check PaperFormalization.Manuscript.sourceGlue_lipschitzOn
#print axioms PaperFormalization.Manuscript.sourceGlue_lipschitzOn
#check PaperFormalization.Manuscript.sourceGlue_traces
#print axioms PaperFormalization.Manuscript.sourceGlue_traces
#check PaperFormalization.Manuscript.sourceOriginalCovarianceView
#print axioms PaperFormalization.Manuscript.sourceOriginalCovarianceView
#check PaperFormalization.Manuscript.sourceOriginalCovarianceView_sample
#print axioms PaperFormalization.Manuscript.sourceOriginalCovarianceView_sample
#check PaperFormalization.Manuscript.sourceOriginalCovarianceView_preLaw
#print axioms PaperFormalization.Manuscript.sourceOriginalCovarianceView_preLaw
#check PaperFormalization.Manuscript.sourceHistoryInit
#print axioms PaperFormalization.Manuscript.sourceHistoryInit
#check PaperFormalization.Manuscript.sourceReferencePost
#print axioms PaperFormalization.Manuscript.sourceReferencePost
#check PaperFormalization.Manuscript.sourceReferenceBranch
#print axioms PaperFormalization.Manuscript.sourceReferenceBranch
#check PaperFormalization.Manuscript.sourceReferencePre
#print axioms PaperFormalization.Manuscript.sourceReferencePre
#check PaperFormalization.Manuscript.sourceReferencePost_succ
#print axioms PaperFormalization.Manuscript.sourceReferencePost_succ
#check PaperFormalization.Manuscript.sourceReferenceBranch_start
#print axioms PaperFormalization.Manuscript.sourceReferenceBranch_start
#check PaperFormalization.Manuscript.sourceHistoryInit_measurable
#print axioms PaperFormalization.Manuscript.sourceHistoryInit_measurable
#check PaperFormalization.Manuscript.sourceReferencePost_measurable
#print axioms PaperFormalization.Manuscript.sourceReferencePost_measurable
#check PaperFormalization.Manuscript.sourceReferenceBranch_measurable
#print axioms PaperFormalization.Manuscript.sourceReferenceBranch_measurable
#check PaperFormalization.Manuscript.sourceFullHistoryPreLaw
#print axioms PaperFormalization.Manuscript.sourceFullHistoryPreLaw
#check PaperFormalization.Manuscript.sourceCausalPreLaw_identity
#print axioms PaperFormalization.Manuscript.sourceCausalPreLaw_identity
#check PaperFormalization.Manuscript.single_characteristic_product_joint_law
#print axioms PaperFormalization.Manuscript.single_characteristic_product_joint_law
#check PaperFormalization.Manuscript.independent_single_characteristic_joint_law
#print axioms PaperFormalization.Manuscript.independent_single_characteristic_joint_law
#check PaperFormalization.Manuscript.original_environment_independent_initial_coordinate
#print axioms PaperFormalization.Manuscript.original_environment_independent_initial_coordinate
#check PaperFormalization.Manuscript.original_reference_path_law_identified
#print axioms PaperFormalization.Manuscript.original_reference_path_law_identified
#check PaperFormalization.Manuscript.original_reference_all_evaluation_laws
#print axioms PaperFormalization.Manuscript.original_reference_all_evaluation_laws
#check PaperFormalization.Manuscript.SourceReferencePathSpace
#print axioms PaperFormalization.Manuscript.SourceReferencePathSpace
#check PaperFormalization.Manuscript.sourceReferencePathEval
#print axioms PaperFormalization.Manuscript.sourceReferencePathEval
#check PaperFormalization.Manuscript.sourceReferencePathEval_measurable
#print axioms PaperFormalization.Manuscript.sourceReferencePathEval_measurable
#check PaperFormalization.Manuscript.sourceReferencePathLipschitz
#print axioms PaperFormalization.Manuscript.sourceReferencePathLipschitz
#check PaperFormalization.Manuscript.sourceReferencePathLipschitz_isClosed
#print axioms PaperFormalization.Manuscript.sourceReferencePathLipschitz_isClosed
#check PaperFormalization.Manuscript.sourceReferencePathLipschitz_iff
#print axioms PaperFormalization.Manuscript.sourceReferencePathLipschitz_iff
#check PaperFormalization.Manuscript.source_reference_randomPath_eq_of_label_agreement
#print axioms PaperFormalization.Manuscript.source_reference_randomPath_eq_of_label_agreement
#check PaperFormalization.Manuscript.sourceCausalReferencePath
#print axioms PaperFormalization.Manuscript.sourceCausalReferencePath
#check PaperFormalization.Manuscript.sourceCausalReferencePath_measurable
#print axioms PaperFormalization.Manuscript.sourceCausalReferencePath_measurable
#check PaperFormalization.Manuscript.sourceCausalReferencePath_eval
#print axioms PaperFormalization.Manuscript.sourceCausalReferencePath_eval
#check PaperFormalization.Manuscript.exists_source_causal_reference_path_version
#print axioms PaperFormalization.Manuscript.exists_source_causal_reference_path_version
#check PaperFormalization.Manuscript.source_independent_seed_path_agreement
#print axioms PaperFormalization.Manuscript.source_independent_seed_path_agreement
#check PaperFormalization.Manuscript.source_reference_version_all_marginal_laws
#print axioms PaperFormalization.Manuscript.source_reference_version_all_marginal_laws
#check PaperFormalization.Manuscript.sourceTrackingPathsOfClosedBranches
#print axioms PaperFormalization.Manuscript.sourceTrackingPathsOfClosedBranches
#check PaperFormalization.Manuscript.sourceParticleUnflatten
#print axioms PaperFormalization.Manuscript.sourceParticleUnflatten
#check PaperFormalization.Manuscript.particleFlatten_sourceParticleUnflatten
#print axioms PaperFormalization.Manuscript.particleFlatten_sourceParticleUnflatten
#check PaperFormalization.Manuscript.sourceParticleUnflatten_particleFlatten
#print axioms PaperFormalization.Manuscript.sourceParticleUnflatten_particleFlatten
#check PaperFormalization.Manuscript.sourceParticleFlattenIsometry
#print axioms PaperFormalization.Manuscript.sourceParticleFlattenIsometry
#check PaperFormalization.Manuscript.sourceParticleFlatten_measurable
#print axioms PaperFormalization.Manuscript.sourceParticleFlatten_measurable
#check PaperFormalization.Manuscript.sourceParticleUnflatten_measurable
#print axioms PaperFormalization.Manuscript.sourceParticleUnflatten_measurable
#check PaperFormalization.Manuscript.source_matrixEuclideanOperator_eq_toEuclideanCLM
#print axioms PaperFormalization.Manuscript.source_matrixEuclideanOperator_eq_toEuclideanCLM
#check PaperFormalization.Manuscript.source_alignedCovarianceFactor_congr
#print axioms PaperFormalization.Manuscript.source_alignedCovarianceFactor_congr
#check PaperFormalization.Manuscript.sourceJumpViewMatrixMeasurable
#print axioms PaperFormalization.Manuscript.sourceJumpViewMatrixMeasurable
#check PaperFormalization.Manuscript.sourceJumpViewMatrixBorel
#print axioms PaperFormalization.Manuscript.sourceJumpViewMatrixBorel
#check PaperFormalization.Manuscript.exists_source_original_jump_view
#print axioms PaperFormalization.Manuscript.exists_source_original_jump_view
#check PaperFormalization.Manuscript.exists_source_original_reference_gamma_event
#print axioms PaperFormalization.Manuscript.exists_source_original_reference_gamma_event
#check PaperFormalization.Manuscript.source_scheduled_covariance_identifications
#print axioms PaperFormalization.Manuscript.source_scheduled_covariance_identifications
#check PaperFormalization.Manuscript.sourceFullHistoryPreLaw_properties
#print axioms PaperFormalization.Manuscript.sourceFullHistoryPreLaw_properties
#check PaperFormalization.Manuscript.source_causal_population_event_implies_eligibility
#print axioms PaperFormalization.Manuscript.source_causal_population_event_implies_eligibility

-- Regrouping inverse, including empty indices.
example {N d : ℕ} (v : EuclideanSpace ℝ (Fin N × Fin d)) :
    particleFlatten (sourceParticleUnflatten v) = v := particleFlatten_sourceParticleUnflatten v

example {N d : ℕ} (x : PiLp 2 (fun _ : Fin N => EuclideanSpace ℝ (Fin d))) :
    sourceParticleUnflatten (particleFlatten x) = x := sourceParticleUnflatten_particleFlatten x

example (N d : ℕ) : sourceParticleUnflatten (0 : EuclideanSpace ℝ (Fin N × Fin d)) = 0 := by
  ext i j
  rfl

-- No jumps: the actual path is the zeroth branch at every time.
example (tau : ℕ -> ℝ) (branch : ℕ -> ℝ -> ℝ) (t : ℝ) :
    sourceGlue tau 0 branch t = branch 0 t := by
  simp [sourceGlue, PaperFormalization.Piecewise.jumpCount]

-- A genuine discontinuity: the value at the jump is the RIGHT value 1.
example : sourceGlue (fun n => (n : ℝ)) 1 (fun k _ => (k : ℝ)) 1 = 1 := by
  have ht : ∀ (k : ℕ), k < 1 -> (k : ℝ) < ((k+1 : ℕ) : ℝ) := by
    intro k _
    exact_mod_cast Nat.lt_succ_self k
  simpa using sourceGlue_at_jump (fun n => (n : ℝ)) 1 (fun k _ => (k : ℝ)) ht 1 le_rfl

-- The LEFT trace at that same jump is 0, not 1.
example : Tendsto (sourceGlue (fun n => (n : ℝ)) 1 (fun k _ => (k : ℝ)))
    (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have ht : ∀ (k : ℕ), k < 1 -> (k : ℝ) < ((k+1 : ℕ) : ℝ) := by
    intro k _
    exact_mod_cast Nat.lt_succ_self k
  simpa using (sourceGlue_traces (fun n => (n : ℝ)) 1 (fun k _ => (k : ℝ)) ht 0
    (by norm_num) continuousOn_const).2

-- Zero horizon and zero-dimensional reference path space.
example : StandardBorelSpace (SourceReferencePathSpace 0 0 (fun _ => 0) (fun _ => 0)) := by
  infer_instance

example (path : SourceReferencePathSpace 0 0 (fun _ => 0) (fun _ => 0)) :
    sourceReferencePathEval path 0 0 = 0 := Subsingleton.elim _ _

-- The zero-step reference is literally its initial seed.
example (tau : ℕ -> ℝ)
    (flow : (n : ℕ) -> (Fin n -> ℝ) -> ℝ -> ℝ -> ℝ)
    (jump : (n : ℕ) -> (Fin n -> ℝ) -> ℝ -> ℝ -> ℝ)
    (h : Fin 0 -> ℝ) (u : ℝ) : sourceReferencePost tau flow jump 0 h u = u := rfl

-- One prescribed population jump, with identity continuous flow.
example (h : Fin 1 -> ℝ) (u : ℝ) :
    sourceReferencePost (fun n => (n : ℝ)) (fun _ _ _ x => x)
      (fun _ _ w x => x+w) 1 h u = u+h 0 := rfl

-- The independent auxiliary leaves the original law unchanged.
example {O A : Type*} [MeasurableSpace O] [MeasurableSpace A]
    (nu : Measure O) [IsProbabilityMeasure nu] (lambda : Measure A) [IsProbabilityMeasure lambda] :
    (nu.prod lambda).map (Prod.fst : O × A -> O) = nu :=
  source_original_auxiliary_preserves nu lambda

-- Dropping any number of FUTURE auxiliaries preserves the earlier law.
example {O A : Type*} [MeasurableSpace O] [MeasurableSpace A]
    (nu : Measure O) [IsProbabilityMeasure nu] (lambda : Measure A) [IsProbabilityMeasure lambda]
    (n m : ℕ) : MeasurePreserving (sourceAuxiliaryProjection (O := O) (A := A) n m)
      (sourceAuxiliaryMeasure nu lambda (n+m)) (sourceAuxiliaryMeasure nu lambda n) :=
  sourceAuxiliaryProjection_preserving nu lambda n m

-- The original outcome is retained POINTWISE, not only in distribution.
example (z : SourceAuxiliarySpace ℝ ℝ (1+2)) :
    sourceAuxiliaryOriginal 3 z = sourceAuxiliaryOriginal 1 (sourceAuxiliaryProjection 1 2 z) :=
  sourceAuxiliaryProjection_original 1 2 z

-- A deterministic all-index identity is transferred on one AE environment set.
example {Env Seed E I : Type*} [MeasurableSpace Env] [MeasurableSpace Seed] [MeasurableSpace E]
    (ρ : Measure Env) [IsProbabilityMeasure ρ] (mu0 : Measure Seed) [IsProbabilityMeasure mu0]
    (f : Env -> Seed -> I -> E) :
    ∀ᵐ e ∂ρ, ∀ i, mu0.map (fun u => f e u i) = mu0.map (fun u => f e u i) :=
  source_reference_version_all_marginal_laws ρ mu0 f f (Filter.Eventually.of_forall (fun _ _ => rfl))

-- The lifted representation still has exactly the unlifted ORIGINAL marginal.
example {O A : Type*} [MeasurableSpace O] [MeasurableSpace A]
    (nu : Measure O) [IsProbabilityMeasure nu] (lambda : Measure A) [IsProbabilityMeasure lambda]
    (n : ℕ) : (sourceAuxiliaryMeasure nu lambda n).map
      (sourceAuxiliaryOriginal (O := O) (A := A) n) = nu :=
  (sourceAuxiliaryOriginal_preserving nu lambda n).map_eq
