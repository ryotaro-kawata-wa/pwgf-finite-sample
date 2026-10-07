import PaperFormalization.Manuscript.SourceObservedActualTracking
import PaperFormalization.Manuscript.SourceConstructedPopulationEvent

/-! Boundary diagnostics for M13o; this file is not a verification receipt.
The anonymous examples check algebra and boundary definitions only. They do
not instantiate the original stochastic model or constitute an end-to-end
test of its high-probability theorem. Run the project verifier afterwards.
-/
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
open PaperFormalization.Manuscript PaperFormalization.Continuous PaperFormalization.Piecewise

#check PaperFormalization.Manuscript.source_tracking_all_cases_with_pre
#print axioms PaperFormalization.Manuscript.source_tracking_all_cases_with_pre
#check PaperFormalization.Manuscript.actual_source_tracking_bound
#print axioms PaperFormalization.Manuscript.actual_source_tracking_bound
#check PaperFormalization.Manuscript.exists_source_observed_tracking_schedule_event
#print axioms PaperFormalization.Manuscript.exists_source_observed_tracking_schedule_event
#check PaperFormalization.Manuscript.SourcePopulationBranchPath
#print axioms PaperFormalization.Manuscript.SourcePopulationBranchPath
#check PaperFormalization.Manuscript.sourcePopulationBranchPathMeasurableSpace
#print axioms PaperFormalization.Manuscript.sourcePopulationBranchPathMeasurableSpace
#check PaperFormalization.Manuscript.sourcePopulationBranchPathBorelSpace
#print axioms PaperFormalization.Manuscript.sourcePopulationBranchPathBorelSpace
#check PaperFormalization.Manuscript.sourcePopulationBranchPath_standardBorel
#print axioms PaperFormalization.Manuscript.sourcePopulationBranchPath_standardBorel
#check PaperFormalization.Manuscript.sourcePopulationBranchPathStandardBorel
#print axioms PaperFormalization.Manuscript.sourcePopulationBranchPathStandardBorel
#check PaperFormalization.Manuscript.SourcePopulationPathSpace
#print axioms PaperFormalization.Manuscript.SourcePopulationPathSpace
#check PaperFormalization.Manuscript.sourcePopulationPathSpace_standardBorel
#print axioms PaperFormalization.Manuscript.sourcePopulationPathSpace_standardBorel
#check PaperFormalization.Manuscript.sourcePopulationPathEval
#print axioms PaperFormalization.Manuscript.sourcePopulationPathEval
#check PaperFormalization.Manuscript.sourcePopulationPathEval_measurable
#print axioms PaperFormalization.Manuscript.sourcePopulationPathEval_measurable
#check PaperFormalization.Manuscript.sourcePopulationPathEval_endpoints
#print axioms PaperFormalization.Manuscript.sourcePopulationPathEval_endpoints
#check PaperFormalization.Manuscript.sourcePopulationBranchPath_measurable_of_dense_evaluations
#print axioms PaperFormalization.Manuscript.sourcePopulationBranchPath_measurable_of_dense_evaluations
#check PaperFormalization.Manuscript.sourcePopulationPathEncode
#print axioms PaperFormalization.Manuscript.sourcePopulationPathEncode
#check PaperFormalization.Manuscript.sourcePopulationPathEncode_eval
#print axioms PaperFormalization.Manuscript.sourcePopulationPathEncode_eval
#check PaperFormalization.Manuscript.sourcePopulationPathEncode_measurable
#print axioms PaperFormalization.Manuscript.sourcePopulationPathEncode_measurable
#check PaperFormalization.Manuscript.exists_source_population_path_version_of_dense_grids
#print axioms PaperFormalization.Manuscript.exists_source_population_path_version_of_dense_grids
#check PaperFormalization.Manuscript.sourcePopulationPathLipschitz
#print axioms PaperFormalization.Manuscript.sourcePopulationPathLipschitz
#check PaperFormalization.Manuscript.sourcePopulationPathLipschitz_isClosed
#print axioms PaperFormalization.Manuscript.sourcePopulationPathLipschitz_isClosed
#check PaperFormalization.Manuscript.sourcePopulationPathLipschitz_iff
#print axioms PaperFormalization.Manuscript.sourcePopulationPathLipschitz_iff
#check PaperFormalization.Manuscript.exists_source_population_path_version
#print axioms PaperFormalization.Manuscript.exists_source_population_path_version
#check PaperFormalization.Manuscript.originalConditionalPathLaw
#print axioms PaperFormalization.Manuscript.originalConditionalPathLaw
#check PaperFormalization.Manuscript.originalConditionalPathLaw_markov
#print axioms PaperFormalization.Manuscript.originalConditionalPathLaw_markov
#check PaperFormalization.Manuscript.originalConditionalPathLaw_joint
#print axioms PaperFormalization.Manuscript.originalConditionalPathLaw_joint
#check PaperFormalization.Manuscript.originalConditionalPathLaw_marginal
#print axioms PaperFormalization.Manuscript.originalConditionalPathLaw_marginal
#check PaperFormalization.Manuscript.originalConditionalPathLaw_unique
#print axioms PaperFormalization.Manuscript.originalConditionalPathLaw_unique
#check PaperFormalization.Manuscript.originalConditionalPathLaw_all_marginals_unique
#print axioms PaperFormalization.Manuscript.originalConditionalPathLaw_all_marginals_unique
#check PaperFormalization.Manuscript.originalConditionalPathLaw_eval_condDistrib
#print axioms PaperFormalization.Manuscript.originalConditionalPathLaw_eval_condDistrib
#check PaperFormalization.Manuscript.exists_source_constructed_population_event
#print axioms PaperFormalization.Manuscript.exists_source_constructed_population_event
#check PaperFormalization.Manuscript.actual_source_tracking_of_observed_events
#print axioms PaperFormalization.Manuscript.actual_source_tracking_of_observed_events
#check PaperFormalization.Manuscript.exists_source_actual_tracking_on_observed_event
#print axioms PaperFormalization.Manuscript.exists_source_actual_tracking_on_observed_event

-- Algebra used in the zero-envelope configuration-equality conclusion.
example {E : Type*} [NormedAddCommGroup E] {N : Nat}
    (hN : 0 < N) (X Y : E)
    (h : norm (X - Y) / Real.sqrt (N : Real) = 0) : X = Y := by
  have hsqrtN : Real.sqrt (N : Real) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (Nat.cast_pos.2 hN))
  have hnorm : norm (X - Y) = 0 := by
    field_simp [hsqrtN] at h
    simpa using h
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

-- The empty jump product remains one.
example (eta : Nat -> Real) (A : Real) :
    jumpAmplification (sourceJumpError A eta) 0 = 1 := by
  simp [jumpAmplification]

-- At J = 0 and T = 0, the literal envelope and its real supremum are zero.
example (kappa : Real -> Real) (tau eta : Nat -> Real)
    (delta deltaTilde A : Real) :
    sourceCurvatureEnvelope kappa tau eta delta deltaTilde A 0 0 = 0 := by
  simp [sourceCurvatureEnvelope]

example (kappa : Real -> Real) (tau eta : Nat -> Real)
    (delta deltaTilde A : Real) :
    sourceCurvatureEnvelopeSup kappa tau eta delta deltaTilde A 0 0 = 0 := by
  rw [sourceCurvatureEnvelopeSup_eq_sSup]
  simp [sourceCurvatureEnvelope]

-- A terminal jump is allowed: its following open branch has zero measure.
example (tau : Nat -> Real) (J : Nat) (T : Real) (h : tau J = T) :
    volume.restrict (Ioo (tau J) T) = 0 := by
  simp [h]

-- Concrete empty-dimension and singleton-branch path spaces remain standard Borel.
example : StandardBorelSpace (SourcePopulationPathSpace 0 0 (fun _ => 0) (fun _ => 0)) := by
  infer_instance

example : Nonempty (SourcePopulationPathSpace 0 0 (fun _ => 0) (fun _ => 0)) := by
  infer_instance

-- A singleton branch keeps its endpoint evaluation, even for a nonzero vector.
example (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    sourcePopulationPathEval
      (sourcePopulationPathEncode (J := 0) (a := fun _ => 0) (b := fun _ => 0)
        (fun _ _ _ => x) (fun _ _ => continuousOn_const)) 0 0 0 = x := by
  exact sourcePopulationPathEncode_eval _ _ 0 0 0 ⟨le_rfl, le_rfl⟩

-- Original-law disintegration is exact; no Gaussian or iid premise is required.
example {O S : Type*} [MeasurableSpace O] [MeasurableSpace S]
    (nu : Measure O) [IsProbabilityMeasure nu] (environment : O → S)
    (paths : O → SourcePopulationPathSpace 0 0 (fun _ => 0) (fun _ => 0))
    (hpaths : Measurable paths) :
    nu.map (fun x => (environment x, paths x)) =
      (nu.map environment) ⊗ₘ originalConditionalPathLaw nu environment paths :=
  originalConditionalPathLaw_joint nu environment paths hpaths

-- The exact combined schedule budget is zero when there are no jumps.
example (pTotal : ℝ) : ((0 : ℝ) / (0+1)) * (5*pTotal/32) = 0 := by ring
