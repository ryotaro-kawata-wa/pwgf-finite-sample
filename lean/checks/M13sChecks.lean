import PaperFormalization.Manuscript.SourceRawCharacteristicVersion

/-! M13s UNEXECUTED diagnostics. These are not a verification receipt.
The full source theorem types and axioms are inspected as well as small boundary
examples. The examples do not replace source-interface review of the top theorem.
-/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal Topology ProbabilityTheory
open PaperFormalization.Manuscript

#check PaperFormalization.Manuscript.sourceODEClamp
#print axioms PaperFormalization.Manuscript.sourceODEClamp
#check PaperFormalization.Manuscript.sourceODEClamp_coe
#print axioms PaperFormalization.Manuscript.sourceODEClamp_coe
#check PaperFormalization.Manuscript.sourceODEClamp_continuous
#print axioms PaperFormalization.Manuscript.sourceODEClamp_continuous
#check PaperFormalization.Manuscript.sourceODEPathExtend
#print axioms PaperFormalization.Manuscript.sourceODEPathExtend
#check PaperFormalization.Manuscript.sourceODEPathExtend_continuous
#print axioms PaperFormalization.Manuscript.sourceODEPathExtend_continuous
#check PaperFormalization.Manuscript.sourceODEIntegralCLM
#print axioms PaperFormalization.Manuscript.sourceODEIntegralCLM
#check PaperFormalization.Manuscript.sourceODESolutionSet
#print axioms PaperFormalization.Manuscript.sourceODESolutionSet
#check PaperFormalization.Manuscript.sourceODESolutionSet_isClosed
#print axioms PaperFormalization.Manuscript.sourceODESolutionSet_isClosed
#check PaperFormalization.Manuscript.sourceODESolutionSet_hasDerivWithinAt
#print axioms PaperFormalization.Manuscript.sourceODESolutionSet_hasDerivWithinAt
#check PaperFormalization.Manuscript.source_c1_lipschitz_on_closedBall
#print axioms PaperFormalization.Manuscript.source_c1_lipschitz_on_closedBall
#check PaperFormalization.Manuscript.sourceODESolutionSet_initial_injective
#print axioms PaperFormalization.Manuscript.sourceODESolutionSet_initial_injective
#check PaperFormalization.Manuscript.sourceODESolutionSet_of_hasDerivAt
#print axioms PaperFormalization.Manuscript.sourceODESolutionSet_of_hasDerivAt
#check PaperFormalization.Manuscript.sourceODEPathMeasurable
#print axioms PaperFormalization.Manuscript.sourceODEPathMeasurable
#check PaperFormalization.Manuscript.sourceODEPathBorel
#print axioms PaperFormalization.Manuscript.sourceODEPathBorel
#check PaperFormalization.Manuscript.sourceODEExistenceDomain
#print axioms PaperFormalization.Manuscript.sourceODEExistenceDomain
#check PaperFormalization.Manuscript.sourceODEInitial_measurableEmbedding
#print axioms PaperFormalization.Manuscript.sourceODEInitial_measurableEmbedding
#check PaperFormalization.Manuscript.sourceODEExistenceDomain_measurable
#print axioms PaperFormalization.Manuscript.sourceODEExistenceDomain_measurable
#check PaperFormalization.Manuscript.sourceCanonicalODEPath
#print axioms PaperFormalization.Manuscript.sourceCanonicalODEPath
#check PaperFormalization.Manuscript.sourceCanonicalODEPath_measurable
#print axioms PaperFormalization.Manuscript.sourceCanonicalODEPath_measurable
#check PaperFormalization.Manuscript.sourceCanonicalODEPath_of_solution
#print axioms PaperFormalization.Manuscript.sourceCanonicalODEPath_of_solution
#check PaperFormalization.Manuscript.sourceCanonicalODEPath_of_not_mem
#print axioms PaperFormalization.Manuscript.sourceCanonicalODEPath_of_not_mem
#check PaperFormalization.Manuscript.sourceCanonicalODEPath_initial
#print axioms PaperFormalization.Manuscript.sourceCanonicalODEPath_initial
#check PaperFormalization.Manuscript.sourceCanonicalODEPath_mem
#print axioms PaperFormalization.Manuscript.sourceCanonicalODEPath_mem
#check PaperFormalization.Manuscript.sourceCanonicalODEFlow
#print axioms PaperFormalization.Manuscript.sourceCanonicalODEFlow
#check PaperFormalization.Manuscript.sourceCanonicalODEFlow_measurable
#print axioms PaperFormalization.Manuscript.sourceCanonicalODEFlow_measurable
#check PaperFormalization.Manuscript.sourceCanonicalODEFlow_initial
#print axioms PaperFormalization.Manuscript.sourceCanonicalODEFlow_initial
#check PaperFormalization.Manuscript.sourceCanonicalODEFlow_eq_actual
#print axioms PaperFormalization.Manuscript.sourceCanonicalODEFlow_eq_actual
#check PaperFormalization.Manuscript.sourceODESolutionSet_symmetry
#print axioms PaperFormalization.Manuscript.sourceODESolutionSet_symmetry
#check PaperFormalization.Manuscript.sourceODEExistenceDomain_symmetry
#print axioms PaperFormalization.Manuscript.sourceODEExistenceDomain_symmetry
#check PaperFormalization.Manuscript.sourceCanonicalODEFlow_symmetry
#print axioms PaperFormalization.Manuscript.sourceCanonicalODEFlow_symmetry
#check PaperFormalization.Manuscript.sourceParticlePermuteIsometry
#print axioms PaperFormalization.Manuscript.sourceParticlePermuteIsometry
#check PaperFormalization.Manuscript.sourceParticlePermuteIsometry_apply
#print axioms PaperFormalization.Manuscript.sourceParticlePermuteIsometry_apply
#check PaperFormalization.Manuscript.sourceHorizonEndpoint
#print axioms PaperFormalization.Manuscript.sourceHorizonEndpoint
#check PaperFormalization.Manuscript.sourceHorizonEndpoint_ordered
#print axioms PaperFormalization.Manuscript.sourceHorizonEndpoint_ordered
#check PaperFormalization.Manuscript.sourceHorizonEndpoint_used
#print axioms PaperFormalization.Manuscript.sourceHorizonEndpoint_used
#check PaperFormalization.Manuscript.sourceExactEmpiricalDrift
#print axioms PaperFormalization.Manuscript.sourceExactEmpiricalDrift
#check PaperFormalization.Manuscript.sourceCanonicalEmpiricalFlow
#print axioms PaperFormalization.Manuscript.sourceCanonicalEmpiricalFlow
#check PaperFormalization.Manuscript.sourceCanonicalEmpiricalFlow_properties
#print axioms PaperFormalization.Manuscript.sourceCanonicalEmpiricalFlow_properties
#check PaperFormalization.Manuscript.sourceCanonicalEmpiricalFlow_ode
#print axioms PaperFormalization.Manuscript.sourceCanonicalEmpiricalFlow_ode
#check PaperFormalization.Manuscript.sourceCanonicalEmpiricalFlow_eq_source
#print axioms PaperFormalization.Manuscript.sourceCanonicalEmpiricalFlow_eq_source
#check PaperFormalization.Manuscript.source_stdGaussian_isometry_invariant
#print axioms PaperFormalization.Manuscript.source_stdGaussian_isometry_invariant
#check PaperFormalization.Manuscript.source_step_normal_permutation
#print axioms PaperFormalization.Manuscript.source_step_normal_permutation
#check PaperFormalization.Manuscript.sourceInitialConfigurationLaw
#print axioms PaperFormalization.Manuscript.sourceInitialConfigurationLaw
#check PaperFormalization.Manuscript.sourceInitialConfigurationLaw_probability
#print axioms PaperFormalization.Manuscript.sourceInitialConfigurationLaw_probability
#check PaperFormalization.Manuscript.source_initial_configuration_permutation
#print axioms PaperFormalization.Manuscript.source_initial_configuration_permutation
#check PaperFormalization.Manuscript.source_original_input_product_law
#print axioms PaperFormalization.Manuscript.source_original_input_product_law
#check PaperFormalization.Manuscript.sourceAuxiliaryTransform
#print axioms PaperFormalization.Manuscript.sourceAuxiliaryTransform
#check PaperFormalization.Manuscript.sourceAuxiliaryTransform_measurable
#print axioms PaperFormalization.Manuscript.sourceAuxiliaryTransform_measurable
#check PaperFormalization.Manuscript.sourceAuxiliaryTransform_original
#print axioms PaperFormalization.Manuscript.sourceAuxiliaryTransform_original
#check PaperFormalization.Manuscript.sourceAuxiliaryTransform_array
#print axioms PaperFormalization.Manuscript.sourceAuxiliaryTransform_array
#check PaperFormalization.Manuscript.sourceAuxiliaryTransform_preserving
#print axioms PaperFormalization.Manuscript.sourceAuxiliaryTransform_preserving
#check PaperFormalization.Manuscript.sourceAuxiliaryHistory_preserving
#print axioms PaperFormalization.Manuscript.sourceAuxiliaryHistory_preserving
#check PaperFormalization.Manuscript.sourceInputPermute
#print axioms PaperFormalization.Manuscript.sourceInputPermute
#check PaperFormalization.Manuscript.sourceInputPermute_preserving
#print axioms PaperFormalization.Manuscript.sourceInputPermute_preserving
#check PaperFormalization.Manuscript.sourcePairPermute
#print axioms PaperFormalization.Manuscript.sourcePairPermute
#check PaperFormalization.Manuscript.sourcePackedPermute
#print axioms PaperFormalization.Manuscript.sourcePackedPermute
#check PaperFormalization.Manuscript.sourcePackedPermute_population
#print axioms PaperFormalization.Manuscript.sourcePackedPermute_population
#check PaperFormalization.Manuscript.sourcePackedPermute_init
#print axioms PaperFormalization.Manuscript.sourcePackedPermute_init
#check PaperFormalization.Manuscript.sourceCanonicalCoupledStep_permute
#print axioms PaperFormalization.Manuscript.sourceCanonicalCoupledStep_permute
#check PaperFormalization.Manuscript.sourceCanonicalCoupledPost_permute
#print axioms PaperFormalization.Manuscript.sourceCanonicalCoupledPost_permute
#check PaperFormalization.Manuscript.sourceActualCovarianceVersion_permute
#print axioms PaperFormalization.Manuscript.sourceActualCovarianceVersion_permute
#check PaperFormalization.Manuscript.sourceActualFinitePost_permute
#print axioms PaperFormalization.Manuscript.sourceActualFinitePost_permute
#check PaperFormalization.Manuscript.sourceFiniteHorizonBranch_permute
#print axioms PaperFormalization.Manuscript.sourceFiniteHorizonBranch_permute
#check PaperFormalization.Manuscript.sourceFinalBranch
#print axioms PaperFormalization.Manuscript.sourceFinalBranch
#check PaperFormalization.Manuscript.sourceFinalRight
#print axioms PaperFormalization.Manuscript.sourceFinalRight
#check PaperFormalization.Manuscript.sourcePairCloud
#print axioms PaperFormalization.Manuscript.sourcePairCloud
#check PaperFormalization.Manuscript.sourcePairCloud_measurable
#print axioms PaperFormalization.Manuscript.sourcePairCloud_measurable
#check PaperFormalization.Manuscript.sourceFiniteHorizonBranch_measurable
#print axioms PaperFormalization.Manuscript.sourceFiniteHorizonBranch_measurable
#check PaperFormalization.Manuscript.sourceFinalBranch_measurable
#print axioms PaperFormalization.Manuscript.sourceFinalBranch_measurable
#check PaperFormalization.Manuscript.sourceInputFinalBranch
#print axioms PaperFormalization.Manuscript.sourceInputFinalBranch
#check PaperFormalization.Manuscript.sourceInputFinalBranch_observation
#print axioms PaperFormalization.Manuscript.sourceInputFinalBranch_observation
#check PaperFormalization.Manuscript.sourceInputFinalBranch_transform
#print axioms PaperFormalization.Manuscript.sourceInputFinalBranch_transform
#check PaperFormalization.Manuscript.sourceFinalBranch_exchangeable
#print axioms PaperFormalization.Manuscript.sourceFinalBranch_exchangeable
#check PaperFormalization.Manuscript.source_pair_marginals_of_permutation
#print axioms PaperFormalization.Manuscript.source_pair_marginals_of_permutation
#check PaperFormalization.Manuscript.source_closed_time_in_horizon
#print axioms PaperFormalization.Manuscript.source_closed_time_in_horizon
#check PaperFormalization.Manuscript.source_closed_branch_moment_from_right
#print axioms PaperFormalization.Manuscript.source_closed_branch_moment_from_right
#check PaperFormalization.Manuscript.sourceFinalBranch_all_closed_moments
#print axioms PaperFormalization.Manuscript.sourceFinalBranch_all_closed_moments
#check PaperFormalization.Manuscript.SourceReferenceControl
#print axioms PaperFormalization.Manuscript.SourceReferenceControl
#check PaperFormalization.Manuscript.sourceReferenceControl_congr
#print axioms PaperFormalization.Manuscript.sourceReferenceControl_congr
#check PaperFormalization.Manuscript.sourceReferenceControl_exponential_eligibility
#print axioms PaperFormalization.Manuscript.sourceReferenceControl_exponential_eligibility
#check PaperFormalization.Manuscript.exists_source_retained_population_gamma_radius_event
#print axioms PaperFormalization.Manuscript.exists_source_retained_population_gamma_radius_event
#check PaperFormalization.Manuscript.sourceOriginalCharacteristic
#print axioms PaperFormalization.Manuscript.sourceOriginalCharacteristic
#check PaperFormalization.Manuscript.sourceOriginalCharacteristic_measurable
#print axioms PaperFormalization.Manuscript.sourceOriginalCharacteristic_measurable
#check PaperFormalization.Manuscript.sourceFiniteReferenceBranch_original
#print axioms PaperFormalization.Manuscript.sourceFiniteReferenceBranch_original
#check PaperFormalization.Manuscript.sourceFinalBranch_reference_original
#print axioms PaperFormalization.Manuscript.sourceFinalBranch_reference_original
#check PaperFormalization.Manuscript.sourceFinalBranch_reference_map
#print axioms PaperFormalization.Manuscript.sourceFinalBranch_reference_map
#check PaperFormalization.Manuscript.sourceScheduleLeft
#print axioms PaperFormalization.Manuscript.sourceScheduleLeft
#check PaperFormalization.Manuscript.sourceScheduleRight
#print axioms PaperFormalization.Manuscript.sourceScheduleRight
#check PaperFormalization.Manuscript.sourceSchedule_ordered
#print axioms PaperFormalization.Manuscript.sourceSchedule_ordered
#check PaperFormalization.Manuscript.sourceSchedule_total_length
#print axioms PaperFormalization.Manuscript.sourceSchedule_total_length
#check PaperFormalization.Manuscript.SourceRightAntiSpikiness
#print axioms PaperFormalization.Manuscript.SourceRightAntiSpikiness
#check PaperFormalization.Manuscript.sourceRightAntiSpikiness_of_positive
#print axioms PaperFormalization.Manuscript.sourceRightAntiSpikiness_of_positive
#check PaperFormalization.Manuscript.sourceRightAntiSpikiness_branches
#print axioms PaperFormalization.Manuscript.sourceRightAntiSpikiness_branches
#check PaperFormalization.Manuscript.SourceTrackingSmallness
#print axioms PaperFormalization.Manuscript.SourceTrackingSmallness
#check PaperFormalization.Manuscript.SourceTrackingConclusion
#print axioms PaperFormalization.Manuscript.SourceTrackingConclusion
#check PaperFormalization.Manuscript.source_finite_horizon_tracking
#print axioms PaperFormalization.Manuscript.source_finite_horizon_tracking
#check PaperFormalization.Manuscript.sourceFinalPopulationScale
#print axioms PaperFormalization.Manuscript.sourceFinalPopulationScale
#check PaperFormalization.Manuscript.sourceFinalMomentScale
#print axioms PaperFormalization.Manuscript.sourceFinalMomentScale
#check PaperFormalization.Manuscript.sourceFinalGammaThreshold
#print axioms PaperFormalization.Manuscript.sourceFinalGammaThreshold
#check PaperFormalization.Manuscript.sourceFinalJumpCoefficient
#print axioms PaperFormalization.Manuscript.sourceFinalJumpCoefficient
#check PaperFormalization.Manuscript.sourceFinalScales_positive
#print axioms PaperFormalization.Manuscript.sourceFinalScales_positive
#check PaperFormalization.Manuscript.source_iIndepFun_pullback
#print axioms PaperFormalization.Manuscript.source_iIndepFun_pullback
#check PaperFormalization.Manuscript.source_final_original_marginal
#print axioms PaperFormalization.Manuscript.source_final_original_marginal
#check PaperFormalization.Manuscript.SourceVisitedEmpiricalSolutions
#print axioms PaperFormalization.Manuscript.SourceVisitedEmpiricalSolutions
#check PaperFormalization.Manuscript.source_visited_empirical_coordinate_odes
#print axioms PaperFormalization.Manuscript.source_visited_empirical_coordinate_odes
#check PaperFormalization.Manuscript.source_final_reference_coordinate_odes
#print axioms PaperFormalization.Manuscript.source_final_reference_coordinate_odes
#check PaperFormalization.Manuscript.exists_source_scheduled_tracking_event
#print axioms PaperFormalization.Manuscript.exists_source_scheduled_tracking_event
#check PaperFormalization.Manuscript.sourceActualFinitePost_finite_step
#print axioms PaperFormalization.Manuscript.sourceActualFinitePost_finite_step
#check PaperFormalization.Manuscript.SourceRawEmpiricalSchedule
#print axioms PaperFormalization.Manuscript.SourceRawEmpiricalSchedule
#check PaperFormalization.Manuscript.source_canonical_schedule_agrees_with_source
#print axioms PaperFormalization.Manuscript.source_canonical_schedule_agrees_with_source
#check PaperFormalization.Manuscript.source_glued_paths_eq_of_closed_agreement
#print axioms PaperFormalization.Manuscript.source_glued_paths_eq_of_closed_agreement
#check PaperFormalization.Manuscript.exists_source_tracking_for_raw_solution_branches
#print axioms PaperFormalization.Manuscript.exists_source_tracking_for_raw_solution_branches
#check PaperFormalization.Manuscript.exists_source_final_characteristic_version
#print axioms PaperFormalization.Manuscript.exists_source_final_characteristic_version
#check PaperFormalization.Manuscript.source_final_restricted_tracking_failure
#print axioms PaperFormalization.Manuscript.source_final_restricted_tracking_failure

-- 1: clamping agrees at every point of the closed interval.
example (a b : Real) (hab : a ≤ b) (t : Icc a b) : sourceODEClamp a b hab t = t :=
  sourceODEClamp_coe a b hab t

-- 2-3: outside values are only harmless totalizations.
example (a b t : Real) (hab : a ≤ b) (ht : t ≤ a) :
    (sourceODEClamp a b hab t : Real) = a := by
  simp [sourceODEClamp,min_eq_left (ht.trans hab),max_eq_left ht]

example (a b t : Real) (hab : a ≤ b) (ht : b ≤ t) :
    (sourceODEClamp a b hab t : Real) = b := by
  simp [sourceODEClamp,min_eq_right ht,max_eq_right hab]

-- 4: the constant fallback keeps the original initial state.
example (a b t x : Real) (hab : a ≤ b) :
    sourceODEPathExtend hab (ContinuousMap.const (Icc a b) x) t = x := rfl

-- 5: zero-length integrals do not require a positive interval length.
example (a b : Real) (hab : a ≤ b) (u : C(Icc a b,Real)) :
    sourceODEIntegralCLM a b hab a u = 0 := by
  change (∫ s in a..a, sourceODEPathExtend hab u s) = 0
  simp

-- 6: an actual stationary source path belongs to the solution graph.
example (a b x : Real) (hab : a ≤ b) :
    ContinuousMap.const (Icc a b) x ∈ sourceODESolutionSet (fun _ : Real => 0) a b hab := by
  intro t
  simp [sourceODESolutionSet,sourceODEPathExtend]

-- 7: a nonstationary raw ODE solution is recognized via its actual derivative.
example (a b x : Real) (hab : a ≤ b) :
    (⟨fun t : Icc a b => x+(t:Real)-a, by fun_prop⟩ : C(Icc a b,Real)) ∈
      sourceODESolutionSet (fun _ : Real => 1) a b hab := by
  exact sourceODESolutionSet_of_hasDerivAt (fun _ : Real => 1) continuous_const a b hab
    (fun t => x+t-a) (by fun_prop) (by intro t ht; convert ((hasDerivAt_const t x).add (hasDerivAt_id t)).sub_const a using 1 <;> simp)

-- 8: canonical selection returns the true constant solution, not a new sample.
example (a b x t : Real) (hab : a ≤ b) (ht : t ∈ Icc a b) :
    sourceCanonicalODEFlow (fun _ : Real => 0) a b hab x t = x := by
  have hh := sourceCanonicalODEFlow_eq_actual (fun _ : Real => 0) contDiff_const a b hab
    (fun _ => x) continuousOn_const (by intro s hs; exact hasDerivAt_const s x)
  exact hh ht

-- 9: canonical selection agrees with the translating source solution.
example (a b x t : Real) (hab : a ≤ b) (ht : t ∈ Icc a b) :
    sourceCanonicalODEFlow (fun _ : Real => 1) a b hab x t = x+t-a := by
  have hh := sourceCanonicalODEFlow_eq_actual (fun _ : Real => 1) contDiff_const a b hab
    (fun s => x+s-a) (by fun_prop)
    (by intro s hs; convert ((hasDerivAt_const s x).add (hasDerivAt_id s)).sub_const a using 1 <;> simp)
  simpa using hh ht

-- 10: a source solution supplies the lifetime; it is not assumed globally.
example (a b x : Real) (hab : a ≤ b) :
    x ∈ sourceODEExistenceDomain (fun _ : Real => 0) a b hab := by
  refine ⟨⟨ContinuousMap.const (Icc a b) x, ?_⟩, rfl⟩
  intro t
  simp [sourceODEPathExtend]

-- 11: the undefined-lifetime case has an explicit non-ODE fallback.
example (f : Real -> Real) (a b x : Real) (hab : a ≤ b)
    (hx : x ∉ sourceODEExistenceDomain f a b hab) :
    sourceCanonicalODEPath f a b hab x = ContinuousMap.const (Icc a b) x :=
  sourceCanonicalODEPath_of_not_mem f a b hab x hx

-- 12: singleton intervals are valid for every C1 vector field.
example (f : Real -> Real) (hf : ContDiff Real 1 f) (a x : Real) :
    sourceCanonicalODEFlow f a a le_rfl x a = x :=
  sourceCanonicalODEFlow_initial f hf a a le_rfl x

-- 13: singular/zero spatial dimension is allowed in the Gaussian input law.
example : (stdGaussian (EuclideanSpace Real (Fin 0))).map
    (LinearIsometryEquiv.refl Real (EuclideanSpace Real (Fin 0))) =
      stdGaussian (EuclideanSpace Real (Fin 0)) := source_stdGaussian_isometry_invariant _

-- 14: the empty particle index is legal for the original input distribution.
example (mu0 : Measure (EuclideanSpace Real (Fin 0))) [IsProbabilityMeasure mu0] :
    IsProbabilityMeasure (sourceInitialConfigurationLaw (N := 0) mu0) := inferInstance

-- 15: a genuine two-particle swap has its invariant auxiliary marginal.
example : MeasurePreserving
    (sourceEuclideanPermute (sourceParticleIndexPermute (d := 1) (Equiv.swap (0 : Fin 2) 1)))
    (stdGaussian (SourceStepNormal 2 1)) (stdGaussian (SourceStepNormal 2 1)) :=
  source_step_normal_permutation _

-- 16: the original particle l2 norm is not changed by reindexing.
example {N d : Nat} (s : Equiv.Perm (Fin N)) (u : SourceFiniteConfiguration N d) :
    norm (sourceParticlePermute s u) = norm u :=
  (sourceParticlePermuteIsometry s).norm_map u

-- 17: no population innovation is changed by the auxiliary/particle symmetry.
example {W : Type*} {N d n : Nat} (s : Equiv.Perm (Fin N))
    (h : Fin n -> W × SourceStepNormal N d) :
    sourcePopulationPrefix (sourcePackedPermute s h) = sourcePopulationPrefix h := by
  rfl

-- 18: total branch length is exact, including no jumps.
example (T : Real) :
    (∑ j : Fin 1, (sourceScheduleRight (fun _ => 0) 0 T j-sourceScheduleLeft (fun _ => 0) 0 j)) = T :=
  sourceSchedule_total_length (fun _ => 0) 0 T rfl

-- 19: a terminal jump may leave a singleton final branch.
example (tau : Nat -> Real) (J : Nat) :
    sourceScheduleRight tau J (tau J) (Fin.last J) = sourceScheduleLeft tau J (Fin.last J) := by
  simp [sourceScheduleRight,sourceScheduleLeft]

-- 20: the unused horizon labels have a singleton, never a fictitious solution interval.
example (tau : Nat -> Real) (J n : Nat) (T : Real) (hn : J < n) :
    sourceHorizonEndpoint tau J T n = tau n := by
  simp [sourceHorizonEndpoint, show ¬ n < J from by omega, show n ≠ J from by omega]

-- 21: zero discrepancy needs no positive-radius or sign assumption on A_sp.
example {N d : Nat} (X : Real -> SourceFiniteConfiguration N d) (T A_sp : Real) :
    SourceRightAntiSpikiness X X T A_sp := by
  intro t ht
  simp

-- 22: a zero horizon makes the literal nonlinear smallness automatic.
example (kappa : Real -> Real) (tau eta : Nat -> Real) (J : Nat)
    (delta deltaTilde A cD : Real) : SourceTrackingSmallness kappa tau eta J 0 delta deltaTilde A cD := by
  unfold SourceTrackingSmallness
  norm_num

-- 23: preserve the explicit loss, do not infer a conditional failure probability.
example (p : Real) (hp : 0 < p) : 17*p/32 < p := by linarith

-- 24: an event carrying an implication bounds restricted outer failure.
example {S : Type*} [MeasurableSpace S] (rho : Measure S) [IsProbabilityMeasure rho]
    (p : Real) (hp : 0 < p) (Good : Set S) (R Q : S -> Prop)
    (hb : rho.real Good.compl ≤ 17*p/32) (h : ∀ s, s ∈ Good -> R s -> Q s) :
    rho.real {s | R s ∧ ¬ Q s} < p :=
  (source_final_restricted_tracking_failure rho p hp Good R Q hb h).2
