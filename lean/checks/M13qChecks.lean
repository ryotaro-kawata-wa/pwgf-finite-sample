import PaperFormalization.Manuscript.SourceOriginalCanonicalJump
import PaperFormalization.Manuscript.SourceActualFiniteConstruction
import PaperFormalization.Manuscript.SourcePopulationGammaRadius
import PaperFormalization.Manuscript.SourceFreshAuxiliaryHistories

/-! Verified M13q boundary diagnostics. See CODEX_HANDOFF_M13Q.md for the receipt. -/
open Matrix MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory Matrix.Norms.Frobenius
namespace PaperFormalization.Manuscript

#check PaperFormalization.Manuscript.SourceAllMomentDomains
#print axioms PaperFormalization.Manuscript.SourceAllMomentDomains
#check PaperFormalization.Manuscript.source_empirical_moment_mem_all_domains
#print axioms PaperFormalization.Manuscript.source_empirical_moment_mem_all_domains
#check PaperFormalization.Manuscript.source_empirical_factor_hermitian_all_domains
#print axioms PaperFormalization.Manuscript.source_empirical_factor_hermitian_all_domains
#check PaperFormalization.Manuscript.source_continuous_empiricalMomentMap
#print axioms PaperFormalization.Manuscript.source_continuous_empiricalMomentMap
#check PaperFormalization.Manuscript.source_empirical_factor_continuous_all_domains
#print axioms PaperFormalization.Manuscript.source_empirical_factor_continuous_all_domains
#check PaperFormalization.Manuscript.source_empirical_drift_contDiff_all_domains
#print axioms PaperFormalization.Manuscript.source_empirical_drift_contDiff_all_domains
#check PaperFormalization.Manuscript.source_local_continuous_flow_of_contDiff
#print axioms PaperFormalization.Manuscript.source_local_continuous_flow_of_contDiff
#check PaperFormalization.Manuscript.source_exists_finite_scale_of_integrable_exp
#print axioms PaperFormalization.Manuscript.source_exists_finite_scale_of_integrable_exp
#check PaperFormalization.Manuscript.source_ae_finite_scale_of_joint_exp
#print axioms PaperFormalization.Manuscript.source_ae_finite_scale_of_joint_exp
#check PaperFormalization.Manuscript.source_ae_finite_scale_of_mixture_class
#print axioms PaperFormalization.Manuscript.source_ae_finite_scale_of_mixture_class
#check PaperFormalization.Manuscript.sourceGramContinuousENormMatrix
#print axioms PaperFormalization.Manuscript.sourceGramContinuousENormMatrix
#check PaperFormalization.Manuscript.sourceGramMeasurableMatrix
#print axioms PaperFormalization.Manuscript.sourceGramMeasurableMatrix
#check PaperFormalization.Manuscript.sourceGramBorelMatrix
#print axioms PaperFormalization.Manuscript.sourceGramBorelMatrix
#check PaperFormalization.Manuscript.source_actual_gram_eq_tensor
#print axioms PaperFormalization.Manuscript.source_actual_gram_eq_tensor
#check PaperFormalization.Manuscript.sourcePopulationGramVersion
#print axioms PaperFormalization.Manuscript.sourcePopulationGramVersion
#check PaperFormalization.Manuscript.sourcePopulationGramVersion_measurable
#print axioms PaperFormalization.Manuscript.sourcePopulationGramVersion_measurable
#check PaperFormalization.Manuscript.sourcePopulationGramVersion_eq_actual
#print axioms PaperFormalization.Manuscript.sourcePopulationGramVersion_eq_actual
#check PaperFormalization.Manuscript.source_feature_integrable_of_source_class
#print axioms PaperFormalization.Manuscript.source_feature_integrable_of_source_class
#check PaperFormalization.Manuscript.source_actual_gram_regular_of_finite_scales
#print axioms PaperFormalization.Manuscript.source_actual_gram_regular_of_finite_scales
#check PaperFormalization.Manuscript.source_actual_gram_version_ae
#print axioms PaperFormalization.Manuscript.source_actual_gram_version_ae
#check PaperFormalization.Manuscript.sourceAEWhiteningMatrixSpace
#print axioms PaperFormalization.Manuscript.sourceAEWhiteningMatrixSpace
#check PaperFormalization.Manuscript.sourceAEWhiteningMatrixBorel
#print axioms PaperFormalization.Manuscript.sourceAEWhiteningMatrixBorel
#check PaperFormalization.Manuscript.source_conditional_aligned_seed_of_aemeasurable
#print axioms PaperFormalization.Manuscript.source_conditional_aligned_seed_of_aemeasurable
#check PaperFormalization.Manuscript.sourceAEJumpMatrixMeasurable
#print axioms PaperFormalization.Manuscript.sourceAEJumpMatrixMeasurable
#check PaperFormalization.Manuscript.sourceAEJumpMatrixBorel
#print axioms PaperFormalization.Manuscript.sourceAEJumpMatrixBorel
#check PaperFormalization.Manuscript.exists_source_original_jump_view_ae_covariance
#print axioms PaperFormalization.Manuscript.exists_source_original_jump_view_ae_covariance
#check PaperFormalization.Manuscript.exists_source_analytic_original_jump_view
#print axioms PaperFormalization.Manuscript.exists_source_analytic_original_jump_view
#check PaperFormalization.Manuscript.source_condDistrib_fresh_evaluation
#print axioms PaperFormalization.Manuscript.source_condDistrib_fresh_evaluation
#check PaperFormalization.Manuscript.source_fresh_joint_after_auxiliary
#print axioms PaperFormalization.Manuscript.source_fresh_joint_after_auxiliary
#check PaperFormalization.Manuscript.source_auxiliary_history_marginal
#print axioms PaperFormalization.Manuscript.source_auxiliary_history_marginal
#check PaperFormalization.Manuscript.source_condDistrib_fresh_evaluation_after_auxiliary
#print axioms PaperFormalization.Manuscript.source_condDistrib_fresh_evaluation_after_auxiliary
#check PaperFormalization.Manuscript.source_fresh_evaluation_gaussian
#print axioms PaperFormalization.Manuscript.source_fresh_evaluation_gaussian
#check PaperFormalization.Manuscript.source_original_map_after_auxiliary
#print axioms PaperFormalization.Manuscript.source_original_map_after_auxiliary
#check PaperFormalization.Manuscript.source_fresh_independent_after_auxiliary
#print axioms PaperFormalization.Manuscript.source_fresh_independent_after_auxiliary
#check PaperFormalization.Manuscript.source_independence_pullback
#print axioms PaperFormalization.Manuscript.source_independence_pullback
#check PaperFormalization.Manuscript.source_characteristic_mixture
#print axioms PaperFormalization.Manuscript.source_characteristic_mixture
#check PaperFormalization.Manuscript.source_full_history_coefficient_mixture
#print axioms PaperFormalization.Manuscript.source_full_history_coefficient_mixture
#check PaperFormalization.Manuscript.source_full_history_finite_scales_of_reference_moments
#print axioms PaperFormalization.Manuscript.source_full_history_finite_scales_of_reference_moments
#check PaperFormalization.Manuscript.exists_source_original_fresh_jump
#print axioms PaperFormalization.Manuscript.exists_source_original_fresh_jump
#check PaperFormalization.Manuscript.source_reference_kernel_support_of_original
#print axioms PaperFormalization.Manuscript.source_reference_kernel_support_of_original
#check PaperFormalization.Manuscript.source_pair_population_gamma_inputs
#print axioms PaperFormalization.Manuscript.source_pair_population_gamma_inputs
#check PaperFormalization.Manuscript.sourceOriginalGammaThreshold
#print axioms PaperFormalization.Manuscript.sourceOriginalGammaThreshold
#check PaperFormalization.Manuscript.sourceOriginalRadiusLoss
#print axioms PaperFormalization.Manuscript.sourceOriginalRadiusLoss
#check PaperFormalization.Manuscript.exists_source_population_gamma_radius_event
#print axioms PaperFormalization.Manuscript.exists_source_population_gamma_radius_event
#check PaperFormalization.Manuscript.sourceCanonicalMatrixMeasurable
#print axioms PaperFormalization.Manuscript.sourceCanonicalMatrixMeasurable
#check PaperFormalization.Manuscript.sourceCanonicalMatrixBorel
#print axioms PaperFormalization.Manuscript.sourceCanonicalMatrixBorel
#check PaperFormalization.Manuscript.sourcePsdClip
#print axioms PaperFormalization.Manuscript.sourcePsdClip
#check PaperFormalization.Manuscript.sourcePsdClip_pos
#print axioms PaperFormalization.Manuscript.sourcePsdClip_pos
#check PaperFormalization.Manuscript.sourcePsdClip_eq
#print axioms PaperFormalization.Manuscript.sourcePsdClip_eq
#check PaperFormalization.Manuscript.sourcePsdClip_measurable
#print axioms PaperFormalization.Manuscript.sourcePsdClip_measurable
#check PaperFormalization.Manuscript.sourceCanonicalWhiteningSeed
#print axioms PaperFormalization.Manuscript.sourceCanonicalWhiteningSeed
#check PaperFormalization.Manuscript.sourceCanonicalWhiteningSeed_measurable
#print axioms PaperFormalization.Manuscript.sourceCanonicalWhiteningSeed_measurable
#check PaperFormalization.Manuscript.sourceCanonicalWhiteningSeed_original_law
#print axioms PaperFormalization.Manuscript.sourceCanonicalWhiteningSeed_original_law
#check PaperFormalization.Manuscript.SourceFiniteConfiguration
#print axioms PaperFormalization.Manuscript.SourceFiniteConfiguration
#check PaperFormalization.Manuscript.sourcePopulationPrefix
#print axioms PaperFormalization.Manuscript.sourcePopulationPrefix
#check PaperFormalization.Manuscript.sourcePopulationPrefix_measurable
#print axioms PaperFormalization.Manuscript.sourcePopulationPrefix_measurable
#check PaperFormalization.Manuscript.sourceCanonicalCoupledStep
#print axioms PaperFormalization.Manuscript.sourceCanonicalCoupledStep
#check PaperFormalization.Manuscript.sourceCanonicalCoupledPost
#print axioms PaperFormalization.Manuscript.sourceCanonicalCoupledPost
#check PaperFormalization.Manuscript.sourceCanonicalCoupledPost_zero
#print axioms PaperFormalization.Manuscript.sourceCanonicalCoupledPost_zero
#check PaperFormalization.Manuscript.sourceCanonicalCoupledPost_reference
#print axioms PaperFormalization.Manuscript.sourceCanonicalCoupledPost_reference
#check PaperFormalization.Manuscript.sourceCanonicalCoupledPost_measurable
#print axioms PaperFormalization.Manuscript.sourceCanonicalCoupledPost_measurable
#check PaperFormalization.Manuscript.sourceCanonicalCoupledPost_reference_joint_law
#print axioms PaperFormalization.Manuscript.sourceCanonicalCoupledPost_reference_joint_law
#check PaperFormalization.Manuscript.sourcePopulationFieldJump
#print axioms PaperFormalization.Manuscript.sourcePopulationFieldJump
#check PaperFormalization.Manuscript.sourceActualCovarianceVersion
#print axioms PaperFormalization.Manuscript.sourceActualCovarianceVersion
#check PaperFormalization.Manuscript.sourceActualCovarianceVersion_measurable
#print axioms PaperFormalization.Manuscript.sourceActualCovarianceVersion_measurable
#check PaperFormalization.Manuscript.sourceActualFinitePost
#print axioms PaperFormalization.Manuscript.sourceActualFinitePost
#check PaperFormalization.Manuscript.sourceActualFinitePost_measurable
#print axioms PaperFormalization.Manuscript.sourceActualFinitePost_measurable
#check PaperFormalization.Manuscript.sourceActualFinitePost_reference
#print axioms PaperFormalization.Manuscript.sourceActualFinitePost_reference
#check PaperFormalization.Manuscript.source_original_canonical_seed_law
#print axioms PaperFormalization.Manuscript.source_original_canonical_seed_law
#check PaperFormalization.Manuscript.sourceAuxiliaryHistory
#print axioms PaperFormalization.Manuscript.sourceAuxiliaryHistory
#check PaperFormalization.Manuscript.sourceAuxiliaryHistory_measurable
#print axioms PaperFormalization.Manuscript.sourceAuxiliaryHistory_measurable
#check PaperFormalization.Manuscript.sourceAuxiliaryHistory_original
#print axioms PaperFormalization.Manuscript.sourceAuxiliaryHistory_original
#check PaperFormalization.Manuscript.source_auxiliary_history_fresh_independent
#print axioms PaperFormalization.Manuscript.source_auxiliary_history_fresh_independent
#check PaperFormalization.Manuscript.source_auxiliary_innovation_marginal
#print axioms PaperFormalization.Manuscript.source_auxiliary_innovation_marginal
#check PaperFormalization.Manuscript.source_auxiliary_history_fresh_gaussian
#print axioms PaperFormalization.Manuscript.source_auxiliary_history_fresh_gaussian

-- 1: the population prefix discards auxiliary values exactly.
example {W A : Type*} {n : Nat} (f : Fin n -> W) (g : Fin n -> A) :
    sourcePopulationPrefix (fun i => (f i,g i)) = f := rfl

-- 2: arbitrary changes to auxiliaries do not alter the population prefix.
example {W A : Type*} {n : Nat} (f : Fin n -> W) (g h : Fin n -> A) :
    sourcePopulationPrefix (fun i => (f i,g i)) = sourcePopulationPrefix (fun i => (f i,h i)) := rfl

-- 3: PSD clipping is the identity on an actual PSD matrix.
example {I : Type*} [Fintype I] [DecidableEq I] (C : Matrix I I Real) (hC : C.PosSemidef) :
    sourcePsdClip C = C := sourcePsdClip_eq C hC

-- 4: singular zero covariance is included.
example {I : Type*} [Fintype I] [DecidableEq I] :
    sourcePsdClip (0 : Matrix I I Real) = 0 := sourcePsdClip_eq _ PosSemidef.zero

-- 5: the raw reference update does not use the whitened coordinate.
example {N d : Nat} (M) (hM) (eta : Real) (C)
    (X Y V : SourceFiniteConfiguration N d) (aux : EuclideanSpace Real (Fin N × Fin d)) :
    (sourceCanonicalCoupledStep M hM eta C X Y V aux).2 = Y + eta • V := rfl

-- 6: zero amplitude leaves both states unchanged.
example {N d : Nat} (M) (hM) (C)
    (X Y V : SourceFiniteConfiguration N d) (aux : EuclideanSpace Real (Fin N × Fin d)) :
    sourceCanonicalCoupledStep M hM 0 C X Y V aux = (X,Y) := by
  simp only [sourceCanonicalCoupledStep,zero_smul,add_zero,sourceParticleUnflatten_particleFlatten]

-- 7: no jumps with arbitrary flow and field inputs.
example {N d : Nat} {W : Type*} (tau eta : Nat -> Real) (flowX flowY field M hM C)
    (h : Fin 0 -> W × EuclideanSpace Real (Fin N × Fin d)) (u : SourceFiniteConfiguration N d) :
    sourceCanonicalCoupledPost tau eta flowX flowY field M hM C 0 h u = (u,u) := rfl

-- 8: no jumps with zero particle and spatial dimensions.
example (tau eta : Nat -> Real) (flowX flowY field M hM C)
    (h : Fin 0 -> Bool × EuclideanSpace Real (Fin 0 × Fin 0)) (u : SourceFiniteConfiguration 0 0) :
    sourceCanonicalCoupledPost tau eta flowX flowY field M hM C 0 h u = (u,u) := rfl

-- 9: the whole recurrence preserves the original one-seed characteristic.
example {N d : Nat} {W : Type*} (tau eta : Nat -> Real) (flowX flowY field M hM C)
    (n : Nat) (h : Fin n -> W × EuclideanSpace Real (Fin N × Fin d))
    (u : SourceFiniteConfiguration N d) (i : Fin N) :
    (sourceCanonicalCoupledPost tau eta flowX flowY field M hM C n h u).2 i =
      sourceReferencePost tau flowY (fun n pop w x => x + eta n • field n pop w x)
        n (sourcePopulationPrefix h) (u i) :=
  sourceCanonicalCoupledPost_reference tau eta flowX flowY field M hM C n h u i

-- 10: changing auxiliaries does not change the reference coordinate.
example {N d : Nat} {W : Type*} (tau eta : Nat -> Real) (flowX flowY field M hM C)
    (n : Nat) (h h' : Fin n -> W × EuclideanSpace Real (Fin N × Fin d))
    (same : sourcePopulationPrefix h = sourcePopulationPrefix h')
    (u : SourceFiniteConfiguration N d) (i : Fin N) :
    (sourceCanonicalCoupledPost tau eta flowX flowY field M hM C n h u).2 i =
      (sourceCanonicalCoupledPost tau eta flowX flowY field M hM C n h' u).2 i := by
  rw [sourceCanonicalCoupledPost_reference,sourceCanonicalCoupledPost_reference,same]

-- 11: level zero uses the universe-lifted original history.
example {O S A : Type*} [MeasurableSpace O] [MeasurableSpace S] [MeasurableSpace A]
    (H : O -> S) (z : SourceAuxiliarySpace O A 0) :
    sourceAuxiliaryOriginal 0 (sourceAuxiliaryHistory H 0 z) = H z.down := rfl

-- 12: every auxiliary level retains the original prehistory.
example {O S A : Type*} [MeasurableSpace O] [MeasurableSpace S] [MeasurableSpace A]
    (H : O -> S) (n : Nat) (z : SourceAuxiliarySpace O A n) :
    sourceAuxiliaryOriginal n (sourceAuxiliaryHistory H n z) = H (sourceAuxiliaryOriginal n z) :=
  sourceAuxiliaryHistory_original H n z

-- 13: independent extension preserves an original observable law.
example {O A E : Type*} [MeasurableSpace O] [MeasurableSpace A] [MeasurableSpace E]
    (nu : Measure O) [IsProbabilityMeasure nu] (lambda : Measure A) [IsProbabilityMeasure lambda]
    (f : O -> E) (hf : Measurable f) :
    (nu.prod lambda).map (fun z => f z.1) = nu.map f :=
  source_original_map_after_auxiliary nu lambda f hf

-- 14: literal radius loss vanishes for an empty cloud.
example (J : Nat) (T alpha K0 D : Real) (B : NNReal) :
    sourceOriginalRadiusLoss J 0 T alpha K0 D B = 0 := by
  simp only [sourceOriginalRadiusLoss,Nat.cast_zero,mul_zero,zero_mul]

-- 15: empirical-moment continuity does not need a nonempty cloud.
example {d : Nat} {H : Nat -> Type*} [∀ n, NormedAddCommGroup (H n)]
    [∀ n, InnerProductSpace Real (H n)] [∀ n, CompleteSpace (H n)]
    (J : EuclideanSpace Real (Fin d) -> lp H 2) (hJ : Continuous J) :
    Continuous (empiricalMomentMap J : SourceFiniteConfiguration 0 d -> lp H 2) :=
  source_continuous_empiricalMomentMap J hJ

-- 16: the PSD rule permits an empty matrix index.
example : (sourcePsdClip (0 : Matrix (Fin 0) (Fin 0) Real)).PosSemidef := sourcePsdClip_pos _

end PaperFormalization.Manuscript
