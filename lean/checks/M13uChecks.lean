import PaperFormalization.Manuscript.VarianceCosineComparisonAssumptions

/-! M13u EXECUTED boundary diagnostics. N=0 appears ONLY in total matrix definitions. -/
open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators NNReal
open PaperFormalization.Manuscript

#check PaperFormalization.Manuscript.VarianceCosinePoint
#print axioms PaperFormalization.Manuscript.VarianceCosinePoint
#check PaperFormalization.Manuscript.VarianceCosineHilbert
#print axioms PaperFormalization.Manuscript.VarianceCosineHilbert
#check PaperFormalization.Manuscript.varianceCosineScalar
#print axioms PaperFormalization.Manuscript.varianceCosineScalar
#check PaperFormalization.Manuscript.varianceCosinePoint
#print axioms PaperFormalization.Manuscript.varianceCosinePoint
#check PaperFormalization.Manuscript.varianceCosinePoint_scalar
#print axioms PaperFormalization.Manuscript.varianceCosinePoint_scalar
#check PaperFormalization.Manuscript.varianceCosineScalar_point
#print axioms PaperFormalization.Manuscript.varianceCosineScalar_point
#check PaperFormalization.Manuscript.varianceCosinePoint_norm
#print axioms PaperFormalization.Manuscript.varianceCosinePoint_norm
#check PaperFormalization.Manuscript.varianceCosineScalar_abs
#print axioms PaperFormalization.Manuscript.varianceCosineScalar_abs
#check PaperFormalization.Manuscript.varianceCosineScalar_norm_le
#print axioms PaperFormalization.Manuscript.varianceCosineScalar_norm_le
#check PaperFormalization.Manuscript.varianceCosinePointCLM
#print axioms PaperFormalization.Manuscript.varianceCosinePointCLM
#check PaperFormalization.Manuscript.varianceCosinePointCLM_apply
#print axioms PaperFormalization.Manuscript.varianceCosinePointCLM_apply
#check PaperFormalization.Manuscript.varianceCosineFeature
#print axioms PaperFormalization.Manuscript.varianceCosineFeature
#check PaperFormalization.Manuscript.varianceCosineFeature_contDiff
#print axioms PaperFormalization.Manuscript.varianceCosineFeature_contDiff
#check PaperFormalization.Manuscript.varianceCosineFeature_fderiv
#print axioms PaperFormalization.Manuscript.varianceCosineFeature_fderiv
#check PaperFormalization.Manuscript.varianceCosineFeature_second
#print axioms PaperFormalization.Manuscript.varianceCosineFeature_second
#check PaperFormalization.Manuscript.varianceCosineFeature_third
#print axioms PaperFormalization.Manuscript.varianceCosineFeature_third
#check PaperFormalization.Manuscript.varianceCosineFeature_third_exists
#print axioms PaperFormalization.Manuscript.varianceCosineFeature_third_exists
#check PaperFormalization.Manuscript.varianceCosineFeature_growth
#print axioms PaperFormalization.Manuscript.varianceCosineFeature_growth
#check PaperFormalization.Manuscript.varianceCosineFeature_growth_three
#print axioms PaperFormalization.Manuscript.varianceCosineFeature_growth_three
#check PaperFormalization.Manuscript.varianceCosineWeight
#print axioms PaperFormalization.Manuscript.varianceCosineWeight
#check PaperFormalization.Manuscript.varianceCosineDecode
#print axioms PaperFormalization.Manuscript.varianceCosineDecode
#check PaperFormalization.Manuscript.varianceCosineEncodedFeature
#print axioms PaperFormalization.Manuscript.varianceCosineEncodedFeature
#check PaperFormalization.Manuscript.varianceCosineEncodedFeature_coordinate
#print axioms PaperFormalization.Manuscript.varianceCosineEncodedFeature_coordinate
#check PaperFormalization.Manuscript.varianceCosineDecode_feature
#print axioms PaperFormalization.Manuscript.varianceCosineDecode_feature
#check PaperFormalization.Manuscript.varianceCosineEncodedFeature_two_terms
#print axioms PaperFormalization.Manuscript.varianceCosineEncodedFeature_two_terms
#check PaperFormalization.Manuscript.varianceCosineObjective
#print axioms PaperFormalization.Manuscript.varianceCosineObjective
#check PaperFormalization.Manuscript.varianceCosineMean
#print axioms PaperFormalization.Manuscript.varianceCosineMean
#check PaperFormalization.Manuscript.varianceCosineVariance
#print axioms PaperFormalization.Manuscript.varianceCosineVariance
#check PaperFormalization.Manuscript.varianceCosineFunctional
#print axioms PaperFormalization.Manuscript.varianceCosineFunctional
#check PaperFormalization.Manuscript.varianceCosineObjective_formula
#print axioms PaperFormalization.Manuscript.varianceCosineObjective_formula
#check PaperFormalization.Manuscript.varianceCosineObjective_contDiff
#print axioms PaperFormalization.Manuscript.varianceCosineObjective_contDiff
#check PaperFormalization.Manuscript.varianceCosineObjective_domains
#print axioms PaperFormalization.Manuscript.varianceCosineObjective_domains
#check PaperFormalization.Manuscript.varianceCosine_integrable_coordinates
#print axioms PaperFormalization.Manuscript.varianceCosine_integrable_coordinates
#check PaperFormalization.Manuscript.varianceCosineFeature_integrable
#print axioms PaperFormalization.Manuscript.varianceCosineFeature_integrable
#check PaperFormalization.Manuscript.varianceCosineEncodedFeature_integrable
#print axioms PaperFormalization.Manuscript.varianceCosineEncodedFeature_integrable
#check PaperFormalization.Manuscript.varianceCosineDecode_integral
#print axioms PaperFormalization.Manuscript.varianceCosineDecode_integral
#check PaperFormalization.Manuscript.varianceCosineVariance_eq_second_sub_mean_sq
#print axioms PaperFormalization.Manuscript.varianceCosineVariance_eq_second_sub_mean_sq
#check PaperFormalization.Manuscript.varianceCosineObjective_population_identity
#print axioms PaperFormalization.Manuscript.varianceCosineObjective_population_identity
#check PaperFormalization.Manuscript.varianceCosineFunctional_lower
#print axioms PaperFormalization.Manuscript.varianceCosineFunctional_lower
#check PaperFormalization.Manuscript.varianceCosineFunctional_dirac_one
#print axioms PaperFormalization.Manuscript.varianceCosineFunctional_dirac_one
#check PaperFormalization.Manuscript.varianceCosineDecode_empirical
#print axioms PaperFormalization.Manuscript.varianceCosineDecode_empirical
#check PaperFormalization.Manuscript.varianceCosineMeanDrift
#print axioms PaperFormalization.Manuscript.varianceCosineMeanDrift
#check PaperFormalization.Manuscript.varianceCosineKernel
#print axioms PaperFormalization.Manuscript.varianceCosineKernel
#check PaperFormalization.Manuscript.varianceCosineD1
#print axioms PaperFormalization.Manuscript.varianceCosineD1
#check PaperFormalization.Manuscript.varianceCosineD2
#print axioms PaperFormalization.Manuscript.varianceCosineD2
#check PaperFormalization.Manuscript.varianceCosineD3
#print axioms PaperFormalization.Manuscript.varianceCosineD3
#check PaperFormalization.Manuscript.varianceCosine_hasFDerivAt
#print axioms PaperFormalization.Manuscript.varianceCosine_hasFDerivAt
#check PaperFormalization.Manuscript.varianceCosineD1_hasFDerivAt
#print axioms PaperFormalization.Manuscript.varianceCosineD1_hasFDerivAt
#check PaperFormalization.Manuscript.varianceCosineD2_hasFDerivAt
#print axioms PaperFormalization.Manuscript.varianceCosineD2_hasFDerivAt
#check PaperFormalization.Manuscript.varianceCosine_fderiv
#print axioms PaperFormalization.Manuscript.varianceCosine_fderiv
#check PaperFormalization.Manuscript.varianceCosine_second_fderiv
#print axioms PaperFormalization.Manuscript.varianceCosine_second_fderiv
#check PaperFormalization.Manuscript.varianceCosine_third_fderiv
#print axioms PaperFormalization.Manuscript.varianceCosine_third_fderiv
#check PaperFormalization.Manuscript.varianceCosineDecode_norm_le
#print axioms PaperFormalization.Manuscript.varianceCosineDecode_norm_le
#check PaperFormalization.Manuscript.varianceCosineThirdBound
#print axioms PaperFormalization.Manuscript.varianceCosineThirdBound
#check PaperFormalization.Manuscript.varianceCosine_third_bound
#print axioms PaperFormalization.Manuscript.varianceCosine_third_bound
#check PaperFormalization.Manuscript.varianceCosineKernel_bound
#print axioms PaperFormalization.Manuscript.varianceCosineKernel_bound
#check PaperFormalization.Manuscript.varianceCosineMeanDrift_bound
#print axioms PaperFormalization.Manuscript.varianceCosineMeanDrift_bound
#check PaperFormalization.Manuscript.varianceCosineMeanDrift_hasDerivAt
#print axioms PaperFormalization.Manuscript.varianceCosineMeanDrift_hasDerivAt
#check PaperFormalization.Manuscript.varianceCosineMeanDrift_contDiff
#print axioms PaperFormalization.Manuscript.varianceCosineMeanDrift_contDiff
#check PaperFormalization.Manuscript.varianceCosineMeanDrift_lipschitz
#print axioms PaperFormalization.Manuscript.varianceCosineMeanDrift_lipschitz
#check PaperFormalization.Manuscript.varianceCosineFeatureD1
#print axioms PaperFormalization.Manuscript.varianceCosineFeatureD1
#check PaperFormalization.Manuscript.varianceCosineFeatureD2
#print axioms PaperFormalization.Manuscript.varianceCosineFeatureD2
#check PaperFormalization.Manuscript.varianceCosineEncodedFeature_contDiff
#print axioms PaperFormalization.Manuscript.varianceCosineEncodedFeature_contDiff
#check PaperFormalization.Manuscript.varianceCosineEncodedFeature_hasFDerivAt
#print axioms PaperFormalization.Manuscript.varianceCosineEncodedFeature_hasFDerivAt
#check PaperFormalization.Manuscript.varianceCosineEncodedFeature_fderiv
#print axioms PaperFormalization.Manuscript.varianceCosineEncodedFeature_fderiv
#check PaperFormalization.Manuscript.varianceCosineEncodedFeature_second
#print axioms PaperFormalization.Manuscript.varianceCosineEncodedFeature_second
#check PaperFormalization.Manuscript.varianceCosineDecode_featureD1
#print axioms PaperFormalization.Manuscript.varianceCosineDecode_featureD1
#check PaperFormalization.Manuscript.varianceCosineDecode_featureD2
#print axioms PaperFormalization.Manuscript.varianceCosineDecode_featureD2
#check PaperFormalization.Manuscript.varianceCosine_inner_point
#print axioms PaperFormalization.Manuscript.varianceCosine_inner_point
#check PaperFormalization.Manuscript.varianceCosine_source_field
#print axioms PaperFormalization.Manuscript.varianceCosine_source_field
#check PaperFormalization.Manuscript.varianceCosine_source_spatial
#print axioms PaperFormalization.Manuscript.varianceCosine_source_spatial
#check PaperFormalization.Manuscript.varianceCosine_source_integral_hessian
#print axioms PaperFormalization.Manuscript.varianceCosine_source_integral_hessian
#check PaperFormalization.Manuscript.varianceCosine_source_kernel_matrix
#print axioms PaperFormalization.Manuscript.varianceCosine_source_kernel_matrix
#check PaperFormalization.Manuscript.varianceCosineEmpiricalMean
#print axioms PaperFormalization.Manuscript.varianceCosineEmpiricalMean
#check PaperFormalization.Manuscript.varianceCosine_source_empirical_drift
#print axioms PaperFormalization.Manuscript.varianceCosine_source_empirical_drift
#check PaperFormalization.Manuscript.varianceCosineMean_exists
#print axioms PaperFormalization.Manuscript.varianceCosineMean_exists
#check PaperFormalization.Manuscript.varianceCosineMean_all_initials
#print axioms PaperFormalization.Manuscript.varianceCosineMean_all_initials
#check PaperFormalization.Manuscript.varianceCosineMeanFlow
#print axioms PaperFormalization.Manuscript.varianceCosineMeanFlow
#check PaperFormalization.Manuscript.varianceCosineMeanFlow_start
#print axioms PaperFormalization.Manuscript.varianceCosineMeanFlow_start
#check PaperFormalization.Manuscript.varianceCosineMeanFlow_measurable
#print axioms PaperFormalization.Manuscript.varianceCosineMeanFlow_measurable
#check PaperFormalization.Manuscript.varianceCosineMeanFlow_continuous
#print axioms PaperFormalization.Manuscript.varianceCosineMeanFlow_continuous
#check PaperFormalization.Manuscript.varianceCosineMeanFlow_hasDerivWithinAt
#print axioms PaperFormalization.Manuscript.varianceCosineMeanFlow_hasDerivWithinAt
#check PaperFormalization.Manuscript.varianceCosineMeanFlow_hasDerivAt
#print axioms PaperFormalization.Manuscript.varianceCosineMeanFlow_hasDerivAt
#check PaperFormalization.Manuscript.varianceCosineMean_unique
#print axioms PaperFormalization.Manuscript.varianceCosineMean_unique
#check PaperFormalization.Manuscript.varianceCosineMeanDrift_integer
#print axioms PaperFormalization.Manuscript.varianceCosineMeanDrift_integer
#check PaperFormalization.Manuscript.varianceCosineMean_upper_barrier
#print axioms PaperFormalization.Manuscript.varianceCosineMean_upper_barrier
#check PaperFormalization.Manuscript.varianceCosineMean_lower_barrier
#print axioms PaperFormalization.Manuscript.varianceCosineMean_lower_barrier
#check PaperFormalization.Manuscript.varianceCosineMeanFlow_movement
#print axioms PaperFormalization.Manuscript.varianceCosineMeanFlow_movement
#check PaperFormalization.Manuscript.varianceCosineMeanFlow_zero
#print axioms PaperFormalization.Manuscript.varianceCosineMeanFlow_zero
#check PaperFormalization.Manuscript.varianceCosineGaussian_exp
#print axioms PaperFormalization.Manuscript.varianceCosineGaussian_exp
#check PaperFormalization.Manuscript.varianceCosineGaussian_scalar_root
#print axioms PaperFormalization.Manuscript.varianceCosineGaussian_scalar_root
#check PaperFormalization.Manuscript.varianceCosineGaussian_moment_class
#print axioms PaperFormalization.Manuscript.varianceCosineGaussian_moment_class
#check PaperFormalization.Manuscript.varianceCosine_moment_of_gaussian_envelope
#print axioms PaperFormalization.Manuscript.varianceCosine_moment_of_gaussian_envelope
#check PaperFormalization.Manuscript.varianceCosineConstantDirection
#print axioms PaperFormalization.Manuscript.varianceCosineConstantDirection
#check PaperFormalization.Manuscript.varianceCosineConstantDirection_norm
#print axioms PaperFormalization.Manuscript.varianceCosineConstantDirection_norm
#check PaperFormalization.Manuscript.varianceCosineNormalMean
#print axioms PaperFormalization.Manuscript.varianceCosineNormalMean
#check PaperFormalization.Manuscript.varianceCosineNormalMean_law
#print axioms PaperFormalization.Manuscript.varianceCosineNormalMean_law
#check PaperFormalization.Manuscript.varianceCosinePostMeanX
#print axioms PaperFormalization.Manuscript.varianceCosinePostMeanX
#check PaperFormalization.Manuscript.varianceCosinePostMeanY
#print axioms PaperFormalization.Manuscript.varianceCosinePostMeanY
#check PaperFormalization.Manuscript.varianceCosineBranchMeanX
#print axioms PaperFormalization.Manuscript.varianceCosineBranchMeanX
#check PaperFormalization.Manuscript.varianceCosineBranchMeanY
#print axioms PaperFormalization.Manuscript.varianceCosineBranchMeanY
#check PaperFormalization.Manuscript.varianceCosinePairBranch
#print axioms PaperFormalization.Manuscript.varianceCosinePairBranch
#check PaperFormalization.Manuscript.varianceCosineRightPair
#print axioms PaperFormalization.Manuscript.varianceCosineRightPair
#check PaperFormalization.Manuscript.varianceCosinePairBranch_difference
#print axioms PaperFormalization.Manuscript.varianceCosinePairBranch_difference
#check PaperFormalization.Manuscript.varianceCosineEmpiricalMean_bound
#print axioms PaperFormalization.Manuscript.varianceCosineEmpiricalMean_bound
#check PaperFormalization.Manuscript.varianceCosinePairBranch_meanX
#print axioms PaperFormalization.Manuscript.varianceCosinePairBranch_meanX
#check PaperFormalization.Manuscript.varianceCosinePairBranch_start
#print axioms PaperFormalization.Manuscript.varianceCosinePairBranch_start
#check PaperFormalization.Manuscript.varianceCosinePairBranch_jump
#print axioms PaperFormalization.Manuscript.varianceCosinePairBranch_jump
#check PaperFormalization.Manuscript.varianceCosinePairBranch_continuous
#print axioms PaperFormalization.Manuscript.varianceCosinePairBranch_continuous
#check PaperFormalization.Manuscript.varianceCosinePairBranch_measurable
#print axioms PaperFormalization.Manuscript.varianceCosinePairBranch_measurable
#check PaperFormalization.Manuscript.varianceCosinePairBranch_envelope
#print axioms PaperFormalization.Manuscript.varianceCosinePairBranch_envelope
#check PaperFormalization.Manuscript.varianceCosineMomentScale
#print axioms PaperFormalization.Manuscript.varianceCosineMomentScale
#check PaperFormalization.Manuscript.varianceCosineSpeed
#print axioms PaperFormalization.Manuscript.varianceCosineSpeed
#check PaperFormalization.Manuscript.varianceCosine_common_displacement
#print axioms PaperFormalization.Manuscript.varianceCosine_common_displacement
#check PaperFormalization.Manuscript.varianceCosinePairBranch_antispike
#print axioms PaperFormalization.Manuscript.varianceCosinePairBranch_antispike
#check PaperFormalization.Manuscript.varianceCosineRight_antiSpikiness
#print axioms PaperFormalization.Manuscript.varianceCosineRight_antiSpikiness
#check PaperFormalization.Manuscript.varianceCosineBranchMeanX_ode
#print axioms PaperFormalization.Manuscript.varianceCosineBranchMeanX_ode
#check PaperFormalization.Manuscript.varianceCosineBranchMeanY_ode
#print axioms PaperFormalization.Manuscript.varianceCosineBranchMeanY_ode
#check PaperFormalization.Manuscript.varianceCosinePairBranch_coordinate_ode
#print axioms PaperFormalization.Manuscript.varianceCosinePairBranch_coordinate_ode
#check PaperFormalization.Manuscript.varianceCosine_closed_lipschitz
#print axioms PaperFormalization.Manuscript.varianceCosine_closed_lipschitz
#check PaperFormalization.Manuscript.varianceCosinePairBranch_lipschitz
#print axioms PaperFormalization.Manuscript.varianceCosinePairBranch_lipschitz
#check PaperFormalization.Manuscript.varianceCosinePairBranch_moments
#print axioms PaperFormalization.Manuscript.varianceCosinePairBranch_moments
#check PaperFormalization.Manuscript.varianceCosineRankFactor
#print axioms PaperFormalization.Manuscript.varianceCosineRankFactor
#check PaperFormalization.Manuscript.varianceCosineRankCovariance
#print axioms PaperFormalization.Manuscript.varianceCosineRankCovariance
#check PaperFormalization.Manuscript.varianceCosineFieldVector
#print axioms PaperFormalization.Manuscript.varianceCosineFieldVector
#check PaperFormalization.Manuscript.varianceCosineRankFactor_hermitian
#print axioms PaperFormalization.Manuscript.varianceCosineRankFactor_hermitian
#check PaperFormalization.Manuscript.varianceCosineRankFactor_covariance
#print axioms PaperFormalization.Manuscript.varianceCosineRankFactor_covariance
#check PaperFormalization.Manuscript.varianceCosineRankCovariance_pos
#print axioms PaperFormalization.Manuscript.varianceCosineRankCovariance_pos
#check PaperFormalization.Manuscript.varianceCosineRankFactor_apply
#print axioms PaperFormalization.Manuscript.varianceCosineRankFactor_apply
#check PaperFormalization.Manuscript.varianceCosine_source_empirical_factor
#print axioms PaperFormalization.Manuscript.varianceCosine_source_empirical_factor
#check PaperFormalization.Manuscript.varianceCosine_population_covariance
#print axioms PaperFormalization.Manuscript.varianceCosine_population_covariance
#check PaperFormalization.Manuscript.varianceCosineFieldVector_gaussian
#print axioms PaperFormalization.Manuscript.varianceCosineFieldVector_gaussian
#check PaperFormalization.Manuscript.varianceCosine_source_jump_action
#print axioms PaperFormalization.Manuscript.varianceCosine_source_jump_action
#check PaperFormalization.Manuscript.VarianceCosineCouplingSpace
#print axioms PaperFormalization.Manuscript.VarianceCosineCouplingSpace
#check PaperFormalization.Manuscript.varianceCosineCouplingLaw
#print axioms PaperFormalization.Manuscript.varianceCosineCouplingLaw
#check PaperFormalization.Manuscript.varianceCosineCouplingLaw_probability
#print axioms PaperFormalization.Manuscript.varianceCosineCouplingLaw_probability
#check PaperFormalization.Manuscript.varianceCosineReferencePre
#print axioms PaperFormalization.Manuscript.varianceCosineReferencePre
#check PaperFormalization.Manuscript.varianceCosineReferencePre_measurable
#print axioms PaperFormalization.Manuscript.varianceCosineReferencePre_measurable
#check PaperFormalization.Manuscript.varianceCosineReferencePre_hermitian
#print axioms PaperFormalization.Manuscript.varianceCosineReferencePre_hermitian
#check PaperFormalization.Manuscript.varianceCosineCouplingSeed
#print axioms PaperFormalization.Manuscript.varianceCosineCouplingSeed
#check PaperFormalization.Manuscript.varianceCosineCouplingZeta
#print axioms PaperFormalization.Manuscript.varianceCosineCouplingZeta
#check PaperFormalization.Manuscript.varianceCosineCouplingSeed_measurable
#print axioms PaperFormalization.Manuscript.varianceCosineCouplingSeed_measurable
#check PaperFormalization.Manuscript.varianceCosineCouplingZeta_measurable
#print axioms PaperFormalization.Manuscript.varianceCosineCouplingZeta_measurable
#check PaperFormalization.Manuscript.varianceCosineCouplingSeed_laws
#print axioms PaperFormalization.Manuscript.varianceCosineCouplingSeed_laws
#check PaperFormalization.Manuscript.varianceCosineCoupling_original_law
#print axioms PaperFormalization.Manuscript.varianceCosineCoupling_original_law
#check PaperFormalization.Manuscript.varianceCosineCoupling_normal_marginals
#print axioms PaperFormalization.Manuscript.varianceCosineCoupling_normal_marginals
#check PaperFormalization.Manuscript.varianceCosineCoupling_comparison_regularities
#print axioms PaperFormalization.Manuscript.varianceCosineCoupling_comparison_regularities
#check PaperFormalization.Manuscript.varianceCosineAffine
#print axioms PaperFormalization.Manuscript.varianceCosineAffine
#check PaperFormalization.Manuscript.varianceCosinePopulation
#print axioms PaperFormalization.Manuscript.varianceCosinePopulation
#check PaperFormalization.Manuscript.varianceCosineAffine_measurable
#print axioms PaperFormalization.Manuscript.varianceCosineAffine_measurable
#check PaperFormalization.Manuscript.varianceCosinePopulation_probability
#print axioms PaperFormalization.Manuscript.varianceCosinePopulation_probability
#check PaperFormalization.Manuscript.varianceCosine_bounded_initial_memLp
#print axioms PaperFormalization.Manuscript.varianceCosine_bounded_initial_memLp
#check PaperFormalization.Manuscript.varianceCosinePopulation_memLp
#print axioms PaperFormalization.Manuscript.varianceCosinePopulation_memLp
#check PaperFormalization.Manuscript.varianceCosinePopulation_mean_variance
#print axioms PaperFormalization.Manuscript.varianceCosinePopulation_mean_variance
#check PaperFormalization.Manuscript.varianceCosinePopulation_objective
#print axioms PaperFormalization.Manuscript.varianceCosinePopulation_objective
#check PaperFormalization.Manuscript.varianceCosinePopulation_field_spec
#print axioms PaperFormalization.Manuscript.varianceCosinePopulation_field_spec
#check PaperFormalization.Manuscript.varianceCosineInitial_marginal
#print axioms PaperFormalization.Manuscript.varianceCosineInitial_marginal
#check PaperFormalization.Manuscript.varianceCosineInitial_bounded
#print axioms PaperFormalization.Manuscript.varianceCosineInitial_bounded
#check PaperFormalization.Manuscript.varianceCosineInitial_iid
#print axioms PaperFormalization.Manuscript.varianceCosineInitial_iid
#check PaperFormalization.Manuscript.varianceCosineTimes
#print axioms PaperFormalization.Manuscript.varianceCosineTimes
#check PaperFormalization.Manuscript.varianceCosineAmplitudes
#print axioms PaperFormalization.Manuscript.varianceCosineAmplitudes
#check PaperFormalization.Manuscript.varianceCosineFlowY
#print axioms PaperFormalization.Manuscript.varianceCosineFlowY
#check PaperFormalization.Manuscript.varianceCosineField
#print axioms PaperFormalization.Manuscript.varianceCosineField
#check PaperFormalization.Manuscript.varianceCosineFlowY_measurable
#print axioms PaperFormalization.Manuscript.varianceCosineFlowY_measurable
#check PaperFormalization.Manuscript.varianceCosineField_measurable
#print axioms PaperFormalization.Manuscript.varianceCosineField_measurable
#check PaperFormalization.Manuscript.varianceCosineFlowY_start
#print axioms PaperFormalization.Manuscript.varianceCosineFlowY_start
#check PaperFormalization.Manuscript.varianceCosineReferencePre_zero
#print axioms PaperFormalization.Manuscript.varianceCosineReferencePre_zero
#check PaperFormalization.Manuscript.varianceCosineReferenceBranch_formula
#print axioms PaperFormalization.Manuscript.varianceCosineReferenceBranch_formula
#check PaperFormalization.Manuscript.varianceCosine_tensor_integrable
#print axioms PaperFormalization.Manuscript.varianceCosine_tensor_integrable
#check PaperFormalization.Manuscript.varianceCosineActualCovariance_zero
#print axioms PaperFormalization.Manuscript.varianceCosineActualCovariance_zero
#check PaperFormalization.Manuscript.varianceCosine_reference_source_ode
#print axioms PaperFormalization.Manuscript.varianceCosine_reference_source_ode
#check PaperFormalization.Manuscript.varianceCosine_raw_empirical_schedule
#print axioms PaperFormalization.Manuscript.varianceCosine_raw_empirical_schedule
#check PaperFormalization.Manuscript.varianceCosineInnovation
#print axioms PaperFormalization.Manuscript.varianceCosineInnovation
#check PaperFormalization.Manuscript.exists_varianceCosine_common_characteristic
#print axioms PaperFormalization.Manuscript.exists_varianceCosine_common_characteristic
#check PaperFormalization.Manuscript.varianceCosineModelLaw
#print axioms PaperFormalization.Manuscript.varianceCosineModelLaw
#check PaperFormalization.Manuscript.varianceCosineModelBranches
#print axioms PaperFormalization.Manuscript.varianceCosineModelBranches
#check PaperFormalization.Manuscript.VarianceCosineComparisonCertificate
#print axioms PaperFormalization.Manuscript.VarianceCosineComparisonCertificate
#check PaperFormalization.Manuscript.varianceCosine_comparison_assumptions
#print axioms PaperFormalization.Manuscript.varianceCosine_comparison_assumptions
#check PaperFormalization.Manuscript.varianceCosine_comparison_right_moments
#print axioms PaperFormalization.Manuscript.varianceCosine_comparison_right_moments
#check PaperFormalization.Manuscript.varianceCosineTowerCoordinates
#print axioms PaperFormalization.Manuscript.varianceCosineTowerCoordinates
#check PaperFormalization.Manuscript.varianceCosineTower_preserving
#print axioms PaperFormalization.Manuscript.varianceCosineTower_preserving
#check PaperFormalization.Manuscript.varianceCosineTower_map
#print axioms PaperFormalization.Manuscript.varianceCosineTower_map

-- 1: representation preserves the scalar coordinate.
example (x : Real) : varianceCosineScalar (varianceCosinePoint x) = x := varianceCosineScalar_point x
-- 2: the represented particle norm is the original absolute value.
example (x : Real) : norm (varianceCosinePoint x) = abs x := varianceCosinePoint_norm x
-- 3: the first source feature has Lean index zero.
example (x : VarianceCosinePoint) : varianceCosineFeature 0 x = varianceCosineScalar x := rfl
-- 4: the second source feature has Lean index one.
example (x : VarianceCosinePoint) : varianceCosineFeature 1 x = (varianceCosineScalar x)^2 := rfl
-- 5: all higher source coordinates are exactly zero.
example (n : Nat) (x : VarianceCosinePoint) : varianceCosineFeature (n+2) x = 0 := rfl
-- 6: genuine decoded features, without forgetting the exponential weights.
example (x : VarianceCosinePoint) : varianceCosineDecode 1 (varianceCosineEncodedFeature x) =
    (varianceCosineScalar x)^2 := varianceCosineDecode_feature x 1
-- 7: zero moment has objective beta, not zero.
example (a beta : Real) : varianceCosineObjective a beta 0 = beta := by simp [varianceCosineObjective]
-- 8: the third derivative of a quadratic feature vanishes.
example (x : VarianceCosinePoint) : fderiv Real (fderiv Real (fderiv Real (varianceCosineFeature 1))) x = 0 :=
  varianceCosineFeature_third 1 x
-- 9: zero is an unstable mean equilibrium, but still an exact equilibrium.
example (beta : Real) : varianceCosineMeanDrift beta 0 = 0 := by simp [varianceCosineMeanDrift]
-- 10: every integer mean is an equilibrium.
example (beta : Real) (k : Int) : varianceCosineMeanDrift beta k = 0 := varianceCosineMeanDrift_integer beta k
-- 11: the mean starts at its prescribed value, including a zero horizon.
example (beta x : Real) : varianceCosineMeanFlow beta 0 x 0 = x := varianceCosineMeanFlow_start beta 0 x
-- 12: exact negative kernel at the pre-jump population mean.
example (a beta : Real) : varianceCosineKernel a beta 0 = -a-beta*Real.pi^2 := by simp [varianceCosineKernel]
-- 13: covariance zero is not excluded by the factor construction.
example (N : Nat) : varianceCosineRankCovariance N 0 = 0 := by ext i j; simp [varianceCosineRankCovariance]
-- 14: zero factor at every particle count, including the empty algebraic case.
example (N : Nat) : varianceCosineRankFactor N 0 = 0 := by ext i j; simp [varianceCosineRankFactor]
-- 15: constant covariance is PSD even at particle count zero.
example (c : Real) : (varianceCosineRankCovariance 0 c).PosSemidef := varianceCosineRankCovariance_pos 0 c
-- 16: the N=1 mean direction has exactly unit norm.
example : norm (varianceCosineConstantDirection 1) = 1 := varianceCosineConstantDirection_norm 1 (by norm_num)
-- 17: singular Gaussian field law includes a zero coefficient.
example : (gaussianReal 0 1).map (varianceCosineFieldVector 2 0) =
    multivariateGaussian 0 (varianceCosineRankCovariance 2 0) := varianceCosineFieldVector_gaussian 2 (by norm_num) 0
-- 18: all real moment orders, rather than only integers, enter this class.
example : gaussianReal 0 1 ∈ sourceMomentClass 2 2 := varianceCosineGaussian_moment_class
-- 19: bounded initial point mass and a zero amplitude retain the additive constant.
example (a beta : Real) : varianceCosineMomentScale a beta 0 0 = 2 := by simp [varianceCosineMomentScale]
-- 20: bounded-support radius zero still has nonzero sine speed.
example (a beta : Real) : varianceCosineSpeed a beta 0 = beta*Real.pi := by simp [varianceCosineSpeed]
-- 21: the actual initial pair agrees exactly, not only almost everywhere.
example (a beta tau eta T Z zeta : Real) (U : SourceFiniteConfiguration 2 1) :
    varianceCosinePairBranch a beta tau eta T U Z zeta 0 0 = (U,U) :=
  varianceCosinePairBranch_start a beta tau eta T U Z zeta
-- 22: the right value at the jump is label one.
example (a beta tau eta T Z zeta : Real) (U : SourceFiniteConfiguration 2 1) :
    varianceCosineRightPair a beta tau eta T U Z zeta tau = varianceCosinePairBranch a beta tau eta T U Z zeta 1 tau := by
  simp [varianceCosineRightPair]
-- 23: the cubic identity includes zero discrepancy.
example (X : SourceFiniteConfiguration 2 1) :
    (2 : Real)⁻¹*∑ i : Fin 2, norm ((X-X) i)^3 = (norm (X-X)/Real.sqrt 2)^3 := by simp
-- 24: anti-spikiness also holds on a singleton final interval.
example (a beta tau eta Z zeta : Real) (U : SourceFiniteConfiguration 1 1) :
    SourceRightAntiSpikiness (fun t => (varianceCosineRightPair a beta tau eta tau U Z zeta t).1)
      (fun t => (varianceCosineRightPair a beta tau eta tau U Z zeta t).2) tau 1 :=
  varianceCosineRight_antiSpikiness (by norm_num) a beta tau eta tau U Z zeta
-- 25: a zero-length scalar branch does not require interior ODE derivatives.
example (beta x : Real) (hb : 0 <= beta) : x ∈ sourceODEExistenceDomain (varianceCosineMeanDrift beta) 0 0 le_rfl :=
  varianceCosineMean_all_initials beta hb 0 0 le_rfl x
-- 26: exactly one nonzero-amplitude scheduled slot.
example (eta : Real) : varianceCosineAmplitudes eta 1 = 0 := by simp [varianceCosineAmplitudes]
-- 27: zero source time is the original initial time.
example (tau : Real) : varianceCosineTimes tau 0 = 0 := by simp [varianceCosineTimes]
-- 28: no second population innovation is silently sampled.
example (Z : Real) : varianceCosineInnovation 1 Z = 0 := by simp [varianceCosineInnovation]
-- 29: the source characteristic starts at every initial point, at every label.
example (a beta tau eta T : Real) (u : VarianceCosinePoint) (past : Fin 1 -> Real) :
    varianceCosineFlowY a beta tau eta T 1 past tau u = u := by
  simpa [varianceCosineTimes] using varianceCosineFlowY_start a beta tau eta T 1 past u
-- 30: affine scaling by one at zero shift is exactly the original point.
example (u : VarianceCosinePoint) : varianceCosineAffine 0 1 u = u := by
  simp [varianceCosineAffine,varianceCosinePoint_scalar]
