/- M13v EXECUTED boundary diagnostics and complete declaration queries. -/
import PaperFormalization.Manuscript.VarianceCosineCosineFlow
import PaperFormalization.Manuscript.VarianceCosineEscapeGeometry
import PaperFormalization.Manuscript.VarianceCosineSpectralCurvature
import PaperFormalization.Manuscript.VarianceCosineGaussianEscape
import PaperFormalization.Manuscript.VarianceCosinePopulationDecay
import PaperFormalization.Manuscript.CurvatureRecoveryResponse
import PaperFormalization.Manuscript.VarianceCosineResponseControl
import PaperFormalization.Manuscript.VarianceCosineResponseEvent
import PaperFormalization.Manuscript.VarianceCosineRateAlgebra
import PaperFormalization.Manuscript.VarianceCosineLateWindow

open Set MeasureTheory ProbabilityTheory
open PaperFormalization.Manuscript PaperFormalization.Continuous

example (b z : Real) : varianceCosineCosineSolution b z 0 = z :=
  varianceCosineCosineSolution_start b z
example (b t : Real) : varianceCosineCosineSolution b (-1) t = -1 :=
  varianceCosineCosineSolution_odd_equilibrium b t
example (b t : Real) : varianceCosineCosineSolution b 1 t = 1 := by
  simp [varianceCosineCosineSolution,varianceCosineCosineDen]
example (b z t : Real) (hz : -1 <= z) (hz1 : z < 1) :
    0 < varianceCosineCosineDen b z t := varianceCosineCosineDen_pos b z t hz hz1
example (rho : Real) (hr : rho <= 1) (k : Int) :
    varianceCosineEscapeLanding rho (2*(k:Real)+1) := varianceCosineEscapeLanding_odd rho hr k
example (rho : Real) (hr : 0 < rho) (k : Int) :
    ¬ (varianceCosineEscapeLanding rho (2*(k:Real))) := varianceCosineEscapeLanding_not_even rho hr k
example (x : Real) : varianceCosineEvenDistance x ∈ Icc 0 1 := varianceCosineEvenDistance_mem x
example (x : Real) : varianceCosineEscapeLanding 0 x := by
  intro k; exact abs_nonneg _
example (a c : Real) : rayleighInf (varianceCosineHessian 1 a c) = a+c :=
  varianceCosineHessian_rayleigh_one a c
example (a c : Real) : rayleighInf (varianceCosineHessian 2 a c) = min a (a+c) :=
  varianceCosineHessian_rayleigh (by omega) a c
example (k : Real -> Real) : recoveryContinuousResponse k 0 = 0 := by
  simp [recoveryContinuousResponse]
example (k : Real -> Real) (tau eta : Real) : recoveryJumpResponse k tau eta tau = eta :=
  recoveryJumpResponse_at_jump k tau eta
example (k : Real -> Real) (tau t : Real) : recoveryJumpResponse k tau 0 t = 0 := by
  simp [recoveryJumpResponse]
example (k : Real -> Real) (tau eta t : Real) (ht : t < tau) :
    recoveryJumpResponse k tau eta t = 0 := by simp [recoveryJumpResponse,not_le.mpr ht]
example (k : Real -> Real) (tau eta t : Real) (heta : 0 <= eta) :
    0 <= recoveryJumpResponse k tau eta t := recoveryJumpResponse_nonneg k tau eta t heta
example (c t : Real) : (∫ u in t..t, Real.exp (c*(t-u))) = 0 := by simp
example (v : NNReal) : 4 <= varianceCosineEscapeConstant v := varianceCosineEscapeConstant_ge_four v
example (v : NNReal) (p : Real) (hp : 0 < p) (hp1 : p <= 1) :
    0 < varianceCosineEscapeRadius v p := (varianceCosineEscapeRadius_bounds v p hp hp1).1
example (beta tau rho : Real) (hb : 0 < beta) (hr : 0 < rho) :
    Real.exp (varianceCosineCurvatureScale beta*varianceCosineRecoveryTime beta tau rho) =
    2*Real.exp (varianceCosineCurvatureScale beta*tau)/rho := varianceCosineRecoveryTime_exp beta tau rho hb hr
example (k : Real -> Real) (tau eta t : Real) :
    sourceCurvatureEnvelope k (varianceCosineTimes tau) (varianceCosineAmplitudes eta) 0 0 0 1 t = 0 := by
  rw [varianceCosine_source_envelope_one_jump]; simp
example (n : Real) (hn : 0 < n) : (n^(-(1/16:Real)))^3 = n^(-(3/16:Real)) := by
  simpa using (varianceCosine_rate_exponents n 0 hn).1
example (n : Real) (hn : 0 < n) : (n^(-(1/16:Real)))^8 = n^(-(1/2:Real)) := by
  simpa using (varianceCosine_rate_exponents n 0 hn).2.1
example (theta : Real) : (1:Real)^(-(1/16:Real))*(1^theta)^4 = 1 := by simp
example {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega) (A E : Set Omega)
    (hA : P Aᶜ = 0) (hE : P Eᶜ = 0) : P (A ∩ E)ᶜ = 0 := by
  apply le_antisymm _ (by positivity)
  simpa using varianceCosine_same_event_budget P A E 0 le_rfl (by simp [hA]) (by simp [hE])

-- Additional probes selected after reviewing the comparison-only local candidate.
-- These use GitHub-version definitions; no candidate module is overlaid.
example (b t : Real) : 0 < varianceCosineCosineDen b 1 t := by
  norm_num [varianceCosineCosineDen]
example (z t : Real) (hz : -1 <= z) (hz1 : z < 1) :
    varianceCosineCosineSolution (-1) z t ∈ Icc (-1) 1 :=
  varianceCosineCosineSolution_mem (-1) z t hz hz1
example (beta : Real) (hb : 0 <= beta) : varianceCosineRecoveryRate 0 beta = 0 := by
  apply min_eq_left
  unfold varianceCosineCurvatureScale
  positivity
example : rayleighInf (varianceCosineHessian 1 1 2) ≠ min (1 : Real) (1+2) := by
  rw [varianceCosineHessian_rayleigh_one]
  norm_num
example (t : Real) : recoveryContinuousResponse (fun _ => 0) t = t := by
  simp [recoveryContinuousResponse, propagator]
example (a beta t : Real) : varianceCosinePopulationExcess a beta 0 (fun _ => 1) t = 0 := by
  simp [varianceCosinePopulationExcess]
example (S T : Real) (hST : T < S) (P : Real -> Prop) : ∀ t ∈ Icc S T, P t := by
  intro t ht
  exact (not_le_of_gt hST (ht.1.trans ht.2)).elim
example (k : Real -> Real) (tau eta A t : Real) :
    sourceCurvatureEnvelope k (varianceCosineTimes tau) (varianceCosineAmplitudes eta) 0 0 A 1 t = 0 := by
  rw [varianceCosine_source_envelope_one_jump]
  simp

#check PaperFormalization.Manuscript.varianceCosineCurvatureScale
#print axioms PaperFormalization.Manuscript.varianceCosineCurvatureScale
#check PaperFormalization.Manuscript.varianceCosineCosineDrift
#print axioms PaperFormalization.Manuscript.varianceCosineCosineDrift
#check PaperFormalization.Manuscript.varianceCosineCosineDen
#print axioms PaperFormalization.Manuscript.varianceCosineCosineDen
#check PaperFormalization.Manuscript.varianceCosineCosineSolution
#print axioms PaperFormalization.Manuscript.varianceCosineCosineSolution
#check PaperFormalization.Manuscript.varianceCosineCurvatureScale_pos
#print axioms PaperFormalization.Manuscript.varianceCosineCurvatureScale_pos
#check PaperFormalization.Manuscript.varianceCosineCosineDen_pos
#print axioms PaperFormalization.Manuscript.varianceCosineCosineDen_pos
#check PaperFormalization.Manuscript.varianceCosineCosineSolution_start
#print axioms PaperFormalization.Manuscript.varianceCosineCosineSolution_start
#check PaperFormalization.Manuscript.varianceCosineCosineSolution_odd_equilibrium
#print axioms PaperFormalization.Manuscript.varianceCosineCosineSolution_odd_equilibrium
#check PaperFormalization.Manuscript.varianceCosineCosineSolution_continuous
#print axioms PaperFormalization.Manuscript.varianceCosineCosineSolution_continuous
#check PaperFormalization.Manuscript.varianceCosineCosineSolution_mem
#print axioms PaperFormalization.Manuscript.varianceCosineCosineSolution_mem
#check PaperFormalization.Manuscript.varianceCosineCosineSolution_hasDerivAt
#print axioms PaperFormalization.Manuscript.varianceCosineCosineSolution_hasDerivAt
#check PaperFormalization.Manuscript.varianceCosine_cos_of_mean_hasDerivAt
#print axioms PaperFormalization.Manuscript.varianceCosine_cos_of_mean_hasDerivAt
#check PaperFormalization.Manuscript.varianceCosineMeanFlow_cosine
#print axioms PaperFormalization.Manuscript.varianceCosineMeanFlow_cosine
#check PaperFormalization.Manuscript.varianceCosineRecoveryDelay
#print axioms PaperFormalization.Manuscript.varianceCosineRecoveryDelay
#check PaperFormalization.Manuscript.varianceCosineRecoveryDelay_nonneg
#print axioms PaperFormalization.Manuscript.varianceCosineRecoveryDelay_nonneg
#check PaperFormalization.Manuscript.varianceCosineRecoveryDelay_exp
#print axioms PaperFormalization.Manuscript.varianceCosineRecoveryDelay_exp
#check PaperFormalization.Manuscript.varianceCosineCosineSolution_recovered
#print axioms PaperFormalization.Manuscript.varianceCosineCosineSolution_recovered
#check PaperFormalization.Manuscript.varianceCosineMeanFlow_cosine_recovered
#print axioms PaperFormalization.Manuscript.varianceCosineMeanFlow_cosine_recovered
#check PaperFormalization.Manuscript.varianceCosineEscapeLanding
#print axioms PaperFormalization.Manuscript.varianceCosineEscapeLanding
#check PaperFormalization.Manuscript.varianceCosineEvenDistance
#print axioms PaperFormalization.Manuscript.varianceCosineEvenDistance
#check PaperFormalization.Manuscript.varianceCosineEvenDistances_nonempty
#print axioms PaperFormalization.Manuscript.varianceCosineEvenDistances_nonempty
#check PaperFormalization.Manuscript.varianceCosineEvenDistances_bddBelow
#print axioms PaperFormalization.Manuscript.varianceCosineEvenDistances_bddBelow
#check PaperFormalization.Manuscript.varianceCosineEscapeLanding_iff_distance
#print axioms PaperFormalization.Manuscript.varianceCosineEscapeLanding_iff_distance
#check PaperFormalization.Manuscript.varianceCosineEscapeLanding_measurable
#print axioms PaperFormalization.Manuscript.varianceCosineEscapeLanding_measurable
#check PaperFormalization.Manuscript.varianceCosineEscapeLanding_bad_eq
#print axioms PaperFormalization.Manuscript.varianceCosineEscapeLanding_bad_eq
#check PaperFormalization.Manuscript.varianceCosine_nearest_even
#print axioms PaperFormalization.Manuscript.varianceCosine_nearest_even
#check PaperFormalization.Manuscript.varianceCosineEvenDistance_mem
#print axioms PaperFormalization.Manuscript.varianceCosineEvenDistance_mem
#check PaperFormalization.Manuscript.varianceCosineEscapeLanding_gap
#print axioms PaperFormalization.Manuscript.varianceCosineEscapeLanding_gap
#check PaperFormalization.Manuscript.varianceCosineMeanFlow_recovered_of_landing
#print axioms PaperFormalization.Manuscript.varianceCosineMeanFlow_recovered_of_landing
#check PaperFormalization.Manuscript.varianceCosineEscapeLanding_odd
#print axioms PaperFormalization.Manuscript.varianceCosineEscapeLanding_odd
#check PaperFormalization.Manuscript.varianceCosineEscapeLanding_not_even
#print axioms PaperFormalization.Manuscript.varianceCosineEscapeLanding_not_even
#check PaperFormalization.Manuscript.varianceCosineHessian
#print axioms PaperFormalization.Manuscript.varianceCosineHessian
#check PaperFormalization.Manuscript.varianceCosine_source_sampled_hessian
#print axioms PaperFormalization.Manuscript.varianceCosine_source_sampled_hessian
#check PaperFormalization.Manuscript.varianceCosineHessian_scalar_apply
#print axioms PaperFormalization.Manuscript.varianceCosineHessian_scalar_apply
#check PaperFormalization.Manuscript.varianceCosine_configuration_norm_sq
#print axioms PaperFormalization.Manuscript.varianceCosine_configuration_norm_sq
#check PaperFormalization.Manuscript.varianceCosineHessian_quadratic
#print axioms PaperFormalization.Manuscript.varianceCosineHessian_quadratic
#check PaperFormalization.Manuscript.varianceCosine_mean_direction_energy
#print axioms PaperFormalization.Manuscript.varianceCosine_mean_direction_energy
#check PaperFormalization.Manuscript.varianceCosineHessian_quadratic_lower
#print axioms PaperFormalization.Manuscript.varianceCosineHessian_quadratic_lower
#check PaperFormalization.Manuscript.varianceCosineHessian_rayleigh_le_parallel
#print axioms PaperFormalization.Manuscript.varianceCosineHessian_rayleigh_le_parallel
#check PaperFormalization.Manuscript.varianceCosine_centered_direction
#print axioms PaperFormalization.Manuscript.varianceCosine_centered_direction
#check PaperFormalization.Manuscript.varianceCosineHessian_rayleigh_le_centered
#print axioms PaperFormalization.Manuscript.varianceCosineHessian_rayleigh_le_centered
#check PaperFormalization.Manuscript.varianceCosineHessian_rayleigh
#print axioms PaperFormalization.Manuscript.varianceCosineHessian_rayleigh
#check PaperFormalization.Manuscript.varianceCosineHessian_rayleigh_one
#print axioms PaperFormalization.Manuscript.varianceCosineHessian_rayleigh_one
#check PaperFormalization.Manuscript.varianceCosineCurvature
#print axioms PaperFormalization.Manuscript.varianceCosineCurvature
#check PaperFormalization.Manuscript.varianceCosineRecoveryRate
#print axioms PaperFormalization.Manuscript.varianceCosineRecoveryRate
#check PaperFormalization.Manuscript.varianceCosineRecoveryRate_pos
#print axioms PaperFormalization.Manuscript.varianceCosineRecoveryRate_pos
#check PaperFormalization.Manuscript.varianceCosine_source_sampled_curvature
#print axioms PaperFormalization.Manuscript.varianceCosine_source_sampled_curvature
#check PaperFormalization.Manuscript.varianceCosine_population_sampled_curvature
#print axioms PaperFormalization.Manuscript.varianceCosine_population_sampled_curvature
#check PaperFormalization.Manuscript.varianceCosineCurvature_lower
#print axioms PaperFormalization.Manuscript.varianceCosineCurvature_lower
#check PaperFormalization.Manuscript.varianceCosineCurvature_abs
#print axioms PaperFormalization.Manuscript.varianceCosineCurvature_abs
#check PaperFormalization.Manuscript.varianceCosineCurvature_recovered
#print axioms PaperFormalization.Manuscript.varianceCosineCurvature_recovered
#check PaperFormalization.Manuscript.varianceCosineCurvature_continuous
#print axioms PaperFormalization.Manuscript.varianceCosineCurvature_continuous
#check PaperFormalization.Manuscript.varianceCosine_mean_curvature_recovered
#print axioms PaperFormalization.Manuscript.varianceCosine_mean_curvature_recovered
#check PaperFormalization.Manuscript.varianceCosineGaussian_pdf_mono
#print axioms PaperFormalization.Manuscript.varianceCosineGaussian_pdf_mono
#check PaperFormalization.Manuscript.varianceCosineGaussian_interval_upper
#print axioms PaperFormalization.Manuscript.varianceCosineGaussian_interval_upper
#check PaperFormalization.Manuscript.varianceCosineGaussian_interval_lower
#print axioms PaperFormalization.Manuscript.varianceCosineGaussian_interval_lower
#check PaperFormalization.Manuscript.varianceCosinePositiveLanding
#print axioms PaperFormalization.Manuscript.varianceCosinePositiveLanding
#check PaperFormalization.Manuscript.varianceCosineNegativeLanding
#print axioms PaperFormalization.Manuscript.varianceCosineNegativeLanding
#check PaperFormalization.Manuscript.varianceCosinePositiveReference
#print axioms PaperFormalization.Manuscript.varianceCosinePositiveReference
#check PaperFormalization.Manuscript.varianceCosineNegativeReference
#print axioms PaperFormalization.Manuscript.varianceCosineNegativeReference
#check PaperFormalization.Manuscript.varianceCosineGaussian_positive_interval
#print axioms PaperFormalization.Manuscript.varianceCosineGaussian_positive_interval
#check PaperFormalization.Manuscript.varianceCosineGaussian_negative_interval
#print axioms PaperFormalization.Manuscript.varianceCosineGaussian_negative_interval
#check PaperFormalization.Manuscript.varianceCosinePositiveReference_disjoint
#print axioms PaperFormalization.Manuscript.varianceCosinePositiveReference_disjoint
#check PaperFormalization.Manuscript.varianceCosineNegativeReference_disjoint
#print axioms PaperFormalization.Manuscript.varianceCosineNegativeReference_disjoint
#check PaperFormalization.Manuscript.varianceCosine_union_of_disjoint_dominators
#print axioms PaperFormalization.Manuscript.varianceCosine_union_of_disjoint_dominators
#check PaperFormalization.Manuscript.varianceCosineEscapeLanding_bad_cover
#print axioms PaperFormalization.Manuscript.varianceCosineEscapeLanding_bad_cover
#check PaperFormalization.Manuscript.varianceCosineEscapeConstant
#print axioms PaperFormalization.Manuscript.varianceCosineEscapeConstant
#check PaperFormalization.Manuscript.varianceCosineEscapeConstant_ge_four
#print axioms PaperFormalization.Manuscript.varianceCosineEscapeConstant_ge_four
#check PaperFormalization.Manuscript.varianceCosineGaussian_escape_failure
#print axioms PaperFormalization.Manuscript.varianceCosineGaussian_escape_failure
#check PaperFormalization.Manuscript.varianceCosineEscapeRadius
#print axioms PaperFormalization.Manuscript.varianceCosineEscapeRadius
#check PaperFormalization.Manuscript.varianceCosineEscapeRadius_bounds
#print axioms PaperFormalization.Manuscript.varianceCosineEscapeRadius_bounds
#check PaperFormalization.Manuscript.varianceCosineGaussian_escape_budget
#print axioms PaperFormalization.Manuscript.varianceCosineGaussian_escape_budget
#check PaperFormalization.Manuscript.varianceCosineEscapeEvent
#print axioms PaperFormalization.Manuscript.varianceCosineEscapeEvent
#check PaperFormalization.Manuscript.varianceCosineEscapeEvent_measurable
#print axioms PaperFormalization.Manuscript.varianceCosineEscapeEvent_measurable
#check PaperFormalization.Manuscript.varianceCosineCoupling_landing_law
#print axioms PaperFormalization.Manuscript.varianceCosineCoupling_landing_law
#check PaperFormalization.Manuscript.varianceCosineEscapeEvent_budget
#print axioms PaperFormalization.Manuscript.varianceCosineEscapeEvent_budget
#check PaperFormalization.Manuscript.recovery_energy_decay
#print axioms PaperFormalization.Manuscript.recovery_energy_decay
#check PaperFormalization.Manuscript.varianceCosinePopulationExcess
#print axioms PaperFormalization.Manuscript.varianceCosinePopulationExcess
#check PaperFormalization.Manuscript.varianceCosinePopulationExcessDeriv
#print axioms PaperFormalization.Manuscript.varianceCosinePopulationExcessDeriv
#check PaperFormalization.Manuscript.varianceCosinePopulationExcess_nonneg
#print axioms PaperFormalization.Manuscript.varianceCosinePopulationExcess_nonneg
#check PaperFormalization.Manuscript.varianceCosinePopulationExcess_hasDerivAt
#print axioms PaperFormalization.Manuscript.varianceCosinePopulationExcess_hasDerivAt
#check PaperFormalization.Manuscript.varianceCosinePopulationExcess_differential_bound
#print axioms PaperFormalization.Manuscript.varianceCosinePopulationExcess_differential_bound
#check PaperFormalization.Manuscript.varianceCosinePopulationExcess_uniform
#print axioms PaperFormalization.Manuscript.varianceCosinePopulationExcess_uniform
#check PaperFormalization.Manuscript.varianceCosineInitial_variance_bounds
#print axioms PaperFormalization.Manuscript.varianceCosineInitial_variance_bounds
#check PaperFormalization.Manuscript.varianceCosinePopulationExcess_eq_objective
#print axioms PaperFormalization.Manuscript.varianceCosinePopulationExcess_eq_objective
#check PaperFormalization.Manuscript.varianceCosinePopulation_objective_after_escape
#print axioms PaperFormalization.Manuscript.varianceCosinePopulation_objective_after_escape
#check PaperFormalization.Manuscript.recoveryContinuousResponse
#print axioms PaperFormalization.Manuscript.recoveryContinuousResponse
#check PaperFormalization.Manuscript.recoveryJumpResponse
#print axioms PaperFormalization.Manuscript.recoveryJumpResponse
#check PaperFormalization.Manuscript.recoveryContinuousResponse_nonneg
#print axioms PaperFormalization.Manuscript.recoveryContinuousResponse_nonneg
#check PaperFormalization.Manuscript.recoveryJumpResponse_nonneg
#print axioms PaperFormalization.Manuscript.recoveryJumpResponse_nonneg
#check PaperFormalization.Manuscript.recoveryJumpResponse_at_jump
#print axioms PaperFormalization.Manuscript.recoveryJumpResponse_at_jump
#check PaperFormalization.Manuscript.recovery_intervalIntegrable
#print axioms PaperFormalization.Manuscript.recovery_intervalIntegrable
#check PaperFormalization.Manuscript.recovery_propagator_le
#print axioms PaperFormalization.Manuscript.recovery_propagator_le
#check PaperFormalization.Manuscript.recovery_integral_exp
#print axioms PaperFormalization.Manuscript.recovery_integral_exp
#check PaperFormalization.Manuscript.recoveryContinuousResponse_early
#print axioms PaperFormalization.Manuscript.recoveryContinuousResponse_early
#check PaperFormalization.Manuscript.recovery_tail_integral
#print axioms PaperFormalization.Manuscript.recovery_tail_integral
#check PaperFormalization.Manuscript.recoveryContinuousResponse_split
#print axioms PaperFormalization.Manuscript.recoveryContinuousResponse_split
#check PaperFormalization.Manuscript.recoveryContinuousResponse_late
#print axioms PaperFormalization.Manuscript.recoveryContinuousResponse_late
#check PaperFormalization.Manuscript.recoveryJumpResponse_early
#print axioms PaperFormalization.Manuscript.recoveryJumpResponse_early
#check PaperFormalization.Manuscript.recoveryJumpResponse_late
#print axioms PaperFormalization.Manuscript.recoveryJumpResponse_late
#check PaperFormalization.Manuscript.varianceCosineRightMean
#print axioms PaperFormalization.Manuscript.varianceCosineRightMean
#check PaperFormalization.Manuscript.varianceCosineRightCurvature
#print axioms PaperFormalization.Manuscript.varianceCosineRightCurvature
#check PaperFormalization.Manuscript.varianceCosineRecoveryTime
#print axioms PaperFormalization.Manuscript.varianceCosineRecoveryTime
#check PaperFormalization.Manuscript.varianceCosineResponseConstant
#print axioms PaperFormalization.Manuscript.varianceCosineResponseConstant
#check PaperFormalization.Manuscript.varianceCosineRightMean_branch
#print axioms PaperFormalization.Manuscript.varianceCosineRightMean_branch
#check PaperFormalization.Manuscript.varianceCosineRightMean_measurable
#print axioms PaperFormalization.Manuscript.varianceCosineRightMean_measurable
#check PaperFormalization.Manuscript.varianceCosineRightCurvature_measurable
#print axioms PaperFormalization.Manuscript.varianceCosineRightCurvature_measurable
#check PaperFormalization.Manuscript.varianceCosineRightCurvature_integrable
#print axioms PaperFormalization.Manuscript.varianceCosineRightCurvature_integrable
#check PaperFormalization.Manuscript.varianceCosineRightCurvature_eq_sampled
#print axioms PaperFormalization.Manuscript.varianceCosineRightCurvature_eq_sampled
#check PaperFormalization.Manuscript.varianceCosineRightCurvature_recovered
#print axioms PaperFormalization.Manuscript.varianceCosineRightCurvature_recovered
#check PaperFormalization.Manuscript.varianceCosineRecoveryTime_exp
#print axioms PaperFormalization.Manuscript.varianceCosineRecoveryTime_exp
#check PaperFormalization.Manuscript.varianceCosine_responses_uniform
#print axioms PaperFormalization.Manuscript.varianceCosine_responses_uniform
#check PaperFormalization.Manuscript.varianceCosine_responses_late
#print axioms PaperFormalization.Manuscript.varianceCosine_responses_late
#check PaperFormalization.Manuscript.recovery_wait_bound
#print axioms PaperFormalization.Manuscript.recovery_wait_bound
#check PaperFormalization.Manuscript.varianceCosine_source_envelope_one_jump
#print axioms PaperFormalization.Manuscript.varianceCosine_source_envelope_one_jump
#check PaperFormalization.Manuscript.varianceCosineJumpSigma
#print axioms PaperFormalization.Manuscript.varianceCosineJumpSigma
#check PaperFormalization.Manuscript.varianceCosineLandingVariance
#print axioms PaperFormalization.Manuscript.varianceCosineLandingVariance
#check PaperFormalization.Manuscript.varianceCosinePostMeanY_landing
#print axioms PaperFormalization.Manuscript.varianceCosinePostMeanY_landing
#check PaperFormalization.Manuscript.varianceCosine_response_control
#print axioms PaperFormalization.Manuscript.varianceCosine_response_control
#check PaperFormalization.Manuscript.varianceCosineEscapeEvent_tower_budget
#print axioms PaperFormalization.Manuscript.varianceCosineEscapeEvent_tower_budget
#check PaperFormalization.Manuscript.varianceCosine_source_envelope_sup_bound
#print axioms PaperFormalization.Manuscript.varianceCosine_source_envelope_sup_bound
#check PaperFormalization.Manuscript.varianceCosine_rpow_nat
#print axioms PaperFormalization.Manuscript.varianceCosine_rpow_nat
#check PaperFormalization.Manuscript.varianceCosine_rate_exponents
#print axioms PaperFormalization.Manuscript.varianceCosine_rate_exponents
#check PaperFormalization.Manuscript.varianceCosine_stability_scale_algebra
#print axioms PaperFormalization.Manuscript.varianceCosine_stability_scale_algebra
#check PaperFormalization.Manuscript.varianceCosine_uniform_rate_algebra
#print axioms PaperFormalization.Manuscript.varianceCosine_uniform_rate_algebra
#check PaperFormalization.Manuscript.varianceCosine_late_rate_algebra
#print axioms PaperFormalization.Manuscript.varianceCosine_late_rate_algebra
#check PaperFormalization.Manuscript.varianceCosine_responses_after_wait
#print axioms PaperFormalization.Manuscript.varianceCosine_responses_after_wait
#check PaperFormalization.Manuscript.varianceCosine_energy_after_wait
#print axioms PaperFormalization.Manuscript.varianceCosine_energy_after_wait
#check PaperFormalization.Manuscript.varianceCosine_wait_logarithmic
#print axioms PaperFormalization.Manuscript.varianceCosine_wait_logarithmic
#check PaperFormalization.Manuscript.varianceCosine_same_event_budget
#print axioms PaperFormalization.Manuscript.varianceCosine_same_event_budget
