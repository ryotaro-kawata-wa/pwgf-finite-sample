import PaperFormalization.Manuscript.SourceRawGrowingTracking
import PaperFormalization.Manuscript.SourceGrowingUniformDecay

/-! Executed M13t diagnostics; see CODEX_HANDOFF_M13T.md for the receipt. Type/axiom queries are not proof placeholders. -/
open MeasureTheory Set Filter
open scoped Topology
open PaperFormalization.Manuscript

#check PaperFormalization.Manuscript.source_gamma_rate_at_fixed_radius
#print axioms PaperFormalization.Manuscript.source_gamma_rate_at_fixed_radius
#check PaperFormalization.Manuscript.exists_source_radius_before_all_exponents
#print axioms PaperFormalization.Manuscript.exists_source_radius_before_all_exponents
#check PaperFormalization.Manuscript.sourceAsymptoticXi
#print axioms PaperFormalization.Manuscript.sourceAsymptoticXi
#check PaperFormalization.Manuscript.sourceMainXi
#print axioms PaperFormalization.Manuscript.sourceMainXi
#check PaperFormalization.Manuscript.sourceRateRadius
#print axioms PaperFormalization.Manuscript.sourceRateRadius
#check PaperFormalization.Manuscript.sourceAsymptoticXi_formula
#print axioms PaperFormalization.Manuscript.sourceAsymptoticXi_formula
#check PaperFormalization.Manuscript.sourceAsymptoticXi_bounds
#print axioms PaperFormalization.Manuscript.sourceAsymptoticXi_bounds
#check PaperFormalization.Manuscript.sourceAsymptoticXi_main
#print axioms PaperFormalization.Manuscript.sourceAsymptoticXi_main
#check PaperFormalization.Manuscript.sourceAsymptoticXi_le_main
#print axioms PaperFormalization.Manuscript.sourceAsymptoticXi_le_main
#check PaperFormalization.Manuscript.sourceAsymptoticXi_covariance_scale
#print axioms PaperFormalization.Manuscript.sourceAsymptoticXi_covariance_scale
#check PaperFormalization.Manuscript.sourceRateRadius_one_le
#print axioms PaperFormalization.Manuscript.sourceRateRadius_one_le
#check PaperFormalization.Manuscript.sourceRadiusArgumentFactor
#print axioms PaperFormalization.Manuscript.sourceRadiusArgumentFactor
#check PaperFormalization.Manuscript.sourceRadiusCoefficientMinimum
#print axioms PaperFormalization.Manuscript.sourceRadiusCoefficientMinimum
#check PaperFormalization.Manuscript.source_radius_argument_bound
#print axioms PaperFormalization.Manuscript.source_radius_argument_bound
#check PaperFormalization.Manuscript.sourceRateRadius_admissible
#print axioms PaperFormalization.Manuscript.sourceRateRadius_admissible
#check PaperFormalization.Manuscript.source_one_add_log_rpow_le
#print axioms PaperFormalization.Manuscript.source_one_add_log_rpow_le
#check PaperFormalization.Manuscript.SourceRateRadiusAdmissible
#print axioms PaperFormalization.Manuscript.SourceRateRadiusAdmissible
#check PaperFormalization.Manuscript.exists_source_rate_radius
#print axioms PaperFormalization.Manuscript.exists_source_rate_radius
#check PaperFormalization.Manuscript.exists_source_final_coefficient_rates
#print axioms PaperFormalization.Manuscript.exists_source_final_coefficient_rates
#check PaperFormalization.Manuscript.source_objective_gap_le_discrepancy_and_residual
#print axioms PaperFormalization.Manuscript.source_objective_gap_le_discrepancy_and_residual
#check PaperFormalization.Manuscript.source_objective_tracking_lift
#print axioms PaperFormalization.Manuscript.source_objective_tracking_lift
#check PaperFormalization.Manuscript.sourceObjectiveError
#print axioms PaperFormalization.Manuscript.sourceObjectiveError
#check PaperFormalization.Manuscript.SourceObjectiveControl
#print axioms PaperFormalization.Manuscript.SourceObjectiveControl
#check PaperFormalization.Manuscript.SourceObjectiveTrackingConclusion
#print axioms PaperFormalization.Manuscript.SourceObjectiveTrackingConclusion
#check PaperFormalization.Manuscript.source_objective_conclusion_of_tracking
#print axioms PaperFormalization.Manuscript.source_objective_conclusion_of_tracking
#check PaperFormalization.Manuscript.source_objective_control_of_closed_labels
#print axioms PaperFormalization.Manuscript.source_objective_control_of_closed_labels
#check PaperFormalization.Manuscript.sourceRateContinuousResponse
#print axioms PaperFormalization.Manuscript.sourceRateContinuousResponse
#check PaperFormalization.Manuscript.sourceRateJumpResponse
#print axioms PaperFormalization.Manuscript.sourceRateJumpResponse
#check PaperFormalization.Manuscript.sourceAsymptoticProfile
#print axioms PaperFormalization.Manuscript.sourceAsymptoticProfile
#check PaperFormalization.Manuscript.SourceControlledResponse
#print axioms PaperFormalization.Manuscript.SourceControlledResponse
#check PaperFormalization.Manuscript.sourceRateContinuousResponse_nonneg
#print axioms PaperFormalization.Manuscript.sourceRateContinuousResponse_nonneg
#check PaperFormalization.Manuscript.sourceRateJumpResponse_nonneg
#print axioms PaperFormalization.Manuscript.sourceRateJumpResponse_nonneg
#check PaperFormalization.Manuscript.sourceAsymptoticProfile_nonneg
#print axioms PaperFormalization.Manuscript.sourceAsymptoticProfile_nonneg
#check PaperFormalization.Manuscript.sourcePointwiseDistanceConstant
#print axioms PaperFormalization.Manuscript.sourcePointwiseDistanceConstant
#check PaperFormalization.Manuscript.sourcePointwiseJointConstant
#print axioms PaperFormalization.Manuscript.sourcePointwiseJointConstant
#check PaperFormalization.Manuscript.source_pointwise_distance_rate
#print axioms PaperFormalization.Manuscript.source_pointwise_distance_rate
#check PaperFormalization.Manuscript.source_pointwise_joint_rate
#print axioms PaperFormalization.Manuscript.source_pointwise_joint_rate
#check PaperFormalization.Manuscript.sourceCorollaryTheta
#print axioms PaperFormalization.Manuscript.sourceCorollaryTheta
#check PaperFormalization.Manuscript.sourceCorollaryTheta_properties
#print axioms PaperFormalization.Manuscript.sourceCorollaryTheta_properties
#check PaperFormalization.Manuscript.SourceUniformRateClaim
#print axioms PaperFormalization.Manuscript.SourceUniformRateClaim
#check PaperFormalization.Manuscript.exists_source_uniform_corollary_rates
#print axioms PaperFormalization.Manuscript.exists_source_uniform_corollary_rates
#check PaperFormalization.Manuscript.sourceRateRadiusCoefficient
#print axioms PaperFormalization.Manuscript.sourceRateRadiusCoefficient
#check PaperFormalization.Manuscript.sourceRateRadiusCoefficient_admissible
#print axioms PaperFormalization.Manuscript.sourceRateRadiusCoefficient_admissible
#check PaperFormalization.Manuscript.sourceUniformRateData
#print axioms PaperFormalization.Manuscript.sourceUniformRateData
#check PaperFormalization.Manuscript.SourceJointRateConclusion
#print axioms PaperFormalization.Manuscript.SourceJointRateConclusion
#check PaperFormalization.Manuscript.sourceMainXi_polynomial_le
#print axioms PaperFormalization.Manuscript.sourceMainXi_polynomial_le
#check PaperFormalization.Manuscript.sourceRateJumpResponse_prefix_le
#print axioms PaperFormalization.Manuscript.sourceRateJumpResponse_prefix_le
#check PaperFormalization.Manuscript.sourceAsymptoticProfile_power_le
#print axioms PaperFormalization.Manuscript.sourceAsymptoticProfile_power_le
#check PaperFormalization.Manuscript.source_pointwise_main_rate_to_power
#print axioms PaperFormalization.Manuscript.source_pointwise_main_rate_to_power
#check PaperFormalization.Manuscript.source_uniform_error_sup_bound
#print axioms PaperFormalization.Manuscript.source_uniform_error_sup_bound
#check PaperFormalization.Manuscript.source_rate_power_tendsto_zero
#print axioms PaperFormalization.Manuscript.source_rate_power_tendsto_zero
#check PaperFormalization.Manuscript.source_joint_rate_uniform_power
#print axioms PaperFormalization.Manuscript.source_joint_rate_uniform_power
#check PaperFormalization.Manuscript.exists_source_scheduled_objective_tracking_event
#print axioms PaperFormalization.Manuscript.exists_source_scheduled_objective_tracking_event
#check PaperFormalization.Manuscript.exists_source_objective_tracking_for_raw_solution_branches
#print axioms PaperFormalization.Manuscript.exists_source_objective_tracking_for_raw_solution_branches
#check PaperFormalization.Manuscript.exists_source_raw_growing_tracking_event
#print axioms PaperFormalization.Manuscript.exists_source_raw_growing_tracking_event

/- 1. A constant objective is exactly equal at empirical and population moments. -/
example (mu : Measure (EuclideanSpace Real (Fin 0))) (X : SourceFiniteConfiguration 0 0) :
    sourceObjectiveError (fun _ => (0 : lp (fun _ : Nat => Real) 2)) (fun _ => (3 : Real)) mu X = 0 := by
  simp [sourceObjectiveError]

/- 2. A zero discrepancy still permits a NONZERO objective/Gamma bias. -/
example : (1 : Real) ≤ (5 : Real)*(0 : Real)+1 := by
  exact source_objective_tracking_lift 0 1 5 1 0 (by norm_num) (by norm_num) (by norm_num)

/- 3. Zero Lambda does not require division by Lambda. -/
example (r gap delta Ebound : Real) (hr : r ≤ Ebound) (hg : gap ≤ delta) : gap ≤ delta := by
  simpa only [zero_mul,zero_add] using source_objective_tracking_lift r gap 0 delta Ebound
    (by norm_num) hr (by simpa using hg)

/- 4. Radius selection is possible without a rate exponent. -/
example : ∃ CD : Real, SourceRateRadiusAdmissible 1 1 CD :=
  exists_source_rate_radius 1 1 (by norm_num)

/- 5. The smallness branch of the theta minimum can be active. -/
example : sourceCorollaryTheta 0 1 (1/8) (1/16) = (1/180 : Real) := by
  norm_num [sourceCorollaryTheta]

/- 6. Both exponent obligations are preserved. -/
example (epsilon : Real) (he : 0 < epsilon) :
    (3+5/2)*sourceCorollaryTheta 3 2 (1/16) epsilon ≤ epsilon ∧
    (5/4+2)*(3+5/2)*sourceCorollaryTheta 3 2 (1/16) epsilon ≤ (1/16 : Real)/2 :=
  (sourceCorollaryTheta_properties 3 2 (1/16) epsilon (by norm_num) (by norm_num) (by norm_num) he).2

/- 7. No jumps and zero speed still distinguish the two Xi scales by eight. -/
example (N : Nat) (T p : Real) : sourceAsymptoticXi N 0 T p 0 = 8*sourceMainXi N T p := by
  simpa using sourceAsymptoticXi_main N 0 T p 0

/- 8. Empty-N algebra is total; this does NOT extend the particle theorem to N=0. -/
example (T p : Real) : sourceMainXi 0 T p = 0 := by simp [sourceMainXi]

/- 9. Confidence-zero algebra is total, but stochastic theorems retain p>0. -/
example (N : Nat) (T : Real) : sourceMainXi N T 0 = 0 := by simp [sourceMainXi]

/- 10. Xi has the literal e, not an undocumented equivalent log scale. -/
example : sourceMainXi 1 0 1 = Real.exp 1 := by simp [sourceMainXi]

/- 11. Zero-horizon continuous response. -/
example (kappa : Real -> Real) : sourceRateContinuousResponse kappa 0 = 0 := by
  simp [sourceRateContinuousResponse]

/- 12. Empty jump response. -/
example (kappa : Real -> Real) (tau eta : Nat -> Real) (t : Real) :
    sourceRateJumpResponse kappa tau eta 0 t = 0 := by simp [sourceRateJumpResponse]

/- 13. Zero amplitudes, at every covariance rank. -/
example (kappa : Real -> Real) (tau : Nat -> Real) (J : Nat) (t : Real) :
    sourceRateJumpResponse kappa tau (fun _ => 0) J t = 0 := by simp [sourceRateJumpResponse]

/- 14. The constant term in the objective profile survives at T=0. -/
example (N : Nat) (kappa : Real -> Real) (tau eta : Nat -> Real) :
    sourceAsymptoticProfile N 0 0 kappa tau eta 0 = (Real.sqrt N)⁻¹ := by
  simp [sourceAsymptoticProfile,sourceRateContinuousResponse,sourceRateJumpResponse]

/- 15. Strict-prefix control never counts a future or current omitted jump. -/
example (kappa : Real -> Real) (tau eta : Nat -> Real) (J : Nat) (t : Real)
    (heta : ∀ i < J, 0 ≤ eta i) :
    sourceRateJumpResponse kappa tau eta 0 t ≤ sourceRateJumpResponse kappa tau eta J t :=
  sourceRateJumpResponse_prefix_le kappa tau eta 0 J t (Nat.zero_le J) heta

/- 16. A singleton horizon and empty schedule satisfy the zero response cap. -/
example (N : Nat) (upsilon : Real) (kappa : Real -> Real) (tau eta : Nat -> Real) :
    SourceControlledResponse N 0 0 upsilon 0 kappa tau eta := by
  constructor
  · intro t ht
    have he : t = 0 := le_antisymm ht.2 ht.1
    subst t
    simp [sourceRateContinuousResponse]
  · intro t ht
    simp [sourceRateJumpResponse]

/- 17. Theta is positive even for a non-integer requested exponent. -/
example (epsilon : Real) (he : 0 < epsilon) : 0 < sourceCorollaryTheta 0 1 (1/8) epsilon :=
  (sourceCorollaryTheta_properties 0 1 (1/8) epsilon (by norm_num) (by norm_num) (by norm_num) he).1

/- 18. Bounded real supremum on a singleton, with nonzero error. -/
example : BddAbove ((fun _ : Real => (2 : Real)) '' Icc 0 0) ∧
    sSup ((fun _ : Real => (2 : Real)) '' Icc 0 0) ≤ 2 :=
  source_uniform_error_sup_bound (fun _ => 2) 0 2 (by norm_num) (fun _ _ => le_rfl)

/- 19. Zero uniform error. -/
example (T : Real) (hT : 0 ≤ T) : BddAbove ((fun _ : Real => (0 : Real)) '' Icc 0 T) ∧
    sSup ((fun _ : Real => (0 : Real)) '' Icc 0 T) ≤ 0 :=
  source_uniform_error_sup_bound (fun _ => 0) T 0 hT (fun _ _ => le_rfl)

/- 20. A genuine negative-rate power tends to zero. -/
example : Tendsto (fun N : Nat => 3*(N : Real)^(-1/4+1/16+1/16 : Real)) atTop (nhds 0) :=
  source_rate_power_tendsto_zero 3 (1/16) (1/16) (by norm_num)

/- 21. The canonically selected radius satisfies both probability and clipping conditions. -/
example : SourceRateRadiusAdmissible 1 1 (sourceRateRadiusCoefficient 1 1 (by norm_num)) :=
  sourceRateRadiusCoefficient_admissible 1 1 (by norm_num)

/- 22. Radius at N=1 and T=0: purely algebraic admission, not p-range relaxation. -/
example : 1 ≤ sourceRateRadius 1 0 0 (1/2) 1 1 0 :=
  sourceRateRadius_one_le 1 0 0 (1/2) 1 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/- 23. The exact finite-schedule radius inequality at a singleton horizon. -/
example : 2*Real.exp 1*1*(1+Real.log (2*(2 : Real)*(2*((0 : Real)+1)+(0 : Real)*0/(Real.exp 1*1))/((1/2)/8)))^(1/(1 : Real)) ≤
    sourceRateRadius 2 0 0 (1/2) 1 (sourceRateRadiusCoefficient 1 1 (by norm_num)) 0 := by
  simpa only [Nat.cast_zero, Nat.cast_ofNat, NNReal.coe_zero] using
    sourceRateRadius_admissible 2 0 0 (1/2) 1 1 (sourceRateRadiusCoefficient 1 1 (by norm_num)) 0
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (sourceRateRadiusCoefficient_admissible 1 1 (by norm_num)).2.1

/- 24. Quantifier order: ONE radius works before EVERY positive exponent. -/
example : ∃ CD : Real, ∀ epsilon : Real, 0 < epsilon -> SourceRateRadiusAdmissible 1 1 CD := by
  obtain ⟨CD,hCD⟩ := exists_source_rate_radius 1 1 (by norm_num)
  exact ⟨CD,fun _ _ => hCD⟩
