import PaperFormalization.Manuscript.VarianceCosineExampleScales

/-! # Original escape event at q_N and the exact response restrictions
M13w verified implementation; source correspondence and axiom audit passed. The model is never conditioned on this event.
The response bound supplied to M13T comes from the checked M13V source
application, not from a hypothesized curvature surrogate.
-/
open MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology
namespace PaperFormalization.Manuscript
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable def varianceCosineExampleEscape (P : VarianceCosineExampleParameters) (N : Nat) :
    Set (VarianceCosineCouplingSpace N) :=
  varianceCosineEscapeEvent P.sigma (varianceCosineExampleRadius P N)

theorem varianceCosineExampleEscape_measurable (P : VarianceCosineExampleParameters) (N : Nat) :
    MeasurableSet (varianceCosineExampleEscape P N) := varianceCosineEscapeEvent_measurable _ _

theorem varianceCosineExampleEscape_budget (P : VarianceCosineExampleParameters) (N : Nat)
    (hN : 0<N) (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0] :
    varianceCosineModelLaw N mu0 (varianceCosineExampleEscape P N)ᶜ <=
      ENNReal.ofReal (varianceCosineExampleFailure N/2) := by
  have hq := varianceCosineExampleFailure_bounds N hN
  exact varianceCosineEscapeEvent_budget (sourceInitialConfigurationLaw (N := N) mu0)
    P.sigma (varianceCosineExampleFailure N) P.sigma_pos hq.1 hq.2

theorem varianceCosineExample_land (P : VarianceCosineExampleParameters) (N : Nat)
    (w : VarianceCosineCouplingSpace N) (hw : w ∈ varianceCosineExampleEscape P N) :
    varianceCosineEscapeLanding (varianceCosineExampleRadius P N)
      (varianceCosinePostMeanY P.a P.beta P.eta w.2.1) := by
  rw [varianceCosinePostMeanY_landing]
  exact hw

theorem varianceCosineExampleRadius_bounds (P : VarianceCosineExampleParameters) (N : Nat) (hN : 0<N) :
    0<varianceCosineExampleRadius P N ∧ varianceCosineExampleRadius P N<=1/8 := by
  have hq := varianceCosineExampleFailure_bounds N hN
  exact varianceCosineEscapeRadius_bounds _ _ hq.1 hq.2

/-- No generic source forcing is replaced by a differently normalized jump. -/
theorem varianceCosineExample_jump_response (kappa : Real -> Real) (tau eta t : Real) :
    sourceRateJumpResponse kappa (varianceCosineTimes tau) (varianceCosineAmplitudes eta) 1 t =
      recoveryJumpResponse kappa tau eta t := by
  classical
  by_cases h : tau<=t
  . simp [sourceRateJumpResponse,recoveryJumpResponse,varianceCosineTimes,varianceCosineAmplitudes,h]
  . simp [sourceRateJumpResponse,recoveryJumpResponse,varianceCosineTimes,varianceCosineAmplitudes,h]

theorem varianceCosineExample_response_scale (P : VarianceCosineExampleParameters) (N : Nat) (hN : 0<N) :
    P.responseConstant/varianceCosineExampleRadius P N = P.wholeResponse*(N:Real)^(1/16:Real) := by
  have hn : (0:Real)<N := by exact_mod_cast hN
  have hd := P.escapeCoefficient_bounds.1
  have hnq := Real.rpow_pos_of_pos hn (1/16:Real)
  rw [varianceCosineExampleRadius_formula,Real.rpow_neg hn.le]
  unfold VarianceCosineExampleParameters.wholeResponse
  field_simp

theorem varianceCosineExample_responses_uniform (P : VarianceCosineExampleParameters) (N : Nat)
    (hN : 0<N) (w : VarianceCosineCouplingSpace N) (hw : w ∈ varianceCosineExampleEscape P N)
    (t : Real) (ht : t ∈ Icc 0 (varianceCosineExampleHorizon N)) :
    let kappa := varianceCosineRightCurvature P.a P.beta P.tau P.eta (varianceCosineExampleHorizon N) w.2.1
    sourceRateContinuousResponse kappa t+
      sourceRateJumpResponse kappa (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta) 1 t <=
        P.wholeResponse*(N:Real)^(1/16:Real) := by
  dsimp only
  have hr := varianceCosineExampleRadius_bounds P N hN
  have h := varianceCosine_responses_uniform P.a P.beta P.tau P.eta (varianceCosineExampleHorizon N)
    w.2.1 (varianceCosineExampleRadius P N) P.a_pos P.beta_pos P.tau_pos.le P.eta_pos.le
    hr.1 (by linarith [hr.2]) (varianceCosineExample_land P N w hw) t ht
  rw [varianceCosineExample_jump_response]
  rw [← varianceCosineExample_response_scale P N hN]
  exact h

theorem varianceCosineExample_controlled_response (P : VarianceCosineExampleParameters) (N : Nat)
    (hN : 0<N) (w : VarianceCosineCouplingSpace N) (hw : w ∈ varianceCosineExampleEscape P N) :
    SourceControlledResponse N 1 (varianceCosineExampleHorizon N) (1/16) P.controlledConstant
      (varianceCosineRightCurvature P.a P.beta P.tau P.eta (varianceCosineExampleHorizon N) w.2.1)
      (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta) := by
  let kappa := varianceCosineRightCurvature P.a P.beta P.tau P.eta (varianceCosineExampleHorizon N) w.2.1
  have hT : 0<=varianceCosineExampleHorizon N := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hh (t : Real) (ht : t ∈ Icc 0 (varianceCosineExampleHorizon N)) :=
    varianceCosineExample_responses_uniform P N hN w hw t ht
  have hc0 (t : Real) (ht : 0<=t) := sourceRateContinuousResponse_nonneg kappa t ht
  have hj0 (t : Real) : 0<=sourceRateJumpResponse kappa (varianceCosineTimes P.tau)
      (varianceCosineAmplitudes P.eta) 1 t := by
    apply sourceRateJumpResponse_nonneg
    intro i hi
    have he : i=0 := by omega
    subst i
    exact P.eta_pos.le
  have hcoeff := mul_le_mul_of_nonneg_right P.wholeResponse_le_controlledConstant
    (Real.rpow_nonneg (Nat.cast_nonneg N) (1/16:Real))
  constructor
  . intro t ht
    have hc : sourceRateContinuousResponse kappa t <= P.controlledConstant*(N:Real)^(1/16:Real) := by
      linarith [hh t ht,hj0 t]
    exact hc.trans (by
      have hh0 : 0<=P.controlledConstant*(N:Real)^(1/16:Real) := by have := P.controlledConstant_pos; positivity
      nlinarith [mul_nonneg hh0 hT])
  . intro t ht
    linarith [hh t ht,hc0 t ht.1]

/-- Actual smallness on the concrete escape event, with original residuals. -/
theorem varianceCosineExample_stable_on_escape (P : VarianceCosineExampleParameters) (N : Nat)
    (hN : 0<N) (hconf : (N:Real)^(-1:Real)<=varianceCosineExampleConfidence N)
    (w : VarianceCosineCouplingSpace N) (hw : w ∈ varianceCosineExampleEscape P N)
    (epsilon : Real) (he : 0<epsilon) (hcut : (P.rateData epsilon he).val.2<=N) :
    SourceTrackingSmallness
      (varianceCosineRightCurvature P.a P.beta P.tau P.eta (varianceCosineExampleHorizon N) w.2.1)
      (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta) 1 (varianceCosineExampleHorizon N)
      (varianceCosineExampleDelta P N) (varianceCosineExampleDeltaTilde P N)
      (varianceCosineExampleA P N) (varianceCosineExampleCD P N) :=
  varianceCosineExample_smallness_of_response P N hN hconf _
    (varianceCosineExample_controlled_response P N hN w hw) epsilon he hcut

/-- The full waiting threshold is an affine function of log(N). -/
theorem varianceCosineExample_wait_identity (P : VarianceCosineExampleParameters) (N : Nat) (hN : 0<N) :
    varianceCosineRecoveryTime P.beta P.tau (varianceCosineExampleRadius P N)+
      Real.log ((varianceCosineExampleRadius P N*(N:Real)^(-(1/4:Real)))⁻¹)/P.lam =
      P.waitIntercept+P.waitSlope*Real.log (N:Real) := by
  have hn : (0:Real)<N := by exact_mod_cast hN
  rw [varianceCosineExampleRadius_formula]
  simpa only [varianceCosineRecoveryTime,varianceCosineRecoveryDelay,
    VarianceCosineExampleParameters.b,VarianceCosineExampleParameters.waitIntercept,
    VarianceCosineExampleParameters.waitSlope] using
    varianceCosine_wait_logarithmic (N:Real) P.escapeCoefficient P.b P.lam P.tau hn
      P.escapeCoefficient_bounds.1 P.b_pos.ne' P.lam_pos.ne'

theorem varianceCosineExample_wait_le_log (P : VarianceCosineExampleParameters) (N : Nat) (hN : 2<=N) :
    varianceCosineRecoveryTime P.beta P.tau (varianceCosineExampleRadius P N)+
      Real.log ((varianceCosineExampleRadius P N*(N:Real)^(-(1/4:Real)))⁻¹)/P.lam <=
      P.waitConstant*Real.log (N:Real) := by
  have hn2 : (2:Real)<=N := by exact_mod_cast hN
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2<=Real.log (N:Real) := Real.log_le_log (by norm_num) hn2
  have hlogN : 0<=Real.log (N:Real) := by linarith
  have hA : P.waitIntercept<=abs P.waitIntercept/Real.log 2*Real.log (N:Real) := by
    have h := mul_le_mul_of_nonneg_left hlog (div_nonneg (abs_nonneg P.waitIntercept) hlog2.le)
    rw [div_mul_cancel₀ _ hlog2.ne'] at h
    exact (le_abs_self _).trans h
  have hB := mul_le_mul_of_nonneg_right (le_abs_self P.waitSlope) hlogN
  rw [varianceCosineExample_wait_identity P N (by omega)]
  unfold VarianceCosineExampleParameters.waitConstant
  nlinarith

/-- The logarithmic window lies after recovery, not merely after the jump. -/
theorem varianceCosineExample_log_after_recovery (P : VarianceCosineExampleParameters) (N : Nat) (hN : 2<=N) :
    varianceCosineRecoveryTime P.beta P.tau (varianceCosineExampleRadius P N) <=
      P.waitConstant*Real.log (N:Real) := by
  have hn : (1:Real)<=N := by exact_mod_cast (by omega : 1<=N)
  have hr := varianceCosineExampleRadius_bounds P N (by omega)
  have hv : 0<(N:Real)^(-(1/4:Real)) := Real.rpow_pos_of_pos (by linarith) _
  have hv1 := Real.rpow_le_one_of_one_le_of_nonpos hn (by norm_num : -(1/4:Real)<=0)
  have hprod : varianceCosineExampleRadius P N*(N:Real)^(-(1/4:Real))<=1 := by
    nlinarith [mul_le_mul_of_nonneg_left hv1 hr.1.le]
  have hlog : 0<=Real.log ((varianceCosineExampleRadius P N*(N:Real)^(-(1/4:Real)))⁻¹) := by
    rw [Real.log_inv]
    exact neg_nonneg.mpr (Real.log_nonpos (mul_pos hr.1 hv).le hprod)
  have hdiv := div_nonneg hlog P.lam_pos.le
  linarith [varianceCosineExample_wait_le_log P N hN]

theorem varianceCosineExample_responses_late (P : VarianceCosineExampleParameters) (N : Nat)
    (hN : 2<=N) (w : VarianceCosineCouplingSpace N) (hw : w ∈ varianceCosineExampleEscape P N)
    (t : Real) (ht : t ∈ Icc (P.waitConstant*Real.log (N:Real)) (varianceCosineExampleHorizon N)) :
    let kappa := varianceCosineRightCurvature P.a P.beta P.tau P.eta (varianceCosineExampleHorizon N) w.2.1
    sourceRateContinuousResponse kappa t <= P.lateContinuous ∧
      sourceRateJumpResponse kappa (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta) 1 t <=
        P.lateJump*(N:Real)^(-(1/4:Real)) := by
  dsimp only
  have hn : (1:Real)<=N := by exact_mod_cast (by omega : 1<=N)
  have hr := varianceCosineExampleRadius_bounds P N (by omega)
  have hv := Real.rpow_pos_of_pos (show (0:Real)<N by linarith) (-(1/4:Real))
  have hv1 := Real.rpow_le_one_of_one_le_of_nonpos hn (by norm_num : -(1/4:Real)<=0)
  have hlate := varianceCosine_responses_after_wait P.a P.beta P.tau P.eta (varianceCosineExampleHorizon N)
    w.2.1 (varianceCosineExampleRadius P N) ((N:Real)^(-(1/4:Real))) t
    P.a_pos P.beta_pos P.tau_pos.le P.eta_pos.le hr.1 (by linarith [hr.2]) hv hv1
    (varianceCosineExample_land P N w hw)
    ⟨ (varianceCosineExample_log_after_recovery P N hN).trans ht.1,ht.2 ⟩
    ((varianceCosineExample_wait_le_log P N hN).trans ht.1)
  rw [varianceCosineExample_jump_response]
  exact hlate

/-- Genuine population objective on the same event; no new loss is allocated. -/
theorem varianceCosineExample_population_late (P : VarianceCosineExampleParameters) (N : Nat)
    (hN : 2<=N) (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius) (hm : varianceCosineMean mu0=0)
    (w : VarianceCosineCouplingSpace N) (hw : w ∈ varianceCosineExampleEscape P N)
    (t : Real) (ht : t ∈ Icc (P.waitConstant*Real.log (N:Real)) (varianceCosineExampleHorizon N)) :
    let pop := varianceCosineExamplePopulation P mu0 (varianceCosineExampleHorizon N) w t
    Integrable varianceCosineEncodedFeature pop ∧
      0<=varianceCosineObjective P.a P.beta (integral pop varianceCosineEncodedFeature)+P.beta ∧
      varianceCosineObjective P.a P.beta (integral pop varianceCosineEncodedFeature)+P.beta <=
        P.populationExcessConstant*(N:Real)^(-(1/2:Real)) := by
  have hq := varianceCosineExampleFailure_bounds N (by omega)
  have hr := varianceCosineExampleRadius_bounds P N (by omega)
  have hresponse := varianceCosine_response_control (N := N) mu0 P.radius P.radius_nonneg hU hm
    P.a P.beta P.tau P.eta (varianceCosineExampleHorizon N) (varianceCosineExampleFailure N)
    P.a_pos P.beta_pos P.tau_pos.le P.eta_pos hq.1 hq.2
  have ho := (hresponse.2.2 w hw).2.2 t
    ⟨ (varianceCosineExample_log_after_recovery P N hN).trans ht.1,ht.2 ⟩
  refine ⟨ ho.1,ho.2.1,?_ ⟩
  have hn : (0:Real)<N := by exact_mod_cast (by omega : 0<N)
  have hv := Real.rpow_pos_of_pos hn (-(1/4:Real))
  have he := varianceCosine_energy_after_wait P.lam
    (varianceCosineRecoveryTime P.beta P.tau (varianceCosineExampleRadius P N))
    (varianceCosineExampleRadius P N) ((N:Real)^(-(1/4:Real))) t _ P.populationExcessConstant
    P.lam_pos hr.1 (by linarith [hr.2]) hv P.populationExcessConstant_nonneg
    ((varianceCosineExample_wait_le_log P N hN).trans ht.1) ho.2.2
  have hpow : ((N:Real)^(-(1/4:Real)))^2=(N:Real)^(-(1/2:Real)) := by
    rw [pow_two,<- Real.rpow_add hn]
    norm_num
  simpa only [hpow,varianceCosineExamplePopulation] using he

end PaperFormalization.Manuscript
