import PaperFormalization.Manuscript.VarianceCosineExampleFunctional
import PaperFormalization.Manuscript.SourceGrowingUniformDecay

/-! # Two displayed powers from the actual response-dependent M13T conclusion
M13w verified implementation; source correspondence and axiom audit passed. Generic adapters are applied to the source output,
not assumed for arbitrary data. The late profile keeps the decaying jump term.
-/
open MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology
namespace PaperFormalization.Manuscript
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

/-- M13T's general polynomial Xi bound suffices: epsilon/3 absorbs 9/4.
No event/radius is changed to perform this exponent conversion. -/
theorem varianceCosineExample_xi_power (N : Nat) (hN : 0<N)
    (hconf : (N:Real)^(-1:Real)<=varianceCosineExampleConfidence N)
    (epsilon : Real) (he : 0<epsilon) :
    (sourceMainXi N (varianceCosineExampleHorizon N) (varianceCosineExampleConfidence N))^
      (varianceCosineExampleExponent epsilon) <=
      (Real.exp 1+1)^(varianceCosineExampleExponent epsilon)*(N:Real)^epsilon := by
  have hn : (0:Real)<N := by exact_mod_cast hN
  have hn1 : (1:Real)<=N := by exact_mod_cast hN
  have hp := varianceCosineExampleConfidence_bounds N hN
  have hs := varianceCosineExampleExponent_pos epsilon he
  have hH : varianceCosineExampleHorizon N<=(N:Real)^(1/4-(1/16)-(1/16):Real) := by
    norm_num [varianceCosineExampleHorizon]
  have hx := sourceMainXi_polynomial_le N (varianceCosineExampleHorizon N)
    (varianceCosineExampleConfidence N) (1/16) (1/16) 1 hN hp.1 (by norm_num) (by norm_num) hH hconf
  have hx0 : 0<=sourceMainXi N (varianceCosineExampleHorizon N) (varianceCosineExampleConfidence N) := by
    unfold sourceMainXi varianceCosineExampleHorizon
    have hp0 := hp.1
    positivity
  have hh := Real.rpow_le_rpow hx0 hx hs.le
  rw [Real.mul_rpow (by positivity : 0<=Real.exp 1+1)
    (Real.rpow_nonneg hn.le _),<- Real.rpow_mul hn.le] at hh
  have hexp : (5/4+1)*varianceCosineExampleExponent epsilon<=epsilon := by
    unfold varianceCosineExampleExponent
    linarith
  exact hh.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hn1 hexp) (by positivity))

/-- Whole-time scalar bound, valid for the strict pre-jump prefix as well. -/
theorem varianceCosineExample_whole_power (P : VarianceCosineExampleParameters)
    (N : Nat) (hN : 0<N) (hconf : (N:Real)^(-1:Real)<=varianceCosineExampleConfidence N)
    (w : VarianceCosineCouplingSpace N) (hw : w ∈ varianceCosineExampleEscape P N)
    (epsilon : Real) (he : 0<epsilon) (K : Nat) (hK : K<=1) (t : Real)
    (ht : t ∈ Icc 0 (varianceCosineExampleHorizon N)) (r : Real)
    (hr : r <= (P.rateData (varianceCosineExampleExponent epsilon) (varianceCosineExampleExponent_pos epsilon he)).val.1*
      (sourceMainXi N (varianceCosineExampleHorizon N) (varianceCosineExampleConfidence N))^(varianceCosineExampleExponent epsilon)*
      sourceAsymptoticProfile N K (varianceCosineExampleHorizon N)
        (varianceCosineRightCurvature P.a P.beta P.tau P.eta (varianceCosineExampleHorizon N) w.2.1)
        (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta) t) :
    r <= varianceCosineExampleRateMultiplier P epsilon he*(2+6*P.controlledConstant)*
      (N:Real)^(-(3/16:Real)+epsilon) := by
  have hp := varianceCosineExampleConfidence_bounds N hN
  have hs := varianceCosineExampleExponent_pos epsilon he
  have hM := (P.rateData (varianceCosineExampleExponent epsilon) hs).property.1
  have hH : varianceCosineExampleHorizon N<=(N:Real)^(1/4-(1/16)-(1/16):Real) := by
    norm_num [varianceCosineExampleHorizon]
  have hEta : forall i : Nat, i<1 -> 0<=varianceCosineAmplitudes P.eta i := by
    intro i hi
    have heq : i=0 := by omega
    subst i
    exact P.eta_pos.le
  have hLoss : (5/4+1)*varianceCosineExampleExponent epsilon<=epsilon := by
    unfold varianceCosineExampleExponent; linarith
  have hh := source_pointwise_main_rate_to_power N 1 K (varianceCosineExampleHorizon N) t
    (varianceCosineExampleConfidence N) (1/16) (1/16) P.controlledConstant 1
    (P.rateData (varianceCosineExampleExponent epsilon) hs).val.1
    (varianceCosineExampleExponent epsilon) epsilon r
    (varianceCosineRightCurvature P.a P.beta P.tau P.eta (varianceCosineExampleHorizon N) w.2.1)
    (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta) hN hK
    (Real.rpow_nonneg (Nat.cast_nonneg N) _) ht (by norm_num) (by norm_num)
    P.controlledConstant_pos.le hM.le hs.le hH hp.1 hconf hLoss hEta
    (varianceCosineExample_controlled_response P N hN w hw) hr
  simpa only [varianceCosineExampleRateMultiplier,
    show (-1/4+(1/16):Real)=-(3/16:Real) by norm_num] using hh

/-- Unlike the coarse whole-time profile, this uses the recovered jump decay. -/
theorem varianceCosineExample_late_profile (P : VarianceCosineExampleParameters)
    (N : Nat) (hN : 2<=N) (w : VarianceCosineCouplingSpace N)
    (hw : w ∈ varianceCosineExampleEscape P N) (t : Real)
    (ht : t ∈ Icc (P.waitConstant*Real.log (N:Real)) (varianceCosineExampleHorizon N)) :
    sourceAsymptoticProfile N 1 (varianceCosineExampleHorizon N)
      (varianceCosineRightCurvature P.a P.beta P.tau P.eta (varianceCosineExampleHorizon N) w.2.1)
      (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta) t <=
      2*(1+P.lateContinuous+P.lateJump)*(N:Real)^(-(1/2:Real)) := by
  have hN0 : 0<N := by omega
  have hn : (0:Real)<N := by exact_mod_cast hN0
  have hH : varianceCosineExampleHorizon N<=(N:Real)^(1/4-(1/16)-(1/16):Real) := by
    norm_num [varianceCosineExampleHorizon]
  have hTs := source_growing_horizon_le_sqrt N (varianceCosineExampleHorizon N) (1/16) (1/16)
    hN0 (by norm_num) (by norm_num) hH
  obtain ⟨ ha,hb ⟩ := source_short_horizon_residual_rates N (varianceCosineExampleHorizon N) hN0 hTs
  have hb' : (N:Real)^(-1/4:Real)+Real.sqrt (varianceCosineExampleHorizon N/N) <=
      2*(N:Real)^(-(1/4:Real)) := by
    convert hb using 1 <;> norm_num
  have hlate := varianceCosineExample_responses_late P N hN w hw t ht
  let kappa := varianceCosineRightCurvature P.a P.beta P.tau P.eta (varianceCosineExampleHorizon N) w.2.1
  have hj0 : 0<=sourceRateJumpResponse kappa (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta) 1 t := by
    rw [varianceCosineExample_jump_response]
    exact recoveryJumpResponse_nonneg kappa P.tau P.eta t P.eta_pos.le
  have hlog : 0<=Real.log (N:Real) := Real.log_nonneg (by exact_mod_cast (by omega : 1<=N))
  have ht0 : 0<=t := (mul_nonneg P.waitConstant_pos.le hlog).trans ht.1
  have hc0 := sourceRateContinuousResponse_nonneg kappa t ht0
  have hprof : sourceAsymptoticProfile N 1 (varianceCosineExampleHorizon N) kappa
      (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta) t <=
      2*(Real.sqrt N)⁻¹*(1+P.lateContinuous)+
      2*(N:Real)^(-(1/4:Real))*(P.lateJump*(N:Real)^(-(1/4:Real))) := by
    unfold sourceAsymptoticProfile
    exact add_le_add (mul_le_mul ha (add_le_add le_rfl hlate.1) (by linarith) (by positivity))
      (mul_le_mul hb' hlate.2 hj0 (by positivity))
  have hhalf : (Real.sqrt N)⁻¹=(N:Real)^(-(1/2:Real)) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_neg hn.le]
  have hquarter : (N:Real)^(-(1/4:Real))*(N:Real)^(-(1/4:Real))=(N:Real)^(-(1/2:Real)) := by
    rw [<- Real.rpow_add hn]; norm_num
  calc
    _ <= _ := hprof
    _ = 2*(1+P.lateContinuous+P.lateJump)*(N:Real)^(-(1/2:Real)) := by
      rw [hhalf]
      calc
        _ = 2*(1+P.lateContinuous)*(N:Real)^(-(1/2:Real))+
            2*P.lateJump*((N:Real)^(-(1/4:Real))*(N:Real)^(-(1/4:Real))) := by ring
        _ = _ := by rw [hquarter]; ring

theorem varianceCosineExample_late_power (P : VarianceCosineExampleParameters)
    (N : Nat) (hN : 2<=N) (hconf : (N:Real)^(-1:Real)<=varianceCosineExampleConfidence N)
    (w : VarianceCosineCouplingSpace N) (hw : w ∈ varianceCosineExampleEscape P N)
    (epsilon : Real) (he : 0<epsilon) (t : Real)
    (ht : t ∈ Icc (P.waitConstant*Real.log (N:Real)) (varianceCosineExampleHorizon N)) (r : Real)
    (hr : r <= (P.rateData (varianceCosineExampleExponent epsilon) (varianceCosineExampleExponent_pos epsilon he)).val.1*
      (sourceMainXi N (varianceCosineExampleHorizon N) (varianceCosineExampleConfidence N))^(varianceCosineExampleExponent epsilon)*
      sourceAsymptoticProfile N 1 (varianceCosineExampleHorizon N)
        (varianceCosineRightCurvature P.a P.beta P.tau P.eta (varianceCosineExampleHorizon N) w.2.1)
        (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta) t) :
    r <= varianceCosineExampleRateMultiplier P epsilon he*2*(1+P.lateContinuous+P.lateJump)*
      (N:Real)^(-(1/2:Real)+epsilon) := by
  have hN0 : 0<N := by omega
  have hn : (0:Real)<N := by exact_mod_cast hN0
  have hxi := varianceCosineExample_xi_power N hN0 hconf epsilon he
  have hp := varianceCosineExample_late_profile P N hN w hw t ht
  have hM := (P.rateData (varianceCosineExampleExponent epsilon)
    (varianceCosineExampleExponent_pos epsilon he)).property.1
  have hlog : 0<=Real.log (N:Real) := Real.log_nonneg (by exact_mod_cast (by omega : 1<=N))
  have ht0 : 0<=t := (mul_nonneg P.waitConstant_pos.le hlog).trans ht.1
  have hprofile0 := sourceAsymptoticProfile_nonneg N 1 (varianceCosineExampleHorizon N) t
    (varianceCosineRightCurvature P.a P.beta P.tau P.eta (varianceCosineExampleHorizon N) w.2.1)
    (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta)
    (Real.rpow_nonneg hn.le _) ht0 (by
      intro i hi
      have hh : i=0 := by omega
      subst i
      exact P.eta_pos.le)
  have hmul := mul_le_mul (mul_le_mul_of_nonneg_left hxi hM.le) hp hprofile0 (by positivity)
  apply hr.trans (hmul.trans_eq _)
  unfold varianceCosineExampleRateMultiplier
  rw [show (N:Real)^(-(1/2:Real)+epsilon)=(N:Real)^epsilon*(N:Real)^(-(1/2:Real)) by
    rw [<- Real.rpow_add hn]; congr 1; ring]
  ring

/-- The sum in the manuscript, and the additional EMPIRICAL objective excess,
are derived from the same joint source bound. -/
theorem varianceCosineExample_rates_of_joint
    (P : VarianceCosineExampleParameters) (N : Nat) (hN : 2<=N)
    (hT : P.tau<=varianceCosineExampleHorizon N)
    (hconf : (N:Real)^(-1:Real)<=varianceCosineExampleConfidence N)
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius) (hm : varianceCosineMean mu0=0)
    (w : VarianceCosineCouplingSpace N) (hw : w ∈ varianceCosineExampleEscape P N)
    (epsilon : Real) (he : 0<epsilon)
    (hjoint : VarianceCosineExampleJointRate P mu0 (varianceCosineExampleHorizon N) w
      (varianceCosineExampleExponent epsilon)
      (P.rateData (varianceCosineExampleExponent epsilon) (varianceCosineExampleExponent_pos epsilon he)).val.1) :
    (forall t, t ∈ Icc 0 (varianceCosineExampleHorizon N) -> varianceCosineExampleError P mu0
      (varianceCosineExampleHorizon N) w t<=varianceCosineExampleRateConstant P epsilon he*(N:Real)^(-(3/16:Real)+epsilon)) ∧
    varianceCosineExamplePreError P mu0 (varianceCosineExampleHorizon N) w<=
      varianceCosineExampleRateConstant P epsilon he*(N:Real)^(-(3/16:Real)+epsilon) ∧
    (forall t, t ∈ Icc (P.waitConstant*Real.log (N:Real)) (varianceCosineExampleHorizon N) ->
      0<=varianceCosineEmpiricalExcess P (varianceCosineExamplePair P (varianceCosineExampleHorizon N) w t).1 ∧
      varianceCosineExampleLateError P mu0 (varianceCosineExampleHorizon N) w t<=
        varianceCosineExampleRateConstant P epsilon he*(N:Real)^(-(1/2:Real)+epsilon)) := by
  have hN0 : 0<N := by omega
  have hn : (0:Real)<N := by exact_mod_cast hN0
  have hn1 : (1:Real)<=N := by exact_mod_cast hN0
  let Q := varianceCosineExampleRateMultiplier P epsilon he
  have hQ : 0<Q := varianceCosineExampleRateMultiplier_pos P epsilon he
  have hCW : 2*Q*(2+6*P.controlledConstant)<=varianceCosineExampleRateConstant P epsilon he := by
    unfold varianceCosineExampleRateConstant
    have := P.lateContinuous_nonneg; have := P.lateJump_nonneg
    have := P.populationExcessConstant_nonneg
    have hh : 0<=6*Q*(1+P.lateContinuous+P.lateJump) := by positivity
    linarith
  have hCL : 6*Q*(1+P.lateContinuous+P.lateJump)+P.populationExcessConstant<=
      varianceCosineExampleRateConstant P epsilon he := by
    unfold varianceCosineExampleRateConstant
    have := P.controlledConstant_pos
    have hh : 0<=2*Q*(2+6*P.controlledConstant) := by positivity
    linarith
  constructor
  . intro t ht
    have hj := (hjoint.1 t ht).2
    have hp := varianceCosineExample_whole_power P N hN0 hconf w hw epsilon he 1 le_rfl t ht _ hj
    have hf := varianceCosine_functional_transfer P hN0 _
      (varianceCosineExamplePopulation_memLp P mu0 hU (varianceCosineExampleHorizon N) w t)
      (varianceCosineExamplePair P (varianceCosineExampleHorizon N) w t).1
      (varianceCosineExamplePair P (varianceCosineExampleHorizon N) w t).2
    have hc := mul_le_mul_of_nonneg_right hCW (Real.rpow_nonneg hn.le (-(3/16:Real)+epsilon))
    change varianceCosinePairFunctionalError P _ _ _<=_
    nlinarith [hf.2.1]
  constructor
  . have hp := varianceCosineExample_whole_power P N hN0 hconf w hw epsilon he 0 (by omega) P.tau
      ⟨ P.tau_pos.le,hT ⟩ _ hjoint.2.2
    have hf := varianceCosine_functional_transfer P hN0 (varianceCosineExamplePrePopulation P mu0)
      (varianceCosinePopulation_memLp mu0 P.radius P.radius_nonneg hU _ _)
      (varianceCosineModelBranches P.a P.beta P.tau P.eta (varianceCosineExampleHorizon N) w 0 P.tau).1
      (varianceCosineModelBranches P.a P.beta P.tau P.eta (varianceCosineExampleHorizon N) w 0 P.tau).2
    have hc := mul_le_mul_of_nonneg_right hCW (Real.rpow_nonneg hn.le (-(3/16:Real)+epsilon))
    change varianceCosinePairFunctionalError P _ _ _<=_
    nlinarith [hf.2.1]
  . intro t ht
    have hlog := Real.log_nonneg hn1
    have ht0 : 0<=t := (mul_nonneg P.waitConstant_pos.le hlog).trans ht.1
    have hp := varianceCosineExample_late_power P N hN hconf w hw epsilon he t ht _
      (hjoint.1 t ⟨ ht0,ht.2 ⟩).2
    have hf := varianceCosine_functional_transfer P hN0 _
      (varianceCosineExamplePopulation_memLp P mu0 hU (varianceCosineExampleHorizon N) w t)
      (varianceCosineExamplePair P (varianceCosineExampleHorizon N) w t).1
      (varianceCosineExamplePair P (varianceCosineExampleHorizon N) w t).2
    have he0 := (varianceCosineExample_population_late P N hN mu0 hU hm w hw t ht).2.2
    have he1 := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn1 (show -(1/2:Real)<=-(1/2:Real)+epsilon by linarith))
      P.populationExcessConstant_nonneg
    have hc := mul_le_mul_of_nonneg_right hCL (Real.rpow_nonneg hn.le (-(1/2:Real)+epsilon))
    refine ⟨ hf.1,?_ ⟩
    change varianceCosinePairFunctionalError P _ _ _+varianceCosineEmpiricalExcess P _<=_
    nlinarith [hf.2.2]

end PaperFormalization.Manuscript
