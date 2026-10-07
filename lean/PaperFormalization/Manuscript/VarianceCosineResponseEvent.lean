import PaperFormalization.Manuscript.VarianceCosineResponseControl
import PaperFormalization.Manuscript.VarianceCosineComparisonAssumptions

/-! # Assemble the recovery lemma on the original probability model
M13v VERIFIED UNIT (full example application remains open). Only fixed model data, a bounded mean-zero initial law, and
a requested failure budget are inputs. The escape probability and response
bounds are outputs on the same explicitly population-measurable event.
This is not yet the growing-horizon tracking proposition: application of
the M13t path theorem and its residual asymptotics remains a separate step.
-/
open MeasureTheory ProbabilityTheory Set
namespace PaperFormalization.Manuscript

noncomputable def varianceCosineJumpSigma (a beta eta : Real) : Real :=
  eta*(a+varianceCosineCurvatureScale beta)
noncomputable def varianceCosineLandingVariance (a beta eta : Real) : NNReal :=
  ⟨(varianceCosineJumpSigma a beta eta)^2,sq_nonneg _⟩

theorem varianceCosinePostMeanY_landing (a beta eta Z : Real) :
    varianceCosinePostMeanY a beta eta Z = -varianceCosineJumpSigma a beta eta*Z := by
  unfold varianceCosinePostMeanY varianceCosineJumpSigma varianceCosineKernel varianceCosineCurvatureScale
  simp only [mul_zero,Real.cos_zero,mul_one]
  ring

/-- The entire response-control unit, before any intersection with a sample
concentration event. No independence after conditioning is used. -/
theorem varianceCosine_response_control {N : Nat}
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (R : Real) (hR : 0 <= R) (hU : ∀ᵐ u ∂ mu0, norm u <= R)
    (hm0 : varianceCosineMean mu0 = 0)
    (a beta tau eta T p : Real) (ha : 0 < a) (hb : 0 < beta)
    (htau : 0 <= tau) (heta : 0 < eta) (hp : 0 < p) (hp1 : p <= 1) :
    let sigma := varianceCosineJumpSigma a beta eta
    let rho := varianceCosineEscapeRadius (varianceCosineLandingVariance a beta eta) p
    let r := varianceCosineRecoveryTime beta tau rho
    let P := varianceCosineCouplingLaw (sourceInitialConfigurationLaw (N := N) mu0)
    let E := varianceCosineEscapeEvent (N := N) sigma rho
    MeasurableSet E ∧ P Eᶜ <= ENNReal.ofReal (p/2) ∧
    ∀ w ∈ E,
      (forall t, t ∈ Icc 0 T ->
        recoveryContinuousResponse (varianceCosineRightCurvature a beta tau eta T w.2.1) t+
        recoveryJumpResponse (varianceCosineRightCurvature a beta tau eta T w.2.1) tau eta t <=
          varianceCosineResponseConstant a beta tau eta/rho) ∧
      (forall t, t ∈ Icc r T ->
        let k := varianceCosineRightCurvature a beta tau eta T w.2.1
        let b := varianceCosineCurvatureScale beta
        let lam := varianceCosineRecoveryRate a beta
        recoveryContinuousResponse k t <= (2*Real.exp (b*tau)/(rho*b))*Real.exp (-lam*(t-r))+lam⁻¹ ∧
        recoveryJumpResponse k tau eta t <= (2*eta*Real.exp (b*tau)/rho)*Real.exp (-lam*(t-r))) ∧
      (forall t, t ∈ Icc r T ->
        let pop := varianceCosinePopulation mu0 (varianceCosineRightMean a beta tau eta T w.2.1 t) (Real.exp (-a*t))
        Integrable varianceCosineEncodedFeature pop ∧
        0 <= varianceCosineObjective a beta (∫ x, varianceCosineEncodedFeature x ∂ pop)+beta ∧
        varianceCosineObjective a beta (∫ x, varianceCosineEncodedFeature x ∂ pop)+beta <=
          (a/2*R^2+2*beta)*Real.exp (-2*varianceCosineRecoveryRate a beta*(t-r))) := by
  let sigma := varianceCosineJumpSigma a beta eta
  let v := varianceCosineLandingVariance a beta eta
  let rho := varianceCosineEscapeRadius v p
  let r := varianceCosineRecoveryTime beta tau rho
  have hbscale := varianceCosineCurvatureScale_pos hb
  have hs : 0 < sigma := by dsimp [sigma,varianceCosineJumpSigma]; positivity
  have hr := varianceCosineEscapeRadius_bounds v p hp hp1
  have hr1 : rho <= 1 := by linarith [hr.2]
  refine ⟨varianceCosineEscapeEvent_measurable sigma rho,
    varianceCosineEscapeEvent_budget (sourceInitialConfigurationLaw (N := N) mu0) sigma p hs hp hp1,?_⟩
  intro w hw
  have hland : varianceCosineEscapeLanding rho (varianceCosinePostMeanY a beta eta w.2.1) := by
    rw [varianceCosinePostMeanY_landing]
    exact hw
  refine ⟨(fun t ht => varianceCosine_responses_uniform a beta tau eta T w.2.1 rho
    ha hb htau heta.le hr.1 hr1 hland t ht),
    (fun t ht => varianceCosine_responses_late a beta tau eta T w.2.1 rho t
      ha hb htau heta.le hr.1 hr1 hland ht),?_⟩
  intro t ht
  let m := fun u => varianceCosineMeanFlow beta T (varianceCosinePostMeanY a beta eta w.2.1) (u-tau)
  have hdelay := varianceCosineRecoveryDelay_nonneg _ rho (varianceCosineCurvatureScale_pos hb) hr.1 hr1
  have htaut : tau <= t := by dsimp [r,varianceCosineRecoveryTime] at ht; linarith [ht.1]
  have hmean : varianceCosineRightMean a beta tau eta T w.2.1 t = m t := by
    simp [varianceCosineRightMean,m,not_lt.mpr htaut]
  have hobj := varianceCosinePopulationExcess_eq_objective mu0 R hR hU hm0 a beta m t
  have hbound := varianceCosinePopulation_objective_after_escape mu0 R hR hU hm0
    a beta tau eta T w.2.1 rho t ha hb htau hr.1 hr1 hland ht.1 ht.2
  rw [hmean]
  exact ⟨hobj.1,by rw [hobj.2]; exact hbound.1,by rw [hobj.2]; exact hbound.2⟩

/-- This event has the same probability on the exact auxiliary tower used
by the existing final source theorem, not a newly substituted model. -/
theorem varianceCosineEscapeEvent_tower_budget {N : Nat}
    (mu : Measure (SourceFiniteConfiguration N 1)) [IsProbabilityMeasure mu]
    (sigma p : Real) (hs : 0 < sigma) (hp : 0 < p) (hp1 : p <= 1) :
    let v : NNReal := ⟨sigma^2,sq_nonneg sigma⟩
    let E := varianceCosineEscapeEvent (N := N) sigma (varianceCosineEscapeRadius v p)
    (sourceAuxiliaryMeasure (mu.prod (gaussianReal 0 1)) (stdGaussian (SourceStepNormal N 1)) 1)
      (varianceCosineTowerCoordinates ⁻¹' E)ᶜ <= ENNReal.ofReal (p/2) := by
  let v : NNReal := ⟨sigma^2,sq_nonneg sigma⟩
  let E := varianceCosineEscapeEvent (N := N) sigma (varianceCosineEscapeRadius v p)
  have hm := varianceCosineEscapeEvent_measurable (N := N) sigma (varianceCosineEscapeRadius v p)
  have hpres := varianceCosineTower_preserving mu
  have h := congrArg (fun m : Measure (VarianceCosineCouplingSpace N) => m Eᶜ) hpres.map_eq
  rw [Measure.map_apply hpres.measurable hm.compl] at h
  rw [preimage_compl] at h
  exact h.trans_le (varianceCosineEscapeEvent_budget mu sigma p hs hp hp1)

/-- Genuine supremum bound for the existing source forcing. Its nonempty
value set is exhibited before applying the real least-upper-bound property. -/
theorem varianceCosine_source_envelope_sup_bound (a beta tau eta T Z rho delta deltaTilde A : Real)
    (ha : 0 < a) (hb : 0 < beta) (htau : 0 <= tau) (heta : 0 <= eta) (hT : 0 <= T)
    (hr : 0 < rho) (hr1 : rho <= 1) (hd : 0 <= delta) (hA : 0 <= A)
    (hland : varianceCosineEscapeLanding rho (varianceCosinePostMeanY a beta eta Z)) :
    sourceCurvatureEnvelopeSup (varianceCosineRightCurvature a beta tau eta T Z)
      (varianceCosineTimes tau) (varianceCosineAmplitudes eta) delta deltaTilde A 1 T <=
      (delta+A*(Real.sqrt delta+Real.sqrt deltaTilde))*varianceCosineResponseConstant a beta tau eta/rho := by
  let k := varianceCosineRightCurvature a beta tau eta T Z
  let S := A*(Real.sqrt delta+Real.sqrt deltaTilde)
  have hS : 0 <= S := by dsimp [S]; positivity
  rw [sourceCurvatureEnvelopeSup_eq_sSup]
  apply csSup_le
  . exact ⟨_,0,⟨le_rfl,hT⟩,rfl⟩
  . rintro y ⟨t,ht,rfl⟩
    rw [varianceCosine_source_envelope_one_jump]
    have hC := recoveryContinuousResponse_nonneg k t ht.1
    have hJ := recoveryJumpResponse_nonneg k tau eta t heta
    have h := varianceCosine_responses_uniform a beta tau eta T Z rho ha hb htau heta hr hr1 hland t ht
    calc
      _ <= (delta+S)*(recoveryContinuousResponse k t+recoveryJumpResponse k tau eta t) := by
        have h1 := mul_nonneg hd hJ
        have h2 := mul_nonneg hS hC
        change delta*recoveryContinuousResponse k t+S*recoveryJumpResponse k tau eta t <= _
        nlinarith
      _ <= (delta+S)*(varianceCosineResponseConstant a beta tau eta/rho) :=
        mul_le_mul_of_nonneg_left h (add_nonneg hd hS)
      _ = _ := by ring
end PaperFormalization.Manuscript
