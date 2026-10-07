import PaperFormalization.Manuscript.VarianceCosineGaussianEscape
import PaperFormalization.Manuscript.VarianceCosinePopulationDecay
import PaperFormalization.Manuscript.CurvatureRecoveryResponse
import PaperFormalization.Manuscript.VarianceCosineSourceRealization

/-! # Source curvature and its two response integrals on the same escape event
M13v VERIFIED UNIT (full example application remains open). These are the original right-continuous population mean,
sampled Hessian and source propagator, not freely supplied comparison data.
The early case covers horizons shorter than the recovery time. The late
case uses the same event and includes both the jump time and terminal time.
-/
open Set MeasureTheory ProbabilityTheory
namespace PaperFormalization.Manuscript
open Continuous

noncomputable def varianceCosineRightMean (a beta tau eta T Z t : Real) : Real :=
  if t<tau then 0 else varianceCosineMeanFlow beta T (varianceCosinePostMeanY a beta eta Z) (t-tau)
noncomputable def varianceCosineRightCurvature (a beta tau eta T Z t : Real) : Real :=
  varianceCosineCurvature a beta (varianceCosineRightMean a beta tau eta T Z t)
noncomputable def varianceCosineRecoveryTime (beta tau rho : Real) : Real :=
  tau+varianceCosineRecoveryDelay (varianceCosineCurvatureScale beta) rho
noncomputable def varianceCosineResponseConstant (a beta tau eta : Real) : Real :=
  2*Real.exp (varianceCosineCurvatureScale beta*tau)*
    ((varianceCosineCurvatureScale beta)⁻¹+eta)+(varianceCosineRecoveryRate a beta)⁻¹

/-- Both branch labels are identified, rather than discarding the left trace. -/
theorem varianceCosineRightMean_branch (a beta tau eta T Z t : Real) :
    varianceCosineRightMean a beta tau eta T Z t =
      varianceCosineBranchMeanY a beta tau eta T Z (if t<tau then 0 else 1) t := by
  unfold varianceCosineRightMean varianceCosineBranchMeanY
  split_ifs <;> simp_all

theorem varianceCosineRightMean_measurable (a beta tau eta T : Real) :
    Measurable (fun z : Real × Real => varianceCosineRightMean a beta tau eta T z.1 z.2) := by
  have hflow := varianceCosineMeanFlow_measurable beta T
  unfold varianceCosineRightMean varianceCosinePostMeanY
  apply Measurable.ite (measurableSet_lt measurable_snd measurable_const) measurable_const
  exact hflow.comp (by fun_prop : Measurable (fun z : Real × Real =>
    (eta * varianceCosineKernel a beta 0 * z.1, z.2-tau)))

theorem varianceCosineRightCurvature_measurable (a beta tau eta T Z : Real) :
    Measurable (varianceCosineRightCurvature a beta tau eta T Z) :=
  (varianceCosineCurvature_continuous a beta).measurable.comp
    ((varianceCosineRightMean_measurable a beta tau eta T).comp (measurable_const.prodMk measurable_id))

/-- Bounded Borel curvature gives true integrability, even across the jump. -/
theorem varianceCosineRightCurvature_integrable (a beta tau eta T Z : Real)
    (ha : 0 <= a) (hb : 0 <= beta) :
    IntervalIntegrable (varianceCosineRightCurvature a beta tau eta T Z) volume 0 T := by
  letI : IsFiniteMeasure (volume.restrict (uIcc (0 : Real) T)) := by
    unfold uIcc
    infer_instance
  have hm := varianceCosineRightCurvature_measurable a beta tau eta T Z
  have hi : MemLp (varianceCosineRightCurvature a beta tau eta T Z) 1
      (volume.restrict (uIcc 0 T)) := MemLp.of_bound hm.stronglyMeasurable.aestronglyMeasurable
        (max a (varianceCosineCurvatureScale beta))
        (Filter.Eventually.of_forall (fun t => varianceCosineCurvature_abs a beta
          (varianceCosineRightMean a beta tau eta T Z t) ha hb))
  exact IntegrableOn.intervalIntegrable (hi.integrable (by norm_num))

/-- Equality with the sampled full source Hessian for every evaluation cloud. -/
theorem varianceCosineRightCurvature_eq_sampled {N : Nat} (hN : 2 <= N)
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (R : Real) (hR : 0 <= R) (hU : ∀ᵐ u ∂ mu0, norm u <= R)
    (hm0 : varianceCosineMean mu0 = 0) (a beta tau eta T Z t : Real)
    (Y : SourceFiniteConfiguration N 1) :
    rayleighInf (sampledMomentHessian varianceCosineEncodedFeature (varianceCosineObjective a beta)
      (∫ x, varianceCosineEncodedFeature x ∂ varianceCosinePopulation mu0
        (varianceCosineRightMean a beta tau eta T Z t) (Real.exp (-a*t))) Y) =
      varianceCosineRightCurvature a beta tau eta T Z t :=
  varianceCosine_population_sampled_curvature hN mu0 R hR hU hm0 a beta
    (varianceCosineRightMean a beta tau eta T Z t) (Real.exp (-a*t)) Y

theorem varianceCosineRightCurvature_recovered (a beta tau eta T Z rho : Real)
    (ha : 0 < a) (hb : 0 < beta) (htau : 0 <= tau)
    (hr : 0 < rho) (hr1 : rho <= 1)
    (hland : varianceCosineEscapeLanding rho (varianceCosinePostMeanY a beta eta Z))
    (t : Real) (ht : t ∈ Icc (varianceCosineRecoveryTime beta tau rho) T) :
    varianceCosineRecoveryRate a beta <= varianceCosineRightCurvature a beta tau eta T Z t := by
  have hd := varianceCosineRecoveryDelay_nonneg _ rho (varianceCosineCurvatureScale_pos hb) hr hr1
  have htaut : tau <= t := by dsimp [varianceCosineRecoveryTime] at ht; linarith [ht.1]
  unfold varianceCosineRightCurvature varianceCosineRightMean
  rw [if_neg (not_lt.mpr htaut)]
  apply varianceCosineCurvature_recovered a beta _ hb.le
  exact varianceCosineMeanFlow_recovered_of_landing beta T (varianceCosinePostMeanY a beta eta Z) rho (t-tau)
    hb hr hland (by constructor <;> linarith [ht.2])
    (by dsimp [varianceCosineRecoveryTime] at ht; linarith [ht.1])

/-- Literal exponential amplification at the printed recovery time. -/
theorem varianceCosineRecoveryTime_exp (beta tau rho : Real) (hb : 0 < beta) (hr : 0 < rho) :
    Real.exp (varianceCosineCurvatureScale beta*varianceCosineRecoveryTime beta tau rho) =
      2*Real.exp (varianceCosineCurvatureScale beta*tau)/rho := by
  have hb' := varianceCosineCurvatureScale_pos hb
  have he : varianceCosineCurvatureScale beta*varianceCosineRecoveryTime beta tau rho =
      varianceCosineCurvatureScale beta*tau+Real.log (2/rho) := by
    unfold varianceCosineRecoveryTime varianceCosineRecoveryDelay
    field_simp <;> ring
  rw [he,Real.exp_add,Real.exp_log (by positivity)]
  ring

/-- The full response sum at each horizon time has the same 1/rho bound. -/
theorem varianceCosine_responses_uniform (a beta tau eta T Z rho : Real)
    (ha : 0 < a) (hb : 0 < beta) (htau : 0 <= tau) (heta : 0 <= eta)
    (hr : 0 < rho) (hr1 : rho <= 1)
    (hland : varianceCosineEscapeLanding rho (varianceCosinePostMeanY a beta eta Z))
    (t : Real) (ht : t ∈ Icc 0 T) :
    recoveryContinuousResponse (varianceCosineRightCurvature a beta tau eta T Z) t+
      recoveryJumpResponse (varianceCosineRightCurvature a beta tau eta T Z) tau eta t <=
      varianceCosineResponseConstant a beta tau eta/rho := by
  let b := varianceCosineCurvatureScale beta
  let lam := varianceCosineRecoveryRate a beta
  let r := varianceCosineRecoveryTime beta tau rho
  let k := varianceCosineRightCurvature a beta tau eta T Z
  have hb' : 0 < b := varianceCosineCurvatureScale_pos hb
  have hl : 0 < lam := varianceCosineRecoveryRate_pos ha hb
  have hr0 : 0 <= r := by
    have h := varianceCosineRecoveryDelay_nonneg b rho hb' hr hr1
    dsimp [r,varianceCosineRecoveryTime]; linarith
  have htaur : tau <= r := by
    have h := varianceCosineRecoveryDelay_nonneg b rho hb' hr hr1
    dsimp [r,varianceCosineRecoveryTime]; linarith
  have hk := varianceCosineRightCurvature_integrable a beta tau eta T Z ha.le hb.le
  have hkt := recovery_intervalIntegrable k 0 t T hk le_rfl ht.1 ht.2
  have hlow (u : Real) (hu : u ∈ Icc 0 t) : -b <= k u :=
    varianceCosineCurvature_lower a beta _ ha.le hb.le
  have hrec (u : Real) (hu : u ∈ Icc r t) : lam <= k u :=
    varianceCosineRightCurvature_recovered a beta tau eta T Z rho ha hb htau hr hr1 hland u
      ⟨hu.1,hu.2.trans ht.2⟩
  have hbase : recoveryContinuousResponse k t+recoveryJumpResponse k tau eta t <=
      Real.exp (b*r)*(b⁻¹+eta)+lam⁻¹ := by
    by_cases htr : t <= r
    . have hc := recoveryContinuousResponse_early k b t hb' ht.1 hkt hlow
      have hj := recoveryJumpResponse_early k b tau eta r t hb'.le htau heta htr hkt hlow
      have hex : Real.exp (b*t) <= Real.exp (b*r) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htr hb'.le)
      have hc' := hc.trans (div_le_div_of_nonneg_right hex hb'.le)
      have hl0 : 0 <= lam⁻¹ := inv_nonneg.mpr hl.le
      rw [div_eq_mul_inv] at hc'
      nlinarith
    . have hrt := (le_of_not_ge htr)
      have hc := recoveryContinuousResponse_late k b lam r t hb' hl hr0 hrt hkt hlow hrec
      have hj := recoveryJumpResponse_late k b lam tau eta r t hb'.le hl htau heta htaur hrt hkt hlow hrec
      have hd : Real.exp (-lam*(t-r)) <= 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      have hd0 := (Real.exp_pos (-lam*(t-r))).le
      have hC0 : 0 <= Real.exp (b*r)/b := by positivity
      have hJ0 : 0 <= eta*Real.exp (b*r) := by positivity
      have h1 := mul_le_of_le_one_right hC0 hd
      have h2 := mul_le_of_le_one_right hJ0 hd
      rw [div_eq_mul_inv] at hc h1
      nlinarith
  have hex := varianceCosineRecoveryTime_exp beta tau rho hb hr
  have hlam : lam⁻¹ <= lam⁻¹/rho := by
    apply (le_div_iff₀ hr).mpr
    exact mul_le_of_le_one_right (inv_nonneg.mpr hl.le) hr1
  apply hbase.trans
  change Real.exp (b*r)*(b⁻¹+eta)+lam⁻¹ <= _
  rw [hex]
  unfold varianceCosineResponseConstant
  change _ <= (2*Real.exp (b*tau)*(b⁻¹+eta)+lam⁻¹)/rho
  calc
    _ <= (2*Real.exp (b*tau)/rho)*(b⁻¹+eta)+lam⁻¹/rho := add_le_add le_rfl hlam
    _ = _ := by ring

/-- The stronger late-time estimates retain the exponential transient. -/
theorem varianceCosine_responses_late (a beta tau eta T Z rho t : Real)
    (ha : 0 < a) (hb : 0 < beta) (htau : 0 <= tau) (heta : 0 <= eta)
    (hr : 0 < rho) (hr1 : rho <= 1)
    (hland : varianceCosineEscapeLanding rho (varianceCosinePostMeanY a beta eta Z))
    (ht : t ∈ Icc (varianceCosineRecoveryTime beta tau rho) T) :
    let b := varianceCosineCurvatureScale beta
    let lam := varianceCosineRecoveryRate a beta
    let r := varianceCosineRecoveryTime beta tau rho
    let k := varianceCosineRightCurvature a beta tau eta T Z
    recoveryContinuousResponse k t <= (2*Real.exp (b*tau)/(rho*b))*Real.exp (-lam*(t-r))+lam⁻¹ ∧
    recoveryJumpResponse k tau eta t <= (2*eta*Real.exp (b*tau)/rho)*Real.exp (-lam*(t-r)) := by
  let b := varianceCosineCurvatureScale beta
  let lam := varianceCosineRecoveryRate a beta
  let r := varianceCosineRecoveryTime beta tau rho
  let k := varianceCosineRightCurvature a beta tau eta T Z
  have hb' : 0 < b := varianceCosineCurvatureScale_pos hb
  have hl : 0 < lam := varianceCosineRecoveryRate_pos ha hb
  have hdelay := varianceCosineRecoveryDelay_nonneg b rho hb' hr hr1
  have htaur : tau <= r := by dsimp [r,varianceCosineRecoveryTime]; linarith
  have hr0 : 0 <= r := htau.trans htaur
  have hk := recovery_intervalIntegrable k 0 t T
    (varianceCosineRightCurvature_integrable a beta tau eta T Z ha.le hb.le) le_rfl (hr0.trans ht.1) ht.2
  have hlow (u : Real) (_hu : u ∈ Icc 0 t) : -b <= k u :=
    varianceCosineCurvature_lower a beta _ ha.le hb.le
  have hrec (u : Real) (hu : u ∈ Icc r t) : lam <= k u :=
    varianceCosineRightCurvature_recovered a beta tau eta T Z rho ha hb htau hr hr1 hland u
      ⟨hu.1,hu.2.trans ht.2⟩
  have hc := recoveryContinuousResponse_late k b lam r t hb' hl hr0 ht.1 hk hlow hrec
  have hj := recoveryJumpResponse_late k b lam tau eta r t hb'.le hl htau heta htaur ht.1 hk hlow hrec
  have hex := varianceCosineRecoveryTime_exp beta tau rho hb hr
  change Real.exp (b*r)=_ at hex
  rw [hex] at hc hj
  constructor
  . convert hc using 1 <;> ring
  . convert hj using 1 <;> ring

/-- Waiting long enough cancels exactly the 1/rho amplification. -/
theorem recovery_wait_bound (lam r rho v t : Real) (hl : 0 < lam) (hr : 0 < rho) (hv : 0 < v)
    (ht : r+Real.log ((rho*v)⁻¹)/lam <= t) :
    Real.exp (-lam*(t-r)) <= rho*v := by
  have h : Real.log ((rho*v)⁻¹) <= lam*(t-r) := by
    have hh : Real.log ((rho*v)⁻¹)/lam <= t-r := by linarith
    have hh' := (div_le_iff₀ hl).mp hh
    nlinarith
  have he := Real.exp_le_exp.mpr (neg_le_neg h)
  simpa only [neg_mul,Real.exp_neg,Real.exp_log (inv_pos.mpr (mul_pos hr hv)),inv_inv] using he

/-- The one-jump source forcing is exactly the pair of responses above. -/
theorem varianceCosine_source_envelope_one_jump (kappa : Real -> Real)
    (tau eta delta deltaTilde A t : Real) :
    sourceCurvatureEnvelope kappa (varianceCosineTimes tau) (varianceCosineAmplitudes eta)
      delta deltaTilde A 1 t =
      delta*recoveryContinuousResponse kappa t+
      A*(Real.sqrt delta+Real.sqrt deltaTilde)*recoveryJumpResponse kappa tau eta t := by
  classical
  unfold sourceCurvatureEnvelope recoveryContinuousResponse recoveryJumpResponse
  by_cases ht : tau <= t <;> simp [varianceCosineTimes,varianceCosineAmplitudes,ht] <;> ring
end PaperFormalization.Manuscript
