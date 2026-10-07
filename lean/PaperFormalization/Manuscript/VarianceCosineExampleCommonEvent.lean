import PaperFormalization.Manuscript.VarianceCosineExampleRateTransfer

/-! # One original-model event for every positive accuracy exponent
M13w verified implementation; source correspondence and axiom audit passed. The event is an intersection of the ACTUAL M13T
comparison event and the ACTUAL population escape event. Neither is conditioned
on the other. The selector and its admission threshold have no epsilon input.
This is the closing application, not a rate-assumption adapter.
-/
open MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology
namespace PaperFormalization.Manuscript
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

/-- The printed pointwise bounds, including the additional true left trace. -/
def VarianceCosineExamplePointwiseRates (P : VarianceCosineExampleParameters)
    (mu0 : Measure VarianceCosinePoint) (N : Nat) (w : VarianceCosineCouplingSpace N)
    (epsilon : Real) (he : 0<epsilon) : Prop :=
  (forall t, t ∈ Icc 0 (varianceCosineExampleHorizon N) ->
    varianceCosineExampleError P mu0 (varianceCosineExampleHorizon N) w t <=
      varianceCosineExampleRateConstant P epsilon he*(N:Real)^(-(3/16:Real)+epsilon)) ∧
  varianceCosineExamplePreError P mu0 (varianceCosineExampleHorizon N) w <=
    varianceCosineExampleRateConstant P epsilon he*(N:Real)^(-(3/16:Real)+epsilon) ∧
  (forall t, t ∈ Icc (P.waitConstant*Real.log (N:Real)) (varianceCosineExampleHorizon N) ->
    0<=varianceCosineEmpiricalExcess P (varianceCosineExamplePair P (varianceCosineExampleHorizon N) w t).1 ∧
    varianceCosineExampleLateError P mu0 (varianceCosineExampleHorizon N) w t <=
      varianceCosineExampleRateConstant P epsilon he*(N:Real)^(-(1/2:Real)+epsilon))

/-- The original smallness predicate, with actual residuals and actual radius. -/
def VarianceCosineExampleActualSmallness (P : VarianceCosineExampleParameters)
    (N : Nat) (w : VarianceCosineCouplingSpace N) : Prop :=
  SourceTrackingSmallness
    (varianceCosineRightCurvature P.a P.beta P.tau P.eta (varianceCosineExampleHorizon N) w.2.1)
    (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta) 1 (varianceCosineExampleHorizon N)
    (varianceCosineExampleDelta P N) (varianceCosineExampleDeltaTilde P N)
    (varianceCosineExampleA P N) (varianceCosineExampleCD P N)

/-- Exact union budget. The constant 49/64 is the sum of 17/64 and 1/2. -/
theorem varianceCosineExample_intersection_budget
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (Cmp Escape : Set Omega) (q : Real) (hq : 0<=q)
    (hc : mu Cmpᶜ<=ENNReal.ofReal (17*(q/2)/32))
    (he : mu Escapeᶜ<=ENNReal.ofReal (q/2)) :
    mu (Cmp ∩ Escape)ᶜ<=ENNReal.ofReal (49*q/64) := by
  rw [compl_inter]
  calc
    _ <= mu Cmpᶜ+mu Escapeᶜ := measure_union_le _ _
    _ <= ENNReal.ofReal (17*(q/2)/32)+ENNReal.ofReal (q/2) := add_le_add hc he
    _ = ENNReal.ofReal (49*q/64) := by
      rw [<- ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- Existence from primitive model parameters and the original initial law.
The accuracy exponent occurs strictly AFTER the event and its probability.
All residuals, source equations, canonical coordinates and response estimates
have been supplied by the preceding source applications. -/
theorem exists_varianceCosineExample_common_event
    (P : VarianceCosineExampleParameters) (N : Nat)
    (hN : varianceCosineExampleAdmission P<=N)
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius) (hm : varianceCosineMean mu0=0) :
    ∃ Good : Set (VarianceCosineCouplingSpace N),
      MeasurableSet Good ∧
      varianceCosineModelLaw N mu0 Goodᶜ<=ENNReal.ofReal (49*varianceCosineExampleFailure N/64) ∧
      forall w, w ∈ Good -> forall epsilon (he : 0<epsilon),
        varianceCosineExampleRateCutoff P epsilon he<=N ->
        VarianceCosineExampleActualSmallness P N w ∧
        VarianceCosineExamplePointwiseRates P mu0 N w epsilon he ∧
        VarianceCosineExampleTrackingConclusion P w := by
  obtain ⟨ hN2,hT,hconf,hwindow ⟩ := varianceCosineExample_admission_spec P N hN
  have hN0 : 0<N := by omega
  obtain ⟨ Cmp,hCmp,hCmpBudget,hCmpValid ⟩ :=
    exists_varianceCosineExample_comparison_event P N hN2 hT hconf mu0 hU hm
  let Escape := varianceCosineExampleEscape P N
  have hEscape := varianceCosineExampleEscape_measurable P N
  have hEscapeBudget := varianceCosineExampleEscape_budget P N hN0 mu0
  refine ⟨ Cmp ∩ Escape,hCmp.inter hEscape,?_,?_ ⟩
  . apply varianceCosineExample_intersection_budget
      (varianceCosineModelLaw N mu0) Cmp Escape (varianceCosineExampleFailure N)
      (varianceCosineExampleFailure_bounds N hN0).1.le
    . exact hCmpBudget
    . exact hEscapeBudget
  . intro w hw epsilon he hcut
    have hcutRate : (P.rateData (varianceCosineExampleExponent epsilon)
        (varianceCosineExampleExponent_pos epsilon he)).val.2<=N :=
      (le_max_right _ _).trans hcut
    have hResponse := varianceCosineExample_controlled_response P N hN0 w hw.2
    have hJoint := hCmpValid w hw.1 (varianceCosineExampleExponent epsilon)
      (varianceCosineExampleExponent_pos epsilon he) hcutRate hResponse
    refine ⟨ varianceCosineExample_stable_on_escape P N hN0 hconf w hw.2
      (varianceCosineExampleExponent epsilon) (varianceCosineExampleExponent_pos epsilon he) hcutRate,?_,hJoint.1 ⟩
    exact varianceCosineExample_rates_of_joint P N hN2 hT hconf mu0 hU hm w hw.2 epsilon he hJoint.2

/-- A concrete epsilon-independent choice. Small N are deliberately assigned
an empty event; only N above the displayed admission cutoff has a probability
claim. This avoids silently imposing a theorem outside its proved range. -/
noncomputable def varianceCosineExampleGood
    (P : VarianceCosineExampleParameters)
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius) (hm : varianceCosineMean mu0=0)
    (N : Nat) : Set (VarianceCosineCouplingSpace N) :=
  if hN : varianceCosineExampleAdmission P<=N then
    Classical.choose (exists_varianceCosineExample_common_event P N hN mu0 hU hm)
  else ∅

theorem varianceCosineExampleGood_measurable
    (P : VarianceCosineExampleParameters)
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius) (hm : varianceCosineMean mu0=0) (N : Nat) :
    MeasurableSet (varianceCosineExampleGood P mu0 hU hm N) := by
  classical
  unfold varianceCosineExampleGood
  split_ifs with hN
  . exact (Classical.choose_spec (exists_varianceCosineExample_common_event P N hN mu0 hU hm)).1
  . exact MeasurableSet.empty

theorem varianceCosineExampleGood_probability
    (P : VarianceCosineExampleParameters)
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius) (hm : varianceCosineMean mu0=0)
    (N : Nat) (hN : varianceCosineExampleAdmission P<=N) :
    varianceCosineModelLaw N mu0 (varianceCosineExampleGood P mu0 hU hm N)ᶜ<=
      ENNReal.ofReal (49*varianceCosineExampleFailure N/64) := by
  simpa only [varianceCosineExampleGood,dif_pos hN] using
    (Classical.choose_spec (exists_varianceCosineExample_common_event P N hN mu0 hU hm)).2.1

theorem varianceCosineExampleGood_rates
    (P : VarianceCosineExampleParameters)
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius) (hm : varianceCosineMean mu0=0)
    (N : Nat) (epsilon : Real) (he : 0<epsilon)
    (hN : varianceCosineExampleRateCutoff P epsilon he<=N)
    (w : VarianceCosineCouplingSpace N) (hw : w ∈ varianceCosineExampleGood P mu0 hU hm N) :
    VarianceCosineExampleActualSmallness P N w ∧
    VarianceCosineExamplePointwiseRates P mu0 N w epsilon he := by
  have hAdm : varianceCosineExampleAdmission P<=N := (le_max_left _ _).trans hN
  have hh := (Classical.choose_spec (exists_varianceCosineExample_common_event P N hAdm mu0 hU hm)).2.2
  have hmem : w ∈ Classical.choose (exists_varianceCosineExample_common_event P N hAdm mu0 hU hm) := by
    simpa only [varianceCosineExampleGood,dif_pos hAdm] using hw
  have h := hh w hmem epsilon he hN
  exact ⟨h.1,h.2.1⟩

/-- The same selected event retains both finite-scale trace bounds and the
right/pre zero-envelope conclusions from M13T. -/
theorem varianceCosineExampleGood_tracking
    (P : VarianceCosineExampleParameters)
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius) (hm : varianceCosineMean mu0=0)
    (N : Nat) (epsilon : Real) (he : 0<epsilon)
    (hN : varianceCosineExampleRateCutoff P epsilon he<=N)
    (w : VarianceCosineCouplingSpace N) (hw : w ∈ varianceCosineExampleGood P mu0 hU hm N) :
    VarianceCosineExampleTrackingConclusion P w := by
  have hAdm : varianceCosineExampleAdmission P<=N := (le_max_left _ _).trans hN
  have hmem : w ∈ Classical.choose (exists_varianceCosineExample_common_event P N hAdm mu0 hU hm) := by
    simpa only [varianceCosineExampleGood,dif_pos hAdm] using hw
  exact ((Classical.choose_spec (exists_varianceCosineExample_common_event P N hAdm mu0 hU hm)).2.2
    w hmem epsilon he hN).2.2

end PaperFormalization.Manuscript
