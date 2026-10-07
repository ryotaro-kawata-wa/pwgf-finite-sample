import PaperFormalization.Manuscript.VarianceCosineExampleCommonEvent

/-! # The complete growing-horizon variance-plus-cosine application
M13w verified implementation; source correspondence and axiom audit passed. The theorems below call the actual source
application and its concrete good-event constructor. No comparison rate,
smallness, escape estimate, output law or population decay is a model premise.

Target: prop:canonical-model-assumptions in the unchanged arxiv appendix.
The stronger statement selects constants before mu0 and an event family before
every epsilon. Both printed suprema are formed only after boundedness and
nonemptiness. The late summand is the empirical objective excess above -beta.
See the M13W receipt and separate claim review for the executed scope.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace PaperFormalization.Manuscript
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

/-- Integrability of the displayed objective is never inferred from a totalized
real integral. It is derived for both genuine empirical and population laws. -/
theorem varianceCosineExample_objective_integrability
    (P : VarianceCosineExampleParameters) {N : Nat} (hN : 0<N)
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius)
    (T : Real) (w : VarianceCosineCouplingSpace N) (t : Real) :
    Integrable varianceCosineEncodedFeature
      (finiteEmpiricalMeasure (fun i => (varianceCosineExamplePair P T w t).1 i)) ∧
    Integrable varianceCosineEncodedFeature (varianceCosineExamplePopulation P mu0 T w t) := by
  letI : Nonempty (Fin N) := ⟨ ⟨ 0,hN ⟩ ⟩
  exact ⟨ integrable_finiteEmpiricalMeasure _ _,
    varianceCosineEncodedFeature_integrable _ (varianceCosineExamplePopulation_memLp P mu0 hU T w t) ⟩

/-- Real-valued probability consequence, on the original unchanged law. -/
theorem varianceCosineExampleGood_probability_real
    (P : VarianceCosineExampleParameters)
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius) (hm : varianceCosineMean mu0=0)
    (N : Nat) (hN : varianceCosineExampleAdmission P<=N) :
    1-varianceCosineExampleFailure N<=
      (varianceCosineModelLaw N mu0).real (varianceCosineExampleGood P mu0 hU hm N) := by
  have hN0 : 0<N := by have hh := (varianceCosineExample_admission_spec P N hN).1; omega
  have hq := varianceCosineExampleFailure_bounds N hN0
  have hbudget := varianceCosineExampleGood_probability P mu0 hU hm N hN
  have hmG := varianceCosineExampleGood_measurable P mu0 hU hm N
  have hbudgetR := (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hbudget
  have hb0 : 0 <= 49*varianceCosineExampleFailure N/64 := by nlinarith [hq.1]
  rw [ENNReal.toReal_ofReal hb0] at hbudgetR
  let law := varianceCosineModelLaw N mu0
  let G := varianceCosineExampleGood P mu0 hU hm N
  have hsum : law.real G+law.real Gᶜ=1 := by
    have h := measure_add_measure_compl (μ := law) hmG
    have hh := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),measure_univ,
      ENNReal.toReal_one] at hh
    exact hh
  change law.real Gᶜ<=49*varianceCosineExampleFailure N/64 at hbudgetR
  change 1-varianceCosineExampleFailure N<=law.real G
  linarith

/-- Boundedness and the nonempty late interval precede the use of real sSup. -/
theorem varianceCosineExampleGood_suprema
    (P : VarianceCosineExampleParameters)
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius) (hm : varianceCosineMean mu0=0)
    (N : Nat) (epsilon : Real) (he : 0<epsilon)
    (hN : varianceCosineExampleRateCutoff P epsilon he<=N)
    (w : VarianceCosineCouplingSpace N) (hw : w ∈ varianceCosineExampleGood P mu0 hU hm N) :
    let T := varianceCosineExampleHorizon N
    let S := P.waitConstant*Real.log (N:Real)
    let C := varianceCosineExampleRateConstant P epsilon he
    S<T ∧ VarianceCosineExampleActualSmallness P N w ∧
    BddAbove ((varianceCosineExampleError P mu0 T w) '' Icc 0 T) ∧
    sSup ((varianceCosineExampleError P mu0 T w) '' Icc 0 T)<=C*(N:Real)^(-(3/16:Real)+epsilon) ∧
    varianceCosineExamplePreError P mu0 T w<=C*(N:Real)^(-(3/16:Real)+epsilon) ∧
    BddAbove ((varianceCosineExampleLateError P mu0 T w) '' Icc S T) ∧
    sSup ((varianceCosineExampleLateError P mu0 T w) '' Icc S T)<=C*(N:Real)^(-(1/2:Real)+epsilon) ∧
    (forall t, t ∈ Icc S T ->
      0<=varianceCosineEmpiricalExcess P (varianceCosineExamplePair P T w t).1) := by
  dsimp only
  have hAdm : varianceCosineExampleAdmission P<=N := (le_max_left _ _).trans hN
  have hspec := varianceCosineExample_admission_spec P N hAdm
  have hr := varianceCosineExampleGood_rates P mu0 hU hm N epsilon he hN w hw
  have hT : 0<=varianceCosineExampleHorizon N := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hwhole := source_uniform_error_sup_bound
    (varianceCosineExampleError P mu0 (varianceCosineExampleHorizon N) w)
    (varianceCosineExampleHorizon N)
    (varianceCosineExampleRateConstant P epsilon he*(N:Real)^(-(3/16:Real)+epsilon)) hT hr.2.1
  let S := P.waitConstant*Real.log (N:Real)
  let late := varianceCosineExampleLateError P mu0 (varianceCosineExampleHorizon N) w
  let L := varianceCosineExampleRateConstant P epsilon he*(N:Real)^(-(1/2:Real)+epsilon)
  have hlate (t : Real) (ht : t ∈ Icc S (varianceCosineExampleHorizon N)) : late t<=L :=
    (hr.2.2.2 t ht).2
  have hb : BddAbove (late '' Icc S (varianceCosineExampleHorizon N)) := by
    refine ⟨ L,?_ ⟩
    rintro _ ⟨ t,ht,rfl ⟩
    exact hlate t ht
  have hn : (late '' Icc S (varianceCosineExampleHorizon N)).Nonempty :=
    ⟨ late S,S,⟨ le_rfl,hspec.2.2.2.le ⟩,rfl ⟩
  have hs : sSup (late '' Icc S (varianceCosineExampleHorizon N))<=L := by
    apply csSup_le hn
    rintro _ ⟨ t,ht,rfl ⟩
    exact hlate t ht
  exact ⟨ hspec.2.2.2,hr.1,hwhole.1,hwhole.2,hr.2.2.1,hb,hs,
    fun t ht => (hr.2.2.2 t ht).1 ⟩

/-- Explicit event-family form of the complete proposition. Quantifier order:
fixed P -> constants/cutoffs -> original mu0 -> ONE family of events -> epsilon.
The functions for constants and cutoffs have NO mu0/N/T/sample arguments.
Every real probability and supremum concerns the original canonical coupling.
-/
theorem varianceCosine_growing_example
    (P : VarianceCosineExampleParameters) :
    0<P.waitConstant ∧
    (forall epsilon (he : 0<epsilon), 0<varianceCosineExampleRateConstant P epsilon he) ∧
    forall (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0],
      (∀ᵐ u ∂ mu0, norm u<=P.radius) -> varianceCosineMean mu0=0 ->
      ∃ Good : (N : Nat) -> Set (VarianceCosineCouplingSpace N),
        (forall N, MeasurableSet (Good N)) ∧
        (forall N, varianceCosineExampleAdmission P<=N ->
          varianceCosineModelLaw N mu0 (Good N)ᶜ<=ENNReal.ofReal (49*varianceCosineExampleFailure N/64) ∧
          1-varianceCosineExampleFailure N<=(varianceCosineModelLaw N mu0).real (Good N)) ∧
        forall epsilon (he : 0<epsilon) N,
          varianceCosineExampleRateCutoff P epsilon he<=N ->
          forall w, w ∈ Good N ->
          let T := varianceCosineExampleHorizon N
          let S := P.waitConstant*Real.log (N:Real)
          let C := varianceCosineExampleRateConstant P epsilon he
          VarianceCosineExampleTrackingConclusion P w ∧
          S<T ∧ VarianceCosineExampleActualSmallness P N w ∧
          BddAbove ((varianceCosineExampleError P mu0 T w) '' Icc 0 T) ∧
          sSup ((varianceCosineExampleError P mu0 T w) '' Icc 0 T)<=C*(N:Real)^(-(3/16:Real)+epsilon) ∧
          varianceCosineExamplePreError P mu0 T w<=C*(N:Real)^(-(3/16:Real)+epsilon) ∧
          BddAbove ((varianceCosineExampleLateError P mu0 T w) '' Icc S T) ∧
          sSup ((varianceCosineExampleLateError P mu0 T w) '' Icc S T)<=C*(N:Real)^(-(1/2:Real)+epsilon) ∧
          (forall t, t ∈ Icc S T -> 0<=varianceCosineEmpiricalExcess P (varianceCosineExamplePair P T w t).1) := by
  refine ⟨ P.waitConstant_pos,varianceCosineExampleRateConstant_pos P,?_ ⟩
  intro mu0 hmu hU hm
  letI : IsProbabilityMeasure mu0 := hmu
  refine ⟨ varianceCosineExampleGood P mu0 hU hm,
    varianceCosineExampleGood_measurable P mu0 hU hm,?_,?_ ⟩
  . intro N hN
    exact ⟨ varianceCosineExampleGood_probability P mu0 hU hm N hN,
      varianceCosineExampleGood_probability_real P mu0 hU hm N hN ⟩
  . intro epsilon he N hN w hw
    exact ⟨varianceCosineExampleGood_tracking P mu0 hU hm N epsilon he hN w hw,
      varianceCosineExampleGood_suprema P mu0 hU hm N epsilon he hN w hw⟩

/-- The fixed-epsilon wording printed in the proposition, derived from the
stronger event-family theorem. N0 and C depend only on fixed P and epsilon,
not on the initial law beyond its stated support/mean restrictions. -/
theorem varianceCosine_printed_proposition
    (P : VarianceCosineExampleParameters) (epsilon : Real) (he : 0<epsilon) :
    ∃ CLog C : Real, ∃ N0 : Nat, 0<CLog ∧ 0<C ∧
      forall (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0],
      (∀ᵐ u ∂ mu0, norm u<=P.radius) -> varianceCosineMean mu0=0 ->
      forall N, N0<=N ->
        let T := (N:Real)^(1/8:Real)
        CLog*Real.log (N:Real)<T ∧
        ∃ Good : Set (VarianceCosineCouplingSpace N), MeasurableSet Good ∧
          1-(N:Real)^(-(1/16:Real))<=(varianceCosineModelLaw N mu0).real Good ∧
          forall w, w ∈ Good ->
            sSup ((varianceCosineExampleError P mu0 T w) '' Icc 0 T)<=C*(N:Real)^(-(3/16:Real)+epsilon) ∧
            sSup ((varianceCosineExampleLateError P mu0 T w) '' Icc (CLog*Real.log (N:Real)) T)<=
              C*(N:Real)^(-(1/2:Real)+epsilon) := by
  refine ⟨ P.waitConstant,varianceCosineExampleRateConstant P epsilon he,
    varianceCosineExampleRateCutoff P epsilon he,P.waitConstant_pos,
    varianceCosineExampleRateConstant_pos P epsilon he,?_ ⟩
  intro mu0 hmu hU hm N hN
  letI : IsProbabilityMeasure mu0 := hmu
  have hAdm : varianceCosineExampleAdmission P<=N := (le_max_left _ _).trans hN
  refine ⟨ (varianceCosineExample_admission_spec P N hAdm).2.2.2,
    varianceCosineExampleGood P mu0 hU hm N,
    varianceCosineExampleGood_measurable P mu0 hU hm N,
    varianceCosineExampleGood_probability_real P mu0 hU hm N hAdm,?_ ⟩
  intro w hw
  have h := varianceCosineExampleGood_suprema P mu0 hU hm N epsilon he hN w hw
  exact ⟨ h.2.2.2.1,h.2.2.2.2.2.2.1 ⟩

/-- Exact paired-configuration equality on both sides when the actual source
envelope is zero. This does not assert that the objective sampling gap is zero. -/
theorem varianceCosineExampleGood_zero_envelope
    (P : VarianceCosineExampleParameters)
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius) (hm : varianceCosineMean mu0=0)
    (N : Nat) (epsilon : Real) (he : 0<epsilon)
    (hN : varianceCosineExampleRateCutoff P epsilon he<=N)
    (w : VarianceCosineCouplingSpace N) (hw : w ∈ varianceCosineExampleGood P mu0 hU hm N)
    (hz : sourceCurvatureEnvelopeSup
      (varianceCosineRightCurvature P.a P.beta P.tau P.eta (varianceCosineExampleHorizon N) w.2.1)
      (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta)
      (varianceCosineExampleDelta P N) (varianceCosineExampleDeltaTilde P N)
      (varianceCosineExampleA P N) 1 (varianceCosineExampleHorizon N) = 0) :
    (∀ t ∈ Icc 0 (varianceCosineExampleHorizon N),
      (varianceCosineExamplePair P (varianceCosineExampleHorizon N) w t).1 =
      (varianceCosineExamplePair P (varianceCosineExampleHorizon N) w t).2) ∧
    (varianceCosineModelBranches P.a P.beta P.tau P.eta (varianceCosineExampleHorizon N) w 0 P.tau).1 =
      (varianceCosineModelBranches P.a P.beta P.tau P.eta (varianceCosineExampleHorizon N) w 0 P.tau).2 := by
  have h := varianceCosineExampleGood_tracking P mu0 hU hm N epsilon he hN w hw
  exact ⟨h.2.1 hz,h.2.2.2 hz 0 (by omega)⟩

end PaperFormalization.Manuscript
