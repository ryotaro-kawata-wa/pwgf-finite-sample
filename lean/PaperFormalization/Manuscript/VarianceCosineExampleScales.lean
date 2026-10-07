import PaperFormalization.Manuscript.VarianceCosineExampleSourceInputs

/-! # Literal M13T residuals and smallness, not externally assumed rates
M13w verified implementation; source correspondence and axiom audit passed. All scales are the existing final source scales.
The radius is chosen before every accuracy exponent. The smallness theorem
invokes the proof in sourceUniformRateData, including its real coefficient
estimates and eventual cutoff; no residual inequality is a premise.
-/
open MeasureTheory Set
open scoped NNReal
namespace PaperFormalization.Manuscript
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable def varianceCosineExampleSourceRadius (P : VarianceCosineExampleParameters) (N : Nat) :=
  sourceRateRadius N 1 (varianceCosineExampleHorizon N) (varianceCosineExampleConfidence N)
    2 P.radiusCoefficient P.speed
noncomputable def varianceCosineExamplePopulationScale (P : VarianceCosineExampleParameters) (N : Nat) :=
  sourceFinalMomentScale 1 (varianceCosineExampleHorizon N) 2 P.momentScale
    (varianceCosineExampleConfidence N) P.speed
noncomputable def varianceCosineExampleEnvelope (P : VarianceCosineExampleParameters) (N : Nat) : NNReal :=
  Real.toNNReal (sourceComparisonEnvelope 1 1 1 2 0 (varianceCosineExamplePopulationScale P N)
    (varianceCosineExampleSourceRadius P N) 2 P.thirdBound varianceCosineFeature
    (varianceCosineObjective P.a P.beta))

theorem varianceCosineExampleEnvelope_eq (P : VarianceCosineExampleParameters) (N : Nat) (hN : 0<N) :
    (varianceCosineExampleEnvelope P N : Real) =
      sourceComparisonEnvelope 1 1 1 2 0 (varianceCosineExamplePopulationScale P N)
        (varianceCosineExampleSourceRadius P N) 2 P.thirdBound varianceCosineFeature
        (varianceCosineObjective P.a P.beta) := by
  have hconf := varianceCosineExampleConfidence_bounds N hN
  have hT : 0 <= varianceCosineExampleHorizon N := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hK := (sourceFinalScales_positive 1 (varianceCosineExampleHorizon N) 2 P.momentScale
    (varianceCosineExampleConfidence N) P.speed (by norm_num) hconf.1 hconf.2).2
  have hD := sourceRateRadius_one_le N 1 (varianceCosineExampleHorizon N)
    (varianceCosineExampleConfidence N) 2 P.radiusCoefficient P.speed hN hT hconf.1 hconf.2.le
    (by norm_num) P.radiusCoefficient_admissible.1
  change 1 <= varianceCosineExampleSourceRadius P N at hD
  have hR := one_le_sourceMomentRadius 1 1 1 2 0 (varianceCosineExamplePopulationScale P N)
    (varianceCosineExampleSourceRadius P N) 2 (by norm_num) hK.le (by linarith)
  unfold varianceCosineExampleEnvelope
  apply Real.coe_toNNReal
  unfold sourceComparisonEnvelope sourceObjectiveAnchorFactor
  have := P.thirdBound_nonneg
  positivity

noncomputable def varianceCosineExampleDelta (P : VarianceCosineExampleParameters) (N : Nat) :=
  sourceFinalGammaThreshold 1 N (varianceCosineExampleHorizon N) 2 P.momentScale
    (varianceCosineExampleSourceRadius P N) (varianceCosineExampleConfidence N)
    1 1 1 2 0 P.speed (varianceCosineExampleEnvelope P N)
noncomputable def varianceCosineExampleDeltaTilde (P : VarianceCosineExampleParameters) (N : Nat) :=
  sourcePrescribedCovarianceEnvelope 1 N 1 1 1 1 2 0 2 (varianceCosineExamplePopulationScale P N)
    (varianceCosineExampleEnvelope P N) (varianceCosineExampleConfidence N)
noncomputable def varianceCosineExampleA (P : VarianceCosineExampleParameters) (N : Nat) :=
  sourceFinalJumpCoefficient 1 1 1 1 1 2 0 (varianceCosineExampleSourceRadius P N)
    (varianceCosineExampleConfidence N) (varianceCosineExampleEnvelope P N)
noncomputable def varianceCosineExampleLambda (P : VarianceCosineExampleParameters) (N : Nat) :=
  featureDisplacementLambda 1 1 1 2 0 (varianceCosineExampleSourceRadius P N)
    (varianceCosineExampleEnvelope P N)
noncomputable def varianceCosineExampleCD (P : VarianceCosineExampleParameters) (N : Nat) :=
  varianceCosineExampleLambda P N+3*(varianceCosineExampleEnvelope P N : Real)

/-- Direct evaluation of the ACTUAL residual-smallness theorem at the example
horizon. Accuracy only affects the uniform cutoff, never radius or event. -/
theorem varianceCosineExample_smallness_of_response
    (P : VarianceCosineExampleParameters) (N : Nat) (hN : 0<N)
    (hconf : (N:Real)^(-1:Real) <= varianceCosineExampleConfidence N)
    (kappa : Real -> Real)
    (hresp : SourceControlledResponse N 1 (varianceCosineExampleHorizon N) (1/16)
      P.controlledConstant kappa (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta))
    (epsilon : Real) (he : 0<epsilon) (hcut : (P.rateData epsilon he).val.2<=N) :
    SourceTrackingSmallness kappa (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta)
      1 (varianceCosineExampleHorizon N) (varianceCosineExampleDelta P N)
      (varianceCosineExampleDeltaTilde P N) (varianceCosineExampleA P N) (varianceCosineExampleCD P N) := by
  have hp := varianceCosineExampleConfidence_bounds N hN
  have ht : 0<=varianceCosineExampleHorizon N := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hH : varianceCosineExampleHorizon N <= (N:Real)^(1/4-(1/16)-(1/16):Real) := by
    norm_num [varianceCosineExampleHorizon]
  have heta : forall i : Nat, i<1 -> 0<=varianceCosineAmplitudes P.eta i ∧
      varianceCosineAmplitudes P.eta i<=P.controlledConstant := by
    intro i hi
    have heq : i=0 := by omega
    subst i
    exact ⟨ P.eta_pos.le,P.eta_le_controlledConstant ⟩
  have h := (P.rateData epsilon he).property.2.2 N 1 hcut
    (varianceCosineExampleHorizon N) (varianceCosineExampleConfidence N)
    (by norm_num) ht hp.1 hp.2 hH hconf (varianceCosineExampleEnvelope P N)
    (varianceCosineExampleEnvelope_eq P N hN) kappa
    (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta) heta hresp
  simpa only [varianceCosineExampleDelta,varianceCosineExampleDeltaTilde,varianceCosineExampleA,
    varianceCosineExampleCD,varianceCosineExampleLambda,varianceCosineExampleSourceRadius,
    varianceCosineExamplePopulationScale,VarianceCosineExampleParameters.radiusCoefficient,
    show (2+(1:Real))=3 by norm_num] using h.1

end PaperFormalization.Manuscript
