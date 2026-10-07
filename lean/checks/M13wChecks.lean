import PaperFormalization.Manuscript.VarianceCosineExampleVanishingBounds

/-! M13W executed boundary and interface probes (44 examples). No example is a new axiom.
These probes complement (rather than replace) the canonical named-declaration
build/audit. Every new declaration is also checked and queried below. -/
open MeasureTheory ProbabilityTheory Set Filter
open PaperFormalization.Manuscript
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 4000000

-- Totalized scales at zero and one are not admitted as a spectral theorem.
example : varianceCosineExampleHorizon 0=0 := by norm_num [varianceCosineExampleHorizon]
example : varianceCosineExampleHorizon 1=1 := by norm_num [varianceCosineExampleHorizon]
example : varianceCosineExampleFailure 1=1 := by norm_num [varianceCosineExampleFailure]
example : varianceCosineExampleConfidence 1=(1/2:Real) := by
  norm_num [varianceCosineExampleConfidence,varianceCosineExampleFailure]
example (N : Nat) (hN : 0<N) :
    0<varianceCosineExampleConfidence N ∧ varianceCosineExampleConfidence N<1 :=
  varianceCosineExampleConfidence_bounds N hN
example (N : Nat) (hN : 0<N) : varianceCosineExampleFailure N<=1 :=
  (varianceCosineExampleFailure_bounds N hN).2

-- All positive real accuracy exponents; no upper bound or integer restriction.
example (epsilon : Real) (he : 0<epsilon) : 0<varianceCosineExampleExponent epsilon :=
  varianceCosineExampleExponent_pos epsilon he
example (epsilon : Real) (he : 0<epsilon) :
    (9/4:Real)*varianceCosineExampleExponent epsilon<=epsilon := by
  unfold varianceCosineExampleExponent
  linarith
example (P : VarianceCosineExampleParameters) (N : Nat) :
    varianceCosineExampleRadius P N=P.escapeCoefficient*(N:Real)^(-(1/16:Real)) :=
  varianceCosineExampleRadius_formula P N
example (P : VarianceCosineExampleParameters) : 0<P.escapeCoefficient ∧ P.escapeCoefficient<=1/8 :=
  P.escapeCoefficient_bounds
example (P : VarianceCosineExampleParameters) : 0<P.sigma := P.sigma_pos
example (P : VarianceCosineExampleParameters) : 0<P.b ∧ 0<P.lam := ⟨ P.b_pos,P.lam_pos ⟩
example (P : VarianceCosineExampleParameters) (epsilon : Real) (he : 0<epsilon) :
    varianceCosineExampleAdmission P<=varianceCosineExampleRateCutoff P epsilon he := le_max_left _ _
example (P : VarianceCosineExampleParameters) : ¬ (varianceCosineExampleAdmission P<=1) := by
  have h : 4<=varianceCosineExampleAdmission P := le_max_left _ _
  omega
example (P : VarianceCosineExampleParameters) (N : Nat) (hN : varianceCosineExampleAdmission P<=N) :
    P.waitConstant*Real.log (N:Real)<varianceCosineExampleHorizon N :=
  (varianceCosineExample_admission_spec P N hN).2.2.2

-- Before/at the jump: the right value includes the new jump, the pretrace does not.
example {E : Type*} (P : VarianceCosineExampleParameters) (F : Nat -> Real -> E) :
    sourceGlue (varianceCosineTimes P.tau) 1 F 0=F 0 0 := by
  rw [varianceCosineGlue_one,if_pos P.tau_pos]
example {E : Type*} (tau : Real) (F : Nat -> Real -> E) :
    sourceGlue (varianceCosineTimes tau) 1 F tau=F 1 tau := by
  rw [varianceCosineGlue_one,if_neg (lt_irrefl tau)]
example (k : Real -> Real) (tau eta t : Real) :
    sourceRateJumpResponse k (varianceCosineTimes tau) (varianceCosineAmplitudes eta) 0 t=0 := by
  simp [sourceRateJumpResponse]
example (k : Real -> Real) (tau eta : Real) :
    sourceRateJumpResponse k (varianceCosineTimes tau) (varianceCosineAmplitudes eta) 1 tau=eta := by
  rw [varianceCosineExample_jump_response]
  simp [recoveryJumpResponse,PaperFormalization.Continuous.propagator_self]
example (k : Real -> Real) (tau eta t : Real) (ht : t<tau) :
    sourceRateJumpResponse k (varianceCosineTimes tau) (varianceCosineAmplitudes eta) 1 t=0 := by
  rw [varianceCosineExample_jump_response]
  simp [recoveryJumpResponse,ht,not_le.mpr ht]
example (P : VarianceCosineExampleParameters) {N : Nat} (T : Real) (w : VarianceCosineCouplingSpace N) :
    varianceCosineExamplePair P T w 0=(w.1,w.1) := by
  simpa only [varianceCosineExamplePair,if_pos P.tau_pos,varianceCosineModelBranches] using
    varianceCosinePairBranch_start P.a P.beta P.tau P.eta T w.1 w.2.1
      (varianceCosineCouplingZeta P.a P.beta P.tau w)

-- Reassociation keeps the same original scalar and the same auxiliary vector.
example {N : Nat} (w : VarianceCosineCouplingSpace N) :
    varianceCosineTowerCoordinates (varianceCosineTowerInverse w)=w := varianceCosineTower_right_inverse w
example {N : Nat} (z : VarianceCosineExampleTower N) :
    varianceCosineTowerInverse (varianceCosineTowerCoordinates z)=z := varianceCosineTower_left_inverse z
example {N : Nat} (o : VarianceCosineOriginalSpace N) : varianceCosineOriginalInnovation 1 o=0 := rfl
example {N : Nat} (U : SourceFiniteConfiguration N 1) (Z1 Z2 : Real) :
    sourceOriginalPrehistory varianceCosineOriginalInitial varianceCosineOriginalInnovation 0 (U,Z1)=
    sourceOriginalPrehistory varianceCosineOriginalInitial varianceCosineOriginalInnovation 0 (U,Z2) := by
  apply Prod.ext
  . funext i; exact Fin.elim0 i
  . rfl

-- Equal paired configurations do not imply a zero population sampling error.
example (P : VarianceCosineExampleParameters) {N : Nat}
    (mu : Measure VarianceCosinePoint) (X : SourceFiniteConfiguration N 1) :
    varianceCosinePairFunctionalError P mu X X =
      abs (varianceCosineFunctional P.a P.beta (finiteEmpiricalMeasure (fun i => X i))-
        varianceCosineFunctional P.a P.beta mu) := by
  simp [varianceCosinePairFunctionalError]
example (P : VarianceCosineExampleParameters) {N : Nat} (hN : 0<N) (X : SourceFiniteConfiguration N 1) :
    0<=varianceCosineEmpiricalExcess P X := by
  letI : Nonempty (Fin N) := ⟨ ⟨ 0,hN ⟩ ⟩
  have h := varianceCosineFunctional_lower P.a P.beta P.a_pos.le P.beta_pos.le _
    (varianceCosineEmpirical_memLp hN X)
  unfold varianceCosineEmpiricalExcess
  linarith

-- No independence premise is present in either budget diagnostic.
example {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega) (A E : Set Omega)
    (q : Real) (hq : 0<=q) (ha : mu Aᶜ<=ENNReal.ofReal (17*(q/2)/32))
    (he : mu Eᶜ<=ENNReal.ofReal (q/2)) :
    mu (A ∩ E)ᶜ<=ENNReal.ofReal (49*q/64) :=
  varianceCosineExample_intersection_budget mu A E q hq ha he
example {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega) (A E : Set Omega)
    (ha : mu Aᶜ=0) (he : mu Eᶜ=0) : mu (A ∩ E)ᶜ=0 := by
  apply le_antisymm _ zero_le
  have h := varianceCosineExample_intersection_budget mu A E 0 (by norm_num)
    (by simp [ha]) (by simp [he])
  simpa using h
example (f : Real -> Real) (s : Real) : BddAbove (f '' Icc s s) := by simp

-- The family is selected once; both accuracies use this same set and outcome.
example (P : VarianceCosineExampleParameters) (mu0 : Measure VarianceCosinePoint)
    [IsProbabilityMeasure mu0] (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius)
    (hm : varianceCosineMean mu0=0) (N : Nat) (hN : N<varianceCosineExampleAdmission P) :
    varianceCosineExampleGood P mu0 hU hm N=∅ := by
  simp [varianceCosineExampleGood,not_le.mpr hN]
example (P : VarianceCosineExampleParameters) (mu0 : Measure VarianceCosinePoint)
    [IsProbabilityMeasure mu0] (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius)
    (hm : varianceCosineMean mu0=0) (N : Nat) (e1 e2 : Real) (h1 : 0<e1) (h2 : 0<e2)
    (hc : max (varianceCosineExampleRateCutoff P e1 h1) (varianceCosineExampleRateCutoff P e2 h2)<=N)
    (w : VarianceCosineCouplingSpace N) (hw : w ∈ varianceCosineExampleGood P mu0 hU hm N) :
    VarianceCosineExamplePointwiseRates P mu0 N w e1 h1 ∧
    VarianceCosineExamplePointwiseRates P mu0 N w e2 h2 := by
  exact ⟨ (varianceCosineExampleGood_rates P mu0 hU hm N e1 h1 ((le_max_left _ _).trans hc) w hw).2,
    (varianceCosineExampleGood_rates P mu0 hU hm N e2 h2 ((le_max_right _ _).trans hc) w hw).2 ⟩
example (P : VarianceCosineExampleParameters) (mu0 : Measure VarianceCosinePoint)
    [IsProbabilityMeasure mu0] (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius)
    (hm : varianceCosineMean mu0=0) (N : Nat) : MeasurableSet (varianceCosineExampleGood P mu0 hU hm N) :=
  varianceCosineExampleGood_measurable P mu0 hU hm N
example (P : VarianceCosineExampleParameters) {N : Nat} (hN : 0<N)
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius) (T : Real) (w : VarianceCosineCouplingSpace N) (t : Real) :
    Integrable varianceCosineEncodedFeature (varianceCosineExamplePopulation P mu0 T w t) :=
  (varianceCosineExample_objective_integrability P hN mu0 hU T w t).2
example (P : VarianceCosineExampleParameters) (epsilon : Real) (he : 0<epsilon) :
    0<varianceCosineExampleRateConstant P epsilon he := varianceCosineExampleRateConstant_pos P epsilon he
example (P : VarianceCosineExampleParameters) (epsilon : Real) (he : 0<epsilon) :
    0<varianceCosineExampleRateCutoff P epsilon he := by
  have h : 4<=varianceCosineExampleAdmission P := le_max_left _ _
  have hh : varianceCosineExampleAdmission P<=varianceCosineExampleRateCutoff P epsilon he := le_max_left _ _
  omega

-- Strict accuracy windows for vanishing; no all-epsilon convergence claim.
example (P : VarianceCosineExampleParameters) (epsilon : Real) (he : 0<epsilon) (hu : epsilon<3/16) :
    Tendsto (fun N : Nat => varianceCosineExampleRateConstant P epsilon he*(N:Real)^(-(3/16:Real)+epsilon))
      atTop (nhds 0) := varianceCosineExample_whole_majorant_tendsto_zero P epsilon he hu
example (P : VarianceCosineExampleParameters) (epsilon : Real) (he : 0<epsilon) (hu : epsilon<1/2) :
    Tendsto (fun N : Nat => varianceCosineExampleRateConstant P epsilon he*(N:Real)^(-(1/2:Real)+epsilon))
      atTop (nhds 0) := varianceCosineExample_late_majorant_tendsto_zero P epsilon he hu
example (P : VarianceCosineExampleParameters) (mu0 : Measure VarianceCosinePoint)
    [IsProbabilityMeasure mu0] (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius) (hm : varianceCosineMean mu0=0) :
    Tendsto (fun N : Nat => (varianceCosineModelLaw N mu0).real
      (varianceCosineExampleGood P mu0 hU hm N)ᶜ) atTop (nhds 0) :=
  varianceCosineExampleGood_complement_tendsto_zero P mu0 hU hm

-- Additional ZIP-derived boundary cases, adapted to GitHub definitions.
-- Zero time and zero curvature are distinct from exponential recovery.
example (kappa : Real -> Real) : sourceRateContinuousResponse kappa 0=0 := by
  simp [sourceRateContinuousResponse]
example : recoveryContinuousResponse (fun _ => 0) 1=1 := by
  simp [recoveryContinuousResponse,PaperFormalization.Continuous.propagator]
-- Total response formulas do not require a positive jump amplitude.
example (kappa : Real -> Real) (tau t : Real) :
    sourceRateJumpResponse kappa (varianceCosineTimes tau) (varianceCosineAmplitudes 0) 1 t=0 := by
  simp [sourceRateJumpResponse,varianceCosineAmplitudes]
-- A concrete nonzero objective gap; equality of paired clouds cannot remove it.
example : abs (varianceCosineFunctional 1 1 (Measure.dirac (varianceCosinePoint 0))-
    varianceCosineFunctional 1 1 (Measure.dirac (varianceCosinePoint 1)))=2 := by
  norm_num [varianceCosineFunctional,varianceCosineVariance,varianceCosineMean,varianceCosineScalar_point]
-- Both exact zero conclusions are outputs on the SAME chosen event.
example (P : VarianceCosineExampleParameters)
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius) (hm : varianceCosineMean mu0=0)
    (N : Nat) (epsilon : Real) (he : 0<epsilon)
    (hN : varianceCosineExampleRateCutoff P epsilon he<=N)
    (w : VarianceCosineCouplingSpace N) (hw : w ∈ varianceCosineExampleGood P mu0 hU hm N)
    (hz : sourceCurvatureEnvelopeSup
      (varianceCosineRightCurvature P.a P.beta P.tau P.eta (varianceCosineExampleHorizon N) w.2.1)
      (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta)
      (varianceCosineExampleDelta P N) (varianceCosineExampleDeltaTilde P N)
      (varianceCosineExampleA P N) 1 (varianceCosineExampleHorizon N)=0) :
    (∀ t ∈ Icc 0 (varianceCosineExampleHorizon N),
      (varianceCosineExamplePair P (varianceCosineExampleHorizon N) w t).1 =
      (varianceCosineExamplePair P (varianceCosineExampleHorizon N) w t).2) ∧
    (varianceCosineModelBranches P.a P.beta P.tau P.eta (varianceCosineExampleHorizon N) w 0 P.tau).1 =
      (varianceCosineModelBranches P.a P.beta P.tau P.eta (varianceCosineExampleHorizon N) w 0 P.tau).2 :=
  varianceCosineExampleGood_zero_envelope P mu0 hU hm N epsilon he hN w hw hz

-- Full declared interface and transitive axiom diagnostics.
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.speed
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.speed
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.momentScale
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.momentScale
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.momentScale_pos
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.momentScale_pos
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.thirdBound
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.thirdBound
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.thirdBound_nonneg
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.thirdBound_nonneg
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.b
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.b
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.lam
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.lam
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.sigma
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.sigma
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.landingVariance
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.landingVariance
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.densityConstant
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.densityConstant
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.escapeCoefficient
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.escapeCoefficient
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.responseConstant
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.responseConstant
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.wholeResponse
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.wholeResponse
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.controlledConstant
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.controlledConstant
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.lateContinuous
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.lateContinuous
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.lateJump
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.lateJump
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.populationExcessConstant
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.populationExcessConstant
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.waitIntercept
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.waitIntercept
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.waitSlope
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.waitSlope
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.waitConstant
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.waitConstant
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.b_pos
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.b_pos
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.lam_pos
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.lam_pos
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.sigma_pos
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.sigma_pos
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.densityConstant_ge_four
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.densityConstant_ge_four
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.escapeCoefficient_bounds
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.escapeCoefficient_bounds
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.responseConstant_nonneg
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.responseConstant_nonneg
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.wholeResponse_nonneg
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.wholeResponse_nonneg
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.controlledConstant_pos
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.controlledConstant_pos
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.eta_le_controlledConstant
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.eta_le_controlledConstant
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.wholeResponse_le_controlledConstant
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.wholeResponse_le_controlledConstant
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.lateContinuous_nonneg
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.lateContinuous_nonneg
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.lateJump_nonneg
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.lateJump_nonneg
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.populationExcessConstant_nonneg
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.populationExcessConstant_nonneg
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.waitConstant_pos
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.waitConstant_pos
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.rateData
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.rateData
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.radiusCoefficient
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.radiusCoefficient
#check PaperFormalization.Manuscript.VarianceCosineExampleParameters.radiusCoefficient_admissible
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleParameters.radiusCoefficient_admissible
#check PaperFormalization.Manuscript.varianceCosineExampleHorizon
#print axioms PaperFormalization.Manuscript.varianceCosineExampleHorizon
#check PaperFormalization.Manuscript.varianceCosineExampleFailure
#print axioms PaperFormalization.Manuscript.varianceCosineExampleFailure
#check PaperFormalization.Manuscript.varianceCosineExampleConfidence
#print axioms PaperFormalization.Manuscript.varianceCosineExampleConfidence
#check PaperFormalization.Manuscript.varianceCosineExampleRadius
#print axioms PaperFormalization.Manuscript.varianceCosineExampleRadius
#check PaperFormalization.Manuscript.varianceCosineExampleRadius_formula
#print axioms PaperFormalization.Manuscript.varianceCosineExampleRadius_formula
#check PaperFormalization.Manuscript.varianceCosineExampleFailure_bounds
#print axioms PaperFormalization.Manuscript.varianceCosineExampleFailure_bounds
#check PaperFormalization.Manuscript.varianceCosineExampleConfidence_bounds
#print axioms PaperFormalization.Manuscript.varianceCosineExampleConfidence_bounds
#check PaperFormalization.Manuscript.VarianceCosineOriginalSpace
#print axioms PaperFormalization.Manuscript.VarianceCosineOriginalSpace
#check PaperFormalization.Manuscript.VarianceCosineExampleTower
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleTower
#check PaperFormalization.Manuscript.varianceCosineOriginalLaw
#print axioms PaperFormalization.Manuscript.varianceCosineOriginalLaw
#check PaperFormalization.Manuscript.varianceCosineExampleTowerLaw
#print axioms PaperFormalization.Manuscript.varianceCosineExampleTowerLaw
#check PaperFormalization.Manuscript.varianceCosineOriginalInitial
#print axioms PaperFormalization.Manuscript.varianceCosineOriginalInitial
#check PaperFormalization.Manuscript.varianceCosineOriginalInnovation
#print axioms PaperFormalization.Manuscript.varianceCosineOriginalInnovation
#check PaperFormalization.Manuscript.varianceCosineTowerInverse
#print axioms PaperFormalization.Manuscript.varianceCosineTowerInverse
#check PaperFormalization.Manuscript.varianceCosineTower_left_inverse
#print axioms PaperFormalization.Manuscript.varianceCosineTower_left_inverse
#check PaperFormalization.Manuscript.varianceCosineTower_right_inverse
#print axioms PaperFormalization.Manuscript.varianceCosineTower_right_inverse
#check PaperFormalization.Manuscript.varianceCosineTowerInverse_measurable
#print axioms PaperFormalization.Manuscript.varianceCosineTowerInverse_measurable
#check PaperFormalization.Manuscript.varianceCosineOriginalLaw_probability
#print axioms PaperFormalization.Manuscript.varianceCosineOriginalLaw_probability
#check PaperFormalization.Manuscript.varianceCosineExampleTowerLaw_probability
#print axioms PaperFormalization.Manuscript.varianceCosineExampleTowerLaw_probability
#check PaperFormalization.Manuscript.varianceCosineModelLaw_probability
#print axioms PaperFormalization.Manuscript.varianceCosineModelLaw_probability
#check PaperFormalization.Manuscript.varianceCosineTowerInverse_preserving
#print axioms PaperFormalization.Manuscript.varianceCosineTowerInverse_preserving
#check PaperFormalization.Manuscript.varianceCosineOriginalInitial_measurable
#print axioms PaperFormalization.Manuscript.varianceCosineOriginalInitial_measurable
#check PaperFormalization.Manuscript.varianceCosineOriginalInnovation_measurable
#print axioms PaperFormalization.Manuscript.varianceCosineOriginalInnovation_measurable
#check PaperFormalization.Manuscript.varianceCosineOriginal_initial_law
#print axioms PaperFormalization.Manuscript.varianceCosineOriginal_initial_law
#check PaperFormalization.Manuscript.varianceCosineOriginal_iid
#print axioms PaperFormalization.Manuscript.varianceCosineOriginal_iid
#check PaperFormalization.Manuscript.varianceCosineOriginal_population_independent
#print axioms PaperFormalization.Manuscript.varianceCosineOriginal_population_independent
#check PaperFormalization.Manuscript.varianceCosineOriginal_environment_law
#print axioms PaperFormalization.Manuscript.varianceCosineOriginal_environment_law
#check PaperFormalization.Manuscript.varianceCosineOriginal_fresh
#print axioms PaperFormalization.Manuscript.varianceCosineOriginal_fresh
#check PaperFormalization.Manuscript.varianceCosineOriginal_innovation_law
#print axioms PaperFormalization.Manuscript.varianceCosineOriginal_innovation_law
#check PaperFormalization.Manuscript.varianceCosineExample_packed
#print axioms PaperFormalization.Manuscript.varianceCosineExample_packed
#check PaperFormalization.Manuscript.varianceCosineGlue_one
#print axioms PaperFormalization.Manuscript.varianceCosineGlue_one
#check PaperFormalization.Manuscript.varianceCosineOriginalCharacteristic_formula
#print axioms PaperFormalization.Manuscript.varianceCosineOriginalCharacteristic_formula
#check PaperFormalization.Manuscript.varianceCosineExample_strict_times
#print axioms PaperFormalization.Manuscript.varianceCosineExample_strict_times
#check PaperFormalization.Manuscript.varianceCosineExampleCanonicalFlow
#print axioms PaperFormalization.Manuscript.varianceCosineExampleCanonicalFlow
#check PaperFormalization.Manuscript.varianceCosineExamplePost
#print axioms PaperFormalization.Manuscript.varianceCosineExamplePost
#check PaperFormalization.Manuscript.varianceCosineExampleCanonicalBranch
#print axioms PaperFormalization.Manuscript.varianceCosineExampleCanonicalBranch
#check PaperFormalization.Manuscript.varianceCosineExampleCanonicalRight
#print axioms PaperFormalization.Manuscript.varianceCosineExampleCanonicalRight
#check PaperFormalization.Manuscript.varianceCosineExamplePair
#print axioms PaperFormalization.Manuscript.varianceCosineExamplePair
#check PaperFormalization.Manuscript.varianceCosineExampleRawX
#print axioms PaperFormalization.Manuscript.varianceCosineExampleRawX
#check PaperFormalization.Manuscript.varianceCosineExamplePopulation
#print axioms PaperFormalization.Manuscript.varianceCosineExamplePopulation
#check PaperFormalization.Manuscript.varianceCosineExamplePrePopulation
#print axioms PaperFormalization.Manuscript.varianceCosineExamplePrePopulation
#check PaperFormalization.Manuscript.varianceCosineExampleCharacteristic
#print axioms PaperFormalization.Manuscript.varianceCosineExampleCharacteristic
#check PaperFormalization.Manuscript.varianceCosineExampleModelBranches_measurable
#print axioms PaperFormalization.Manuscript.varianceCosineExampleModelBranches_measurable
#check PaperFormalization.Manuscript.varianceCosineExamplePair_measurable
#print axioms PaperFormalization.Manuscript.varianceCosineExamplePair_measurable
#check PaperFormalization.Manuscript.varianceCosineExample_reference_branch
#print axioms PaperFormalization.Manuscript.varianceCosineExample_reference_branch
#check PaperFormalization.Manuscript.varianceCosineExample_reference_right
#print axioms PaperFormalization.Manuscript.varianceCosineExample_reference_right
#check PaperFormalization.Manuscript.varianceCosineExample_raw_right
#print axioms PaperFormalization.Manuscript.varianceCosineExample_raw_right
#check PaperFormalization.Manuscript.varianceCosineExample_characteristic_branch
#print axioms PaperFormalization.Manuscript.varianceCosineExample_characteristic_branch
#check PaperFormalization.Manuscript.varianceCosineExample_population_right
#print axioms PaperFormalization.Manuscript.varianceCosineExample_population_right
#check PaperFormalization.Manuscript.varianceCosineExample_population_pre
#print axioms PaperFormalization.Manuscript.varianceCosineExample_population_pre
#check PaperFormalization.Manuscript.varianceCosineExample_curvature_identification
#print axioms PaperFormalization.Manuscript.varianceCosineExample_curvature_identification
#check PaperFormalization.Manuscript.varianceCosineExample_pre_kernel
#print axioms PaperFormalization.Manuscript.varianceCosineExample_pre_kernel
#check PaperFormalization.Manuscript.varianceCosineExample_raw_schedule
#print axioms PaperFormalization.Manuscript.varianceCosineExample_raw_schedule
#check PaperFormalization.Manuscript.varianceCosineExample_first_moments
#print axioms PaperFormalization.Manuscript.varianceCosineExample_first_moments
#check PaperFormalization.Manuscript.varianceCosineExample_branch_lipschitz
#print axioms PaperFormalization.Manuscript.varianceCosineExample_branch_lipschitz
#check PaperFormalization.Manuscript.varianceCosineExample_population_ode
#print axioms PaperFormalization.Manuscript.varianceCosineExample_population_ode
#check PaperFormalization.Manuscript.varianceCosineExample_field_zero
#print axioms PaperFormalization.Manuscript.varianceCosineExample_field_zero
#check PaperFormalization.Manuscript.exists_varianceCosineExample_characteristic
#print axioms PaperFormalization.Manuscript.exists_varianceCosineExample_characteristic
#check PaperFormalization.Manuscript.varianceCosineExampleSourceRadius
#print axioms PaperFormalization.Manuscript.varianceCosineExampleSourceRadius
#check PaperFormalization.Manuscript.varianceCosineExamplePopulationScale
#print axioms PaperFormalization.Manuscript.varianceCosineExamplePopulationScale
#check PaperFormalization.Manuscript.varianceCosineExampleEnvelope
#print axioms PaperFormalization.Manuscript.varianceCosineExampleEnvelope
#check PaperFormalization.Manuscript.varianceCosineExampleEnvelope_eq
#print axioms PaperFormalization.Manuscript.varianceCosineExampleEnvelope_eq
#check PaperFormalization.Manuscript.varianceCosineExampleDelta
#print axioms PaperFormalization.Manuscript.varianceCosineExampleDelta
#check PaperFormalization.Manuscript.varianceCosineExampleDeltaTilde
#print axioms PaperFormalization.Manuscript.varianceCosineExampleDeltaTilde
#check PaperFormalization.Manuscript.varianceCosineExampleA
#print axioms PaperFormalization.Manuscript.varianceCosineExampleA
#check PaperFormalization.Manuscript.varianceCosineExampleLambda
#print axioms PaperFormalization.Manuscript.varianceCosineExampleLambda
#check PaperFormalization.Manuscript.varianceCosineExampleCD
#print axioms PaperFormalization.Manuscript.varianceCosineExampleCD
#check PaperFormalization.Manuscript.varianceCosineExample_smallness_of_response
#print axioms PaperFormalization.Manuscript.varianceCosineExample_smallness_of_response
#check PaperFormalization.Manuscript.varianceCosineExampleEscape
#print axioms PaperFormalization.Manuscript.varianceCosineExampleEscape
#check PaperFormalization.Manuscript.varianceCosineExampleEscape_measurable
#print axioms PaperFormalization.Manuscript.varianceCosineExampleEscape_measurable
#check PaperFormalization.Manuscript.varianceCosineExampleEscape_budget
#print axioms PaperFormalization.Manuscript.varianceCosineExampleEscape_budget
#check PaperFormalization.Manuscript.varianceCosineExample_land
#print axioms PaperFormalization.Manuscript.varianceCosineExample_land
#check PaperFormalization.Manuscript.varianceCosineExampleRadius_bounds
#print axioms PaperFormalization.Manuscript.varianceCosineExampleRadius_bounds
#check PaperFormalization.Manuscript.varianceCosineExample_jump_response
#print axioms PaperFormalization.Manuscript.varianceCosineExample_jump_response
#check PaperFormalization.Manuscript.varianceCosineExample_response_scale
#print axioms PaperFormalization.Manuscript.varianceCosineExample_response_scale
#check PaperFormalization.Manuscript.varianceCosineExample_responses_uniform
#print axioms PaperFormalization.Manuscript.varianceCosineExample_responses_uniform
#check PaperFormalization.Manuscript.varianceCosineExample_controlled_response
#print axioms PaperFormalization.Manuscript.varianceCosineExample_controlled_response
#check PaperFormalization.Manuscript.varianceCosineExample_stable_on_escape
#print axioms PaperFormalization.Manuscript.varianceCosineExample_stable_on_escape
#check PaperFormalization.Manuscript.varianceCosineExample_wait_identity
#print axioms PaperFormalization.Manuscript.varianceCosineExample_wait_identity
#check PaperFormalization.Manuscript.varianceCosineExample_wait_le_log
#print axioms PaperFormalization.Manuscript.varianceCosineExample_wait_le_log
#check PaperFormalization.Manuscript.varianceCosineExample_log_after_recovery
#print axioms PaperFormalization.Manuscript.varianceCosineExample_log_after_recovery
#check PaperFormalization.Manuscript.varianceCosineExample_responses_late
#print axioms PaperFormalization.Manuscript.varianceCosineExample_responses_late
#check PaperFormalization.Manuscript.varianceCosineExample_population_late
#print axioms PaperFormalization.Manuscript.varianceCosineExample_population_late
#check PaperFormalization.Manuscript.VarianceCosineExampleJointRate
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleJointRate
#check PaperFormalization.Manuscript.varianceCosineExample_source_joint_transport
#print axioms PaperFormalization.Manuscript.varianceCosineExample_source_joint_transport
#check PaperFormalization.Manuscript.VarianceCosineExampleTrackingConclusion
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleTrackingConclusion
#check PaperFormalization.Manuscript.varianceCosineExample_source_tracking_transport
#print axioms PaperFormalization.Manuscript.varianceCosineExample_source_tracking_transport
#check PaperFormalization.Manuscript.exists_varianceCosineExample_comparison_event
#print axioms PaperFormalization.Manuscript.exists_varianceCosineExample_comparison_event
#check PaperFormalization.Manuscript.varianceCosineExampleAdmissionScale
#print axioms PaperFormalization.Manuscript.varianceCosineExampleAdmissionScale
#check PaperFormalization.Manuscript.varianceCosineExampleAdmission
#print axioms PaperFormalization.Manuscript.varianceCosineExampleAdmission
#check PaperFormalization.Manuscript.varianceCosineExample_admission_root
#print axioms PaperFormalization.Manuscript.varianceCosineExample_admission_root
#check PaperFormalization.Manuscript.varianceCosineExample_admission_spec
#print axioms PaperFormalization.Manuscript.varianceCosineExample_admission_spec
#check PaperFormalization.Manuscript.varianceCosineExampleExponent
#print axioms PaperFormalization.Manuscript.varianceCosineExampleExponent
#check PaperFormalization.Manuscript.varianceCosineExampleExponent_pos
#print axioms PaperFormalization.Manuscript.varianceCosineExampleExponent_pos
#check PaperFormalization.Manuscript.varianceCosineExampleRateCutoff
#print axioms PaperFormalization.Manuscript.varianceCosineExampleRateCutoff
#check PaperFormalization.Manuscript.varianceCosineExampleRateMultiplier
#print axioms PaperFormalization.Manuscript.varianceCosineExampleRateMultiplier
#check PaperFormalization.Manuscript.varianceCosineExampleRateConstant
#print axioms PaperFormalization.Manuscript.varianceCosineExampleRateConstant
#check PaperFormalization.Manuscript.varianceCosineExampleRateMultiplier_pos
#print axioms PaperFormalization.Manuscript.varianceCosineExampleRateMultiplier_pos
#check PaperFormalization.Manuscript.varianceCosineExampleRateConstant_pos
#print axioms PaperFormalization.Manuscript.varianceCosineExampleRateConstant_pos
#check PaperFormalization.Manuscript.varianceCosinePairFunctionalError
#print axioms PaperFormalization.Manuscript.varianceCosinePairFunctionalError
#check PaperFormalization.Manuscript.varianceCosineEmpiricalExcess
#print axioms PaperFormalization.Manuscript.varianceCosineEmpiricalExcess
#check PaperFormalization.Manuscript.varianceCosineExampleError
#print axioms PaperFormalization.Manuscript.varianceCosineExampleError
#check PaperFormalization.Manuscript.varianceCosineExampleLateError
#print axioms PaperFormalization.Manuscript.varianceCosineExampleLateError
#check PaperFormalization.Manuscript.varianceCosineExamplePreError
#print axioms PaperFormalization.Manuscript.varianceCosineExamplePreError
#check PaperFormalization.Manuscript.varianceCosineExamplePopulation_probability
#print axioms PaperFormalization.Manuscript.varianceCosineExamplePopulation_probability
#check PaperFormalization.Manuscript.varianceCosineExamplePrePopulation_probability
#print axioms PaperFormalization.Manuscript.varianceCosineExamplePrePopulation_probability
#check PaperFormalization.Manuscript.varianceCosineEmpirical_memLp
#print axioms PaperFormalization.Manuscript.varianceCosineEmpirical_memLp
#check PaperFormalization.Manuscript.varianceCosineEmpirical_objective
#print axioms PaperFormalization.Manuscript.varianceCosineEmpirical_objective
#check PaperFormalization.Manuscript.varianceCosine_functional_transfer
#print axioms PaperFormalization.Manuscript.varianceCosine_functional_transfer
#check PaperFormalization.Manuscript.varianceCosineExamplePopulation_memLp
#print axioms PaperFormalization.Manuscript.varianceCosineExamplePopulation_memLp
#check PaperFormalization.Manuscript.varianceCosineExampleError_nonneg
#print axioms PaperFormalization.Manuscript.varianceCosineExampleError_nonneg
#check PaperFormalization.Manuscript.varianceCosineExample_xi_power
#print axioms PaperFormalization.Manuscript.varianceCosineExample_xi_power
#check PaperFormalization.Manuscript.varianceCosineExample_whole_power
#print axioms PaperFormalization.Manuscript.varianceCosineExample_whole_power
#check PaperFormalization.Manuscript.varianceCosineExample_late_profile
#print axioms PaperFormalization.Manuscript.varianceCosineExample_late_profile
#check PaperFormalization.Manuscript.varianceCosineExample_late_power
#print axioms PaperFormalization.Manuscript.varianceCosineExample_late_power
#check PaperFormalization.Manuscript.varianceCosineExample_rates_of_joint
#print axioms PaperFormalization.Manuscript.varianceCosineExample_rates_of_joint
#check PaperFormalization.Manuscript.VarianceCosineExamplePointwiseRates
#print axioms PaperFormalization.Manuscript.VarianceCosineExamplePointwiseRates
#check PaperFormalization.Manuscript.VarianceCosineExampleActualSmallness
#print axioms PaperFormalization.Manuscript.VarianceCosineExampleActualSmallness
#check PaperFormalization.Manuscript.varianceCosineExample_intersection_budget
#print axioms PaperFormalization.Manuscript.varianceCosineExample_intersection_budget
#check PaperFormalization.Manuscript.exists_varianceCosineExample_common_event
#print axioms PaperFormalization.Manuscript.exists_varianceCosineExample_common_event
#check PaperFormalization.Manuscript.varianceCosineExampleGood
#print axioms PaperFormalization.Manuscript.varianceCosineExampleGood
#check PaperFormalization.Manuscript.varianceCosineExampleGood_measurable
#print axioms PaperFormalization.Manuscript.varianceCosineExampleGood_measurable
#check PaperFormalization.Manuscript.varianceCosineExampleGood_probability
#print axioms PaperFormalization.Manuscript.varianceCosineExampleGood_probability
#check PaperFormalization.Manuscript.varianceCosineExampleGood_rates
#print axioms PaperFormalization.Manuscript.varianceCosineExampleGood_rates
#check PaperFormalization.Manuscript.varianceCosineExampleGood_tracking
#print axioms PaperFormalization.Manuscript.varianceCosineExampleGood_tracking
#check PaperFormalization.Manuscript.varianceCosineExample_objective_integrability
#print axioms PaperFormalization.Manuscript.varianceCosineExample_objective_integrability
#check PaperFormalization.Manuscript.varianceCosineExampleGood_probability_real
#print axioms PaperFormalization.Manuscript.varianceCosineExampleGood_probability_real
#check PaperFormalization.Manuscript.varianceCosineExampleGood_suprema
#print axioms PaperFormalization.Manuscript.varianceCosineExampleGood_suprema
#check PaperFormalization.Manuscript.varianceCosine_growing_example
#print axioms PaperFormalization.Manuscript.varianceCosine_growing_example
#check PaperFormalization.Manuscript.varianceCosine_printed_proposition
#print axioms PaperFormalization.Manuscript.varianceCosine_printed_proposition
#check PaperFormalization.Manuscript.varianceCosineExampleGood_zero_envelope
#print axioms PaperFormalization.Manuscript.varianceCosineExampleGood_zero_envelope
#check PaperFormalization.Manuscript.varianceCosineExample_failure_majorant_tendsto_zero
#print axioms PaperFormalization.Manuscript.varianceCosineExample_failure_majorant_tendsto_zero
#check PaperFormalization.Manuscript.varianceCosineExample_whole_majorant_tendsto_zero
#print axioms PaperFormalization.Manuscript.varianceCosineExample_whole_majorant_tendsto_zero
#check PaperFormalization.Manuscript.varianceCosineExample_late_majorant_tendsto_zero
#print axioms PaperFormalization.Manuscript.varianceCosineExample_late_majorant_tendsto_zero
#check PaperFormalization.Manuscript.varianceCosineExampleGood_complement_tendsto_zero
#print axioms PaperFormalization.Manuscript.varianceCosineExampleGood_complement_tendsto_zero
