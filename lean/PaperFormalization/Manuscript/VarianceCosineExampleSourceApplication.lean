import PaperFormalization.Manuscript.VarianceCosineExampleResponses

/-! # Apply the verified M13T theorem to the actual one-jump example
M13w verified implementation; source correspondence and axiom audit passed. This file makes the full source theorem call.
All stochastic inputs come from the U constructors; V supplies the response
restriction later. No compatible-view, residual, smallness or rate hypothesis
is added to the example's input parameters.
-/
open MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology ProbabilityTheory Matrix.Norms.Frobenius
namespace PaperFormalization.Manuscript
open Continuous
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 18
set_option maxHeartbeats 16000000
attribute [local instance] sourceGramMeasurableMatrix sourceGramBorelMatrix

/-- Right and true old-side rate, retaining the uncoarsened response profile. -/
def VarianceCosineExampleJointRate (P : VarianceCosineExampleParameters) {N : Nat}
    (mu0 : Measure VarianceCosinePoint) (T : Real) (w : VarianceCosineCouplingSpace N)
    (epsilon M : Real) : Prop :=
  (forall t, t ∈ Icc 0 T ->
    Integrable varianceCosineEncodedFeature (varianceCosineExamplePopulation P mu0 T w t) ∧
    max (norm ((varianceCosineExamplePair P T w t).1-(varianceCosineExamplePair P T w t).2)/Real.sqrt N)
      (sourceObjectiveError varianceCosineEncodedFeature (varianceCosineObjective P.a P.beta)
        (varianceCosineExamplePopulation P mu0 T w t) (varianceCosineExamplePair P T w t).1) <=
      M*(sourceMainXi N T (varianceCosineExampleConfidence N))^epsilon*
        sourceAsymptoticProfile N 1 T (varianceCosineRightCurvature P.a P.beta P.tau P.eta T w.2.1)
          (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta) t) ∧
  (Integrable varianceCosineEncodedFeature (varianceCosineExamplePrePopulation P mu0) ∧
    max (norm ((varianceCosineModelBranches P.a P.beta P.tau P.eta T w 0 P.tau).1-
      (varianceCosineModelBranches P.a P.beta P.tau P.eta T w 0 P.tau).2)/Real.sqrt N)
      (sourceObjectiveError varianceCosineEncodedFeature (varianceCosineObjective P.a P.beta)
        (varianceCosineExamplePrePopulation P mu0)
        (varianceCosineModelBranches P.a P.beta P.tau P.eta T w 0 P.tau).1) <=
      M*(sourceMainXi N T (varianceCosineExampleConfidence N))^epsilon*
        sourceAsymptoticProfile N 0 T (varianceCosineRightCurvature P.a P.beta P.tau P.eta T w.2.1)
          (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta) P.tau)

/-- The scalar kappa used here is IDENTIFIED with the original sampled full
Hessian; the reference sample mean is not substituted for the population mean. -/
theorem varianceCosineExample_source_joint_transport
    (P : VarianceCosineExampleParameters) {N : Nat} (hN : 2<=N)
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius) (hm : varianceCosineMean mu0=0)
    (T : Real) (hT : P.tau<=T) (z : VarianceCosineExampleTower N) (epsilon M : Real) :
    let branches := varianceCosineExampleCanonicalBranch P mu0 (by omega) T hT
    let paths := varianceCosineExampleCanonicalRight P mu0 (by omega) T hT
    let Z := varianceCosineExampleCharacteristic P T z
    let law := fun t => mu0.map (fun u => sourceGlue (varianceCosineTimes P.tau) 1 (fun k => Z k u) t)
    let preLaw := fun k => mu0.map (fun u => Z k u (varianceCosineTimes P.tau (k+1)))
    let kappa := fun t => rayleighInf (sampledMomentHessian varianceCosineEncodedFeature
      (varianceCosineObjective P.a P.beta) (integral (law t) varianceCosineEncodedFeature) (paths z t).2)
    SourceJointRateConclusion varianceCosineEncodedFeature (varianceCosineObjective P.a P.beta)
      law preLaw (sourceGlue (varianceCosineTimes P.tau) 1 (varianceCosineExampleRawX P T z))
      (fun t => (paths z t).2)
      (fun k => varianceCosineExampleRawX P T z k (varianceCosineTimes P.tau (k+1)))
      (fun k => (branches z k (varianceCosineTimes P.tau (k+1))).2)
      kappa (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta) 1 T
      (varianceCosineExampleConfidence N) epsilon M ->
    VarianceCosineExampleJointRate P mu0 T (varianceCosineTowerCoordinates z) epsilon M := by
  dsimp only
  intro hJoint
  have hkappa := funext (varianceCosineExample_curvature_identification P hN mu0 hU hm T hT z)
  rw [hkappa] at hJoint
  constructor
  . intro t ht
    have h := hJoint.1 t ht
    simpa only [varianceCosineExample_population_right,varianceCosineExample_raw_right,
      varianceCosineExample_reference_right] using h
  . have h := hJoint.2 0 (by omega)
    simpa only [varianceCosineTimes,if_neg (by omega : (0+1:Nat)≠0),
      varianceCosineExample_population_pre,varianceCosineExampleRawX,
      varianceCosineExample_reference_branch P mu0 (by omega) T hT z 0 (by omega)] using h

/-- Retain the exact finite-schedule bounds and both zero-envelope implications
on the original right paths and the true old trace. The scales are the GitHub
M13W scales; no definitions or constants from the comparison-only ZIP are used. -/
def VarianceCosineExampleTrackingConclusion (P : VarianceCosineExampleParameters)
    {N : Nat} (w : VarianceCosineCouplingSpace N) : Prop :=
  let T := varianceCosineExampleHorizon N
  let pair := varianceCosineExamplePair P T w
  let pre := varianceCosineModelBranches P.a P.beta P.tau P.eta T w 0 P.tau
  SourceTrackingConclusion (fun t => (pair t).1) (fun t => (pair t).2)
    (fun _ => pre.1) (fun _ => pre.2)
    (varianceCosineRightCurvature P.a P.beta P.tau P.eta T w.2.1)
    (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta) 1 T
    (varianceCosineExampleDelta P N) (varianceCosineExampleDeltaTilde P N)
    (varianceCosineExampleA P N)

/-- Transfer the existing M13T tracking output, including its two exact zero
cases, through the same pointwise identities used for the rate output. -/
theorem varianceCosineExample_source_tracking_transport
    (P : VarianceCosineExampleParameters) {N : Nat} (hN : 2<=N)
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius) (hm : varianceCosineMean mu0=0)
    (hT : P.tau<=varianceCosineExampleHorizon N) (z : VarianceCosineExampleTower N) :
    let T := varianceCosineExampleHorizon N
    let branches := varianceCosineExampleCanonicalBranch P mu0 (by omega) T hT
    let paths := varianceCosineExampleCanonicalRight P mu0 (by omega) T hT
    let Z := varianceCosineExampleCharacteristic P T z
    let law := fun t => mu0.map (fun u => sourceGlue (varianceCosineTimes P.tau) 1 (fun k => Z k u) t)
    let kappa := fun t => rayleighInf (sampledMomentHessian varianceCosineEncodedFeature
      (varianceCosineObjective P.a P.beta) (integral (law t) varianceCosineEncodedFeature) (paths z t).2)
    SourceTrackingConclusion
      (sourceGlue (varianceCosineTimes P.tau) 1 (varianceCosineExampleRawX P T z))
      (fun t => (paths z t).2)
      (fun k => varianceCosineExampleRawX P T z k (varianceCosineTimes P.tau (k+1)))
      (fun k => (branches z k (varianceCosineTimes P.tau (k+1))).2)
      kappa (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta) 1 T
      (varianceCosineExampleDelta P N) (varianceCosineExampleDeltaTilde P N)
      (varianceCosineExampleA P N) ->
    VarianceCosineExampleTrackingConclusion P (varianceCosineTowerCoordinates z) := by
  dsimp only
  intro htr
  let T := varianceCosineExampleHorizon N
  have hkappa := funext (varianceCosineExample_curvature_identification P hN mu0 hU hm T hT z)
  have hx := funext (varianceCosineExample_raw_right P T z)
  have hy := funext (varianceCosineExample_reference_right P mu0 (by omega) T hT z)
  rw [hkappa,hx,hy] at htr
  refine ⟨htr.1,htr.2.1,?_,?_⟩
  · intro k hk
    have hk0 : k=0 := by omega
    subst k
    simpa only [varianceCosineTimes,if_neg (by omega : (0+1:Nat)≠0),
      varianceCosineExampleRawX,
      varianceCosineExample_reference_branch P mu0 (by omega) (varianceCosineExampleHorizon N) hT z 0 (by omega)] using
      htr.2.2.1 0 (by omega)
  · intro hz k hk
    have hk0 : k=0 := by omega
    subst k
    simpa only [varianceCosineTimes,if_neg (by omega : (0+1:Nat)≠0),
      varianceCosineExampleRawX,
      varianceCosineExample_reference_branch P mu0 (by omega) (varianceCosineExampleHorizon N) hT z 0 (by omega)] using
      htr.2.2.2 hz 0 (by omega)

/-- A single comparison event works for ALL positive exponents. Its law is
exactly the original U coupling law, not merely an isomorphic unnamed law. -/
theorem exists_varianceCosineExample_comparison_event
    (P : VarianceCosineExampleParameters) (N : Nat) (hN : 2<=N)
    (hT : P.tau<=varianceCosineExampleHorizon N)
    (hconf : (N:Real)^(-1:Real)<=varianceCosineExampleConfidence N)
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius) (hm : varianceCosineMean mu0=0) :
    ∃ Cmp : Set (VarianceCosineCouplingSpace N),
      MeasurableSet Cmp ∧ varianceCosineModelLaw N mu0 Cmpᶜ <=
        ENNReal.ofReal (17*varianceCosineExampleConfidence N/32) ∧
      forall w, w ∈ Cmp -> forall epsilon (he : 0<epsilon), (P.rateData epsilon he).val.2<=N ->
        SourceControlledResponse N 1 (varianceCosineExampleHorizon N) (1/16) P.controlledConstant
          (varianceCosineRightCurvature P.a P.beta P.tau P.eta (varianceCosineExampleHorizon N) w.2.1)
          (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta) ->
        VarianceCosineExampleTrackingConclusion P w ∧
        VarianceCosineExampleJointRate P mu0 (varianceCosineExampleHorizon N) w epsilon (P.rateData epsilon he).val.1 := by
  have hN0 : 0<N := by omega
  let T := varianceCosineExampleHorizon N
  let nu := varianceCosineOriginalLaw N mu0
  let flowY := varianceCosineFlowY P.a P.beta P.tau P.eta T
  let field := varianceCosineField P.a P.beta
  let initial := varianceCosineOriginalInitial (N := N)
  let innovation := varianceCosineOriginalInnovation (N := N)
  let XB := varianceCosineExampleRawX (N := N) P T
  let cert := varianceCosine_comparison_assumptions N hN0 mu0 P.a P.beta P.tau P.eta T P.radius
    P.a_pos P.beta_pos P.tau_pos P.eta_pos P.radius_nonneg hT hU hm
  obtain ⟨ Phi,hPhi,hVersion ⟩ := exists_varianceCosineExample_characteristic
    (P := P) (N := N) (mu0 := mu0) (T := T) (hT := hT) (hU := hU)
  have hp := varianceCosineExampleConfidence_bounds N hN0
  have hHorizon : T<=(N:Real)^(1/4-(1/16)-(1/16):Real) := by
    norm_num [T,varianceCosineExampleHorizon]
  have heta : forall n : Fin 1, 0<=varianceCosineAmplitudes P.eta n := by
    intro n; fin_cases n; exact P.eta_pos.le
  have hEta : forall n : Fin 1, varianceCosineAmplitudes P.eta n<=P.controlledConstant := by
    intro n; fin_cases n; exact P.eta_le_controlledConstant
  obtain ⟨ Good,hGood,hBudget,hStrict,hValid ⟩ :=
    exists_source_raw_growing_tracking_event
      1 1 1 2 0 2 P.momentScale P.thirdBound 1 1 1 (1/16) (1/16) P.controlledConstant
      varianceCosineFeature
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) P.momentScale_pos (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) P.controlledConstant_pos.le
      cert.featureC2 cert.featureGrowthBound cert.thirdFeatureExists cert.thirdFeatureGrowth
      (varianceCosineObjective P.a P.beta) Set.univ isOpen_univ (varianceCosineObjective_domains 2)
      cert.objectiveC3.contDiffOn (fun z _ => cert.thirdObjective z)
      hN0 (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta) 1 T P.speed
      (by simp [varianceCosineTimes]) (varianceCosineExample_strict_times P)
      (by simpa [varianceCosineTimes] using hT)
      (varianceCosineExampleConfidence N) hp.1 hp.2 (by norm_num) hHorizon hconf
      (varianceCosineExampleEnvelope P N) (varianceCosineExampleEnvelope_eq P N hN0)
      nu mu0 flowY field (varianceCosineFlowY_measurable P.a P.beta P.tau P.eta T)
      (varianceCosineField_measurable P.a P.beta) (varianceCosineFlowY_start P.a P.beta P.tau P.eta T)
      initial innovation varianceCosineOriginalInitial_measurable varianceCosineOriginalInnovation_measurable
      (varianceCosineOriginal_iid mu0) (varianceCosineOriginal_population_independent mu0)
      (varianceCosineOriginal_initial_law mu0) (fun _ : Fin 1 => gaussianReal 0 1) heta hEta
      (varianceCosineOriginal_fresh mu0) (varianceCosineOriginal_innovation_law mu0)
      Phi hPhi hVersion XB
      (varianceCosineExample_first_moments P mu0 hN0 T hT hU hm)
      (varianceCosineExample_branch_lipschitz P mu0 hN0 T hT hU hm)
      (Filter.Eventually.of_forall (varianceCosineExample_raw_schedule P mu0 hN0 T hT hU hm))
      (by
        apply Filter.Eventually.of_forall
        intro z k hk
        apply ae_restrict_of_forall_mem measurableSet_Ioo
        intro t ht
        exact varianceCosineExample_population_ode (P := P) (mu0 := mu0) (T := T)
          (hU := hU) (hm := hm) z.1 z.2 k hk t ht)
      (by
        intro n
        fin_cases n
        dsimp only
        apply Filter.Eventually.of_forall
        intro h
        rw [varianceCosineExample_pre_kernel P mu0 T (sourceHistoryPopulation 0) h]
        exact varianceCosineExample_field_zero (P := P) (mu0 := mu0) (hN := hN0)
          (hU := hU) (hm := hm) (sourceHistoryPopulation 0 h) _)
  let Cmp := varianceCosineTowerInverse ⁻¹' Good
  have hCmp : MeasurableSet Cmp := hGood.preimage varianceCosineTowerInverse_measurable
  have hinv := varianceCosineTowerInverse_preserving (N := N) mu0
  have hMeasure := congrArg (fun m : Measure (VarianceCosineExampleTower N) => m Goodᶜ) hinv.map_eq
  rw [Measure.map_apply hinv.measurable hGood.compl] at hMeasure
  have hB : varianceCosineModelLaw N mu0 Cmpᶜ <= ENNReal.ofReal (17*varianceCosineExampleConfidence N/32) := by
    change varianceCosineModelLaw N mu0 (varianceCosineTowerInverse ⁻¹' Good)ᶜ <= _
    rw [<- preimage_compl,hMeasure]
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    have hb0 : 0 <= 17*varianceCosineExampleConfidence N/32 := by
      nlinarith [hp.1]
    rw [ENNReal.toReal_ofReal hb0]
    exact hBudget
  refine ⟨ Cmp,hCmp,hB,?_ ⟩
  intro w hw epsilon he hcut hresp
  let z := varianceCosineTowerInverse w
  have hx : sourceGlue (varianceCosineTimes P.tau) 1 (XB z) =
      fun t => (varianceCosineExamplePair P T w t).1 := by
    funext t
    exact varianceCosineExample_raw_right P T z t
  have hy : (fun t => (varianceCosineExampleCanonicalRight P mu0 hN0 T hT z t).2) =
      fun t => (varianceCosineExamplePair P T w t).2 := by
    funext t
    exact varianceCosineExample_reference_right P mu0 hN0 T hT z t
  have hkappa := funext (varianceCosineExample_curvature_identification P hN mu0 hU hm T hT z)
  have hsp : SourceRightAntiSpikiness (sourceGlue (varianceCosineTimes P.tau) 1 (XB z))
      (fun t => (varianceCosineExampleCanonicalRight P mu0 hN0 T hT z t).2) T 1 := by
    rw [hx,hy]
    exact cert.antiSpikiness w
  have hresp' : SourceControlledResponse N 1 T (1/16) P.controlledConstant
      (fun t => rayleighInf (sampledMomentHessian varianceCosineEncodedFeature (varianceCosineObjective P.a P.beta)
        (integral (mu0.map (fun u => sourceGlue (varianceCosineTimes P.tau) 1
          (fun k => varianceCosineExampleCharacteristic P T z k u) t)) varianceCosineEncodedFeature)
        (varianceCosineExampleCanonicalRight P mu0 hN0 T hT z t).2))
      (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta) := by
    rw [hkappa]
    exact hresp
  have hresult := (hValid z hw).2 epsilon he hcut hsp hresp'
  exact ⟨varianceCosineExample_source_tracking_transport P hN mu0 hU hm hT z hresult.1,
    varianceCosineExample_source_joint_transport P hN mu0 hU hm T hT z epsilon
      (P.rateData epsilon he).val.1 hresult.2.2⟩

end PaperFormalization.Manuscript
