import PaperFormalization.Manuscript.VarianceCosineExamplePathIdentities

/-! # Discharge the actual M13T stochastic and raw-solution inputs
M13w verified implementation; source correspondence and axiom audit passed. None of the input lemmas accepts a desired
concentration, rate, moment or model-equality conclusion as an assumption.
-/
open MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology ProbabilityTheory Matrix.Norms.Frobenius
namespace PaperFormalization.Manuscript
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
set_option maxHeartbeats 4000000
attribute [local instance] sourceGramMeasurableMatrix sourceGramBorelMatrix


theorem varianceCosineExample_raw_schedule
    (P : VarianceCosineExampleParameters) {N : Nat}
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (hN : 0<N) (T : Real) (hT : P.tau<=T)
    (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius) (hm : varianceCosineMean mu0=0) (z : VarianceCosineExampleTower N) :
    SourceRawEmpiricalSchedule mu0 1 2 2 varianceCosineFeature (varianceCosineObjective P.a P.beta)
      Set.univ isOpen_univ (varianceCosineObjective_domains 2)
      ((varianceCosineObjective_contDiff P.a P.beta).of_le (by norm_num)).contDiffOn hN
      (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta)
      (varianceCosineFlowY P.a P.beta P.tau P.eta T) (varianceCosineField P.a P.beta) 1 T
      (sourceTowerPacked varianceCosineOriginalInnovation 1 z)
      (varianceCosineOriginalInitial (sourceAuxiliaryOriginal 1 z))
      (varianceCosineExampleRawX P T z) := by
  rw [varianceCosineExample_packed]
  exact varianceCosine_raw_empirical_schedule hN mu0 P.radius P.radius_nonneg hU hm
    P.a P.beta P.tau P.eta T P.beta_pos.le P.tau_pos.le hT (varianceCosineTowerCoordinates z)

theorem varianceCosineExample_first_moments
    (P : VarianceCosineExampleParameters) {N : Nat}
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (hN : 0<N) (T : Real) (hT : P.tau<=T)
    (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius) (hm : varianceCosineMean mu0=0) (cloud : Fin 2) (t : Real) (ht : t ∈ Icc 0 T) :
    (varianceCosineExampleTowerLaw N mu0).map (fun z => sourcePairCloud cloud
      (sourceGlue (varianceCosineTimes P.tau) 1 (varianceCosineExampleRawX P T z) t,
       (varianceCosineExampleCanonicalRight P mu0 hN T hT z t).2) ⟨ 0,hN ⟩)
      ∈ sourceMomentClass 2 P.momentScale := by
  let cert := varianceCosine_comparison_assumptions N hN mu0 P.a P.beta P.tau P.eta T P.radius
    P.a_pos P.beta_pos P.tau_pos P.eta_pos P.radius_nonneg hT hU hm
  have hv := varianceCosine_comparison_right_moments N hN mu0 P.a P.beta P.tau P.eta T P.radius
    P.tau_pos.le hT (show 0<=varianceCosineSpeed P.a P.beta P.radius from P.speed.coe_nonneg)
    cert t ht ⟨ 0,hN ⟩
  simp_rw [varianceCosineExample_raw_right,varianceCosineExample_reference_right]
  let f := fun w : VarianceCosineCouplingSpace N =>
    sourcePairCloud cloud (varianceCosineExamplePair P T w t) ⟨ 0,hN ⟩
  have hf : Measurable f :=
    ((measurable_pi_apply (⟨ 0,hN ⟩ : Fin N)).comp (WithLp.measurable_ofLp 2 _)).comp
      ((sourcePairCloud_measurable cloud).comp (varianceCosineExamplePair_measurable P T t))
  change (varianceCosineExampleTowerLaw N mu0).map (fun z => f (varianceCosineTowerCoordinates z)) ∈ _
  unfold varianceCosineExampleTowerLaw varianceCosineOriginalLaw
  rw [varianceCosineTower_map (sourceInitialConfigurationLaw (N := N) mu0) f hf]
  fin_cases cloud
  . simpa [f,sourcePairCloud,varianceCosineExamplePair,
      VarianceCosineExampleParameters.momentScale,varianceCosineModelLaw] using hv.1
  . simpa [f,sourcePairCloud,varianceCosineExamplePair,
      VarianceCosineExampleParameters.momentScale,varianceCosineModelLaw] using hv.2

theorem varianceCosineExample_branch_lipschitz
    (P : VarianceCosineExampleParameters) {N : Nat}
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (hN : 0<N) (T : Real) (hT : P.tau<=T)
    (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius) (hm : varianceCosineMean mu0=0) :
    ∀ᵐ z ∂ varianceCosineExampleTowerLaw N mu0, forall (cloud : Fin 2) (i : Fin N) (j : Fin 2),
      LipschitzOnWith P.speed (fun t => sourcePairCloud cloud
        (varianceCosineExampleRawX P T z j.val t,
          (varianceCosineExampleCanonicalBranch P mu0 hN T hT z j.val t).2) i)
        (Icc (sourceScheduleLeft (varianceCosineTimes P.tau) 1 j)
          (sourceScheduleRight (varianceCosineTimes P.tau) 1 T j)) := by
  let cert := varianceCosine_comparison_assumptions N hN mu0 P.a P.beta P.tau P.eta T P.radius
    P.a_pos P.beta_pos P.tau_pos P.eta_pos P.radius_nonneg hT hU hm
  have hp := (varianceCosineTower_preserving (sourceInitialConfigurationLaw (N := N) mu0)).quasiMeasurePreserving.ae
    cert.branchLipschitz
  filter_upwards [hp] with z hz
  intro cloud i j
  have hj : j.val<=1 := by omega
  simp_rw [varianceCosineExample_reference_branch P mu0 hN T hT z j.val hj]
  fin_cases cloud
  . have hh := (hz j.val i).1
    fin_cases j <;> simpa [sourcePairCloud,varianceCosineExampleRawX,sourceScheduleLeft,
      sourceScheduleRight,varianceCosineTimes,VarianceCosineExampleParameters.speed] using hh
  . have hh := (hz j.val i).2
    fin_cases j <;> simpa [sourcePairCloud,varianceCosineExampleRawX,sourceScheduleLeft,
      sourceScheduleRight,varianceCosineTimes,VarianceCosineExampleParameters.speed] using hh

/-- The source population ODE holds pointwise, before any AE packaging. -/
theorem varianceCosineExample_population_ode
    (P : VarianceCosineExampleParameters)
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0] (T : Real)
    (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius) (hm : varianceCosineMean mu0=0)
    (e : Nat -> Real) (u : VarianceCosinePoint) (k : Nat) (hk : k<=1) (t : Real)
    (ht : t ∈ Ioo (varianceCosineTimes P.tau k)
      (if k<1 then varianceCosineTimes P.tau (k+1) else T)) :
    HasDerivAt (sourceOriginalCharacteristic (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta)
      (varianceCosineFlowY P.a P.beta P.tau P.eta T) (varianceCosineField P.a P.beta) k e u)
      (momentGradientField (fderiv Real varianceCosineEncodedFeature)
        (gradient (varianceCosineObjective P.a P.beta))
        (integral (mu0.map (fun x => sourceOriginalCharacteristic (varianceCosineTimes P.tau)
          (varianceCosineAmplitudes P.eta) (varianceCosineFlowY P.a P.beta P.tau P.eta T)
          (varianceCosineField P.a P.beta) k e x t)) varianceCosineEncodedFeature,
         sourceOriginalCharacteristic (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta)
          (varianceCosineFlowY P.a P.beta P.tau P.eta T) (varianceCosineField P.a P.beta) k e u t)) t := by
  have ht' : t ∈ Ioo (if k=0 then 0 else P.tau) (if k=0 then P.tau else T) := by
    interval_cases k <;> simpa [varianceCosineTimes] using ht
  have hfun := funext (varianceCosineOriginalCharacteristic_formula P T e k hk u)
  rw [hfun]
  simp_rw [varianceCosineOriginalCharacteristic_formula P T e k hk]
  exact varianceCosine_reference_source_ode mu0 P.radius P.radius_nonneg hU hm
    P.a P.beta P.tau P.eta T (e 0) P.beta_pos.le P.tau_pos.le k u t ht'

/-- Fresh-field Gaussian specification for every cloud and every empty prefix.
The matrix is the genuine source Gram covariance under the true pre-law. -/
theorem varianceCosineExample_field_zero
    (P : VarianceCosineExampleParameters) {N : Nat}
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0] (hN : 0<N)
    (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius) (hm : varianceCosineMean mu0=0) (past : Fin 0 -> Real) (Y : SourceFiniteConfiguration N 1) :
    (gaussianReal 0 1).map (sourceRawFieldVector (varianceCosineField P.a P.beta) 0 past Y) =
      multivariateGaussian 0 (populationGramCovariance (varianceCosineExamplePrePopulation P mu0)
        (fun x => stackedKernelMatrix (fun i => actualMomentKernelMatrix varianceCosineEncodedFeature
          (varianceCosineObjective P.a P.beta)
          (integral (varianceCosineExamplePrePopulation P mu0) varianceCosineEncodedFeature) (Y i) x))) := by
  exact varianceCosinePopulation_field_spec hN mu0 P.radius P.radius_nonneg hU hm
    P.a P.beta 0 (Real.exp (-P.a*P.tau)) Y

/-- A measurable common characteristic with the EXACT environment law in the
M13T theorem. No equality of distinct conditioned laws is postulated. -/
theorem exists_varianceCosineExample_characteristic
    (P : VarianceCosineExampleParameters) (N : Nat)
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0] (T : Real) (hT : P.tau<=T)
    (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius) :
    ∃ Phi : (Nat -> Real) -> VarianceCosinePoint ->
      SourceReferencePathSpace 1 1 (sourceScheduleLeft (varianceCosineTimes P.tau) 1)
        (sourceScheduleRight (varianceCosineTimes P.tau) 1 T),
      Measurable (fun z : (Nat -> Real) × VarianceCosinePoint => Phi z.1 z.2) ∧
      ∀ᵐ z ∂ ((varianceCosineOriginalLaw N mu0).map
        (fun o n => varianceCosineOriginalInnovation n o)).prod mu0,
        forall j t, t ∈ Icc (sourceScheduleLeft (varianceCosineTimes P.tau) 1 j)
          (sourceScheduleRight (varianceCosineTimes P.tau) 1 T j) ->
          sourceReferencePathEval (Phi z.1 z.2) j t =
            sourceOriginalCharacteristic (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta)
              (varianceCosineFlowY P.a P.beta P.tau P.eta T) (varianceCosineField P.a P.beta) j.val z.1 z.2 t := by
  rw [varianceCosineOriginal_environment_law mu0]
  exact exists_varianceCosine_common_characteristic mu0 P.radius P.radius_nonneg hU
    P.a P.beta P.tau P.eta T P.a_pos.le P.beta_pos.le P.tau_pos hT

end PaperFormalization.Manuscript
