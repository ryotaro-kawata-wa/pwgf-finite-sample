import PaperFormalization.Manuscript.VarianceCosineExampleSourceData

/-! # Pointwise identification with the raw paths passed to M13T
M13w verified implementation; source correspondence and axiom audit passed. The reference law is the original affine law.
All identities are established before any probability event is formed.
-/
open MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology BigOperators
namespace PaperFormalization.Manuscript
open Continuous
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 14

variable (P : VarianceCosineExampleParameters)

theorem varianceCosineExample_strict_times :
    forall k : Nat, k<1 -> varianceCosineTimes P.tau k < varianceCosineTimes P.tau (k+1) := by
  intro k hk
  have he : k=0 := by omega
  subst k
  simpa [varianceCosineTimes] using P.tau_pos

noncomputable def varianceCosineExampleCanonicalFlow (N : Nat) (T : Real) (hT : P.tau<=T) :=
  sourceCanonicalEmpiricalFlow (N := N) 1 2 varianceCosineFeature (varianceCosineObjective P.a P.beta)
    (varianceCosineTimes P.tau) 1 T (varianceCosineExample_strict_times P)
    (by simpa [varianceCosineTimes] using hT)

noncomputable def varianceCosineExamplePost {N : Nat}
    (mu0 : Measure VarianceCosinePoint) (hN : 0<N) (T : Real) (hT : P.tau<=T) :=
  sourceActualFinitePost mu0 1 2 2 varianceCosineFeature (varianceCosineObjective P.a P.beta)
    Set.univ isOpen_univ (varianceCosineObjective_domains 2)
    ((varianceCosineObjective_contDiff P.a P.beta).of_le (by norm_num)).contDiffOn hN
    (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta)
    (varianceCosineExampleCanonicalFlow P N T hT)
    (varianceCosineFlowY P.a P.beta P.tau P.eta T) (varianceCosineField P.a P.beta)

noncomputable def varianceCosineExampleCanonicalBranch {N : Nat}
    (mu0 : Measure VarianceCosinePoint) (hN : 0<N) (T : Real) (hT : P.tau<=T) :=
  sourceFinalBranch (varianceCosineExamplePost P mu0 hN T hT)
    (varianceCosineExampleCanonicalFlow P N T hT)
    (varianceCosineFlowY P.a P.beta P.tau P.eta T)
    (varianceCosineOriginalInitial (N := N)) varianceCosineOriginalInnovation 1

noncomputable def varianceCosineExampleCanonicalRight {N : Nat}
    (mu0 : Measure VarianceCosinePoint) (hN : 0<N) (T : Real) (hT : P.tau<=T) :=
  sourceFinalRight (varianceCosineExamplePost P mu0 hN T hT)
    (varianceCosineExampleCanonicalFlow P N T hT)
    (varianceCosineFlowY P.a P.beta P.tau P.eta T) (varianceCosineTimes P.tau)
    (varianceCosineOriginalInitial (N := N)) varianceCosineOriginalInnovation 1

noncomputable def varianceCosineExamplePair {N : Nat} (T : Real)
    (w : VarianceCosineCouplingSpace N) (t : Real) :=
  varianceCosineModelBranches P.a P.beta P.tau P.eta T w (if t<P.tau then 0 else 1) t
noncomputable def varianceCosineExampleRawX {N : Nat} (T : Real)
    (z : VarianceCosineExampleTower N) (k : Nat) (t : Real) :=
  (varianceCosineModelBranches P.a P.beta P.tau P.eta T (varianceCosineTowerCoordinates z) k t).1
noncomputable def varianceCosineExamplePopulation {N : Nat}
    (mu0 : Measure VarianceCosinePoint) (T : Real) (w : VarianceCosineCouplingSpace N) (t : Real) :=
  varianceCosinePopulation mu0 (varianceCosineRightMean P.a P.beta P.tau P.eta T w.2.1 t)
    (Real.exp (-P.a*t))
noncomputable def varianceCosineExamplePrePopulation
    (mu0 : Measure VarianceCosinePoint) := varianceCosinePopulation mu0 0 (Real.exp (-P.a*P.tau))
noncomputable def varianceCosineExampleCharacteristic {N : Nat} (T : Real)
    (z : VarianceCosineExampleTower N) :=
  sourceFiniteReferenceBranch (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta)
    (varianceCosineFlowY P.a P.beta P.tau P.eta T) (varianceCosineField P.a P.beta)
    1 (sourceTowerPacked varianceCosineOriginalInnovation 1 z)

theorem varianceCosineExampleModelBranches_measurable {N : Nat} (T : Real) (k : Nat) (t : Real) :
    Measurable (fun w : VarianceCosineCouplingSpace N => varianceCosineModelBranches
      P.a P.beta P.tau P.eta T w k t) := by
  change Measurable ((fun z : SourceFiniteConfiguration N 1 × (Real × Real) =>
    varianceCosinePairBranch P.a P.beta P.tau P.eta T z.1 z.2.1 z.2.2 k t) ∘
    (fun w : VarianceCosineCouplingSpace N =>
      (w.1, (w.2.1, varianceCosineCouplingZeta P.a P.beta P.tau w))))
  have hinput : Measurable (fun w : VarianceCosineCouplingSpace N =>
      (w.1, (w.2.1, varianceCosineCouplingZeta P.a P.beta P.tau w))) :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (varianceCosineCouplingZeta_measurable P.a P.beta P.tau))
  exact (varianceCosinePairBranch_measurable (N := N) P.a P.beta P.tau P.eta T k t).comp hinput

theorem varianceCosineExamplePair_measurable {N : Nat} (T : Real) (t : Real) :
    Measurable (fun w : VarianceCosineCouplingSpace N => varianceCosineExamplePair P T w t) :=
  varianceCosineExampleModelBranches_measurable P T _ t

theorem varianceCosineExample_reference_branch {N : Nat}
    (mu0 : Measure VarianceCosinePoint) (hN : 0<N) (T : Real) (hT : P.tau<=T)
    (z : VarianceCosineExampleTower N) (k : Nat) (hk : k<=1) (t : Real) :
    (varianceCosineExampleCanonicalBranch P mu0 hN T hT z k t).2 =
      (varianceCosineModelBranches P.a P.beta P.tau P.eta T
        (varianceCosineTowerCoordinates z) k t).2 := by
  ext i j
  have he := sourceFinalBranch_reference_original mu0 1 2 2 varianceCosineFeature
    (varianceCosineObjective P.a P.beta) Set.univ isOpen_univ (varianceCosineObjective_domains 2)
    ((varianceCosineObjective_contDiff P.a P.beta).of_le (by norm_num)).contDiffOn hN
    (varianceCosineTimes P.tau) (varianceCosineAmplitudes P.eta)
    (varianceCosineExampleCanonicalFlow P N T hT)
    (varianceCosineFlowY P.a P.beta P.tau P.eta T) (varianceCosineField P.a P.beta)
    varianceCosineOriginalInitial varianceCosineOriginalInnovation 1 k hk z t i
  rw [varianceCosineOriginalCharacteristic_formula P T _ k hk] at he
  exact congrArg (fun x : VarianceCosinePoint => x j) he

theorem varianceCosineExample_reference_right {N : Nat}
    (mu0 : Measure VarianceCosinePoint) (hN : 0<N) (T : Real) (hT : P.tau<=T)
    (z : VarianceCosineExampleTower N) (t : Real) :
    (varianceCosineExampleCanonicalRight P mu0 hN T hT z t).2 =
      (varianceCosineExamplePair P T (varianceCosineTowerCoordinates z) t).2 := by
  change (sourceGlue (varianceCosineTimes P.tau) 1
    (varianceCosineExampleCanonicalBranch P mu0 hN T hT z) t).2 = _
  rw [varianceCosineGlue_one]
  exact varianceCosineExample_reference_branch P mu0 hN T hT z _ (by split_ifs <;> omega) t

theorem varianceCosineExample_raw_right {N : Nat} (T : Real)
    (z : VarianceCosineExampleTower N) (t : Real) :
    sourceGlue (varianceCosineTimes P.tau) 1 (varianceCosineExampleRawX P T z) t =
      (varianceCosineExamplePair P T (varianceCosineTowerCoordinates z) t).1 := by
  rw [varianceCosineGlue_one]
  rfl

theorem varianceCosineExample_characteristic_branch {N : Nat} (T : Real)
    (z : VarianceCosineExampleTower N) (k : Nat) (hk : k<=1) (u : VarianceCosinePoint) (t : Real) :
    varianceCosineExampleCharacteristic P T z k u t =
      varianceCosineAffine (varianceCosineBranchMeanY P.a P.beta P.tau P.eta T
        (varianceCosineTowerCoordinates z).2.1 k t) (Real.exp (-P.a*t)) u := by
  rw [varianceCosineExampleCharacteristic,sourceFiniteReferenceBranch_original
    _ _ _ _ varianceCosineOriginalInnovation 1 k hk]
  exact varianceCosineOriginalCharacteristic_formula P T _ k hk u t

theorem varianceCosineExample_population_right {N : Nat}
    (mu0 : Measure VarianceCosinePoint) (T : Real) (z : VarianceCosineExampleTower N) (t : Real) :
    mu0.map (fun u => sourceGlue (varianceCosineTimes P.tau) 1
      (fun k => varianceCosineExampleCharacteristic P T z k u) t) =
      varianceCosineExamplePopulation P mu0 T (varianceCosineTowerCoordinates z) t := by
  congr 1
  funext u
  rw [varianceCosineGlue_one,varianceCosineExample_characteristic_branch P T z _
    (by split_ifs <;> omega),<- varianceCosineRightMean_branch]

theorem varianceCosineExample_population_pre {N : Nat}
    (mu0 : Measure VarianceCosinePoint) (T : Real) (z : VarianceCosineExampleTower N) :
    mu0.map (fun u => varianceCosineExampleCharacteristic P T z 0 u P.tau) =
      varianceCosineExamplePrePopulation P mu0 := by
  congr 1

theorem varianceCosineExample_curvature_identification {N : Nat} (hN : 2<=N)
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (hU : ∀ᵐ u ∂ mu0, norm u<=P.radius) (hm : varianceCosineMean mu0=0)
    (T : Real) (hT : P.tau<=T) (z : VarianceCosineExampleTower N) (t : Real) :
    rayleighInf (sampledMomentHessian varianceCosineEncodedFeature (varianceCosineObjective P.a P.beta)
      (integral (mu0.map (fun u => sourceGlue (varianceCosineTimes P.tau) 1
        (fun k => varianceCosineExampleCharacteristic P T z k u) t)) varianceCosineEncodedFeature)
      (varianceCosineExampleCanonicalRight P mu0 (by omega) T hT z t).2) =
      varianceCosineRightCurvature P.a P.beta P.tau P.eta T (varianceCosineTowerCoordinates z).2.1 t := by
  rw [varianceCosineExample_population_right]
  exact varianceCosineRightCurvature_eq_sampled hN mu0 P.radius P.radius_nonneg hU hm
    P.a P.beta P.tau P.eta T (varianceCosineTowerCoordinates z).2.1 t _

/-- Exact old-side law at the only jump, for EVERY observed prehistory. -/
theorem varianceCosineExample_pre_kernel {S : Type*} [MeasurableSpace S]
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0] (T : Real)
    (past : S -> Fin 0 -> Real) (h : S) :
    characteristicKernel mu0 (fun h u => sourceReferencePre (varianceCosineTimes P.tau)
      (varianceCosineFlowY P.a P.beta P.tau P.eta T)
      (sourcePopulationFieldJump (varianceCosineAmplitudes P.eta) (varianceCosineField P.a P.beta))
      0 (past h) u) h = varianceCosineExamplePrePopulation P mu0 := by
  have he : (fun h u => sourceReferencePre (varianceCosineTimes P.tau)
      (varianceCosineFlowY P.a P.beta P.tau P.eta T)
      (sourcePopulationFieldJump (varianceCosineAmplitudes P.eta) (varianceCosineField P.a P.beta))
      0 (past h) u) = (fun (_ : S) u => varianceCosineAffine 0 (Real.exp (-P.a*P.tau)) u) := rfl
  rw [he,(characteristicKernel_properties mu0 _
    ((varianceCosineAffine_measurable 0 (Real.exp (-P.a*P.tau))).comp measurable_snd)).2]
  rfl

end PaperFormalization.Manuscript
