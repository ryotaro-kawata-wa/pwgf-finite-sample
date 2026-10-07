import PaperFormalization.Manuscript.VarianceCosineSourceRealization

/-! # Concrete comparison assumptions for the printed variance--cosine model
M13u VERIFIED UNIT (full example application remains open). This unit constructs, rather than assumes, its certificate.
The only model premises are the original positive fixed parameters and the
bounded mean-zero initial probability law. There is no target seed-law,
raw-schedule, non-spikiness, moment, covariance or growth premise to fill later.
The escape event, curvature recovery and final example rates are a DIFFERENT
unit and are not certified by this declaration.
-/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ProbabilityTheory
namespace PaperFormalization.Manuscript

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

noncomputable def varianceCosineModelLaw (N : Nat) (mu0 : Measure VarianceCosinePoint) :=
  varianceCosineCouplingLaw (sourceInitialConfigurationLaw (N := N) mu0)

noncomputable def varianceCosineModelBranches {N : Nat} (a beta tau eta T : Real)
    (w : VarianceCosineCouplingSpace N) :=
  varianceCosinePairBranch a beta tau eta T w.1 w.2.1 (varianceCosineCouplingZeta a beta tau w)

/-- These are OUTPUTS of the original model construction. The fields enumerate
exactly which source-facing assumptions have been discharged. -/
structure VarianceCosineComparisonCertificate
    (N : Nat) (hN : 0 < N) (mu0 : Measure VarianceCosinePoint)
    (a beta tau eta T R : Real) (hSpeed : 0 <= varianceCosineSpeed a beta R) : Prop where
  featureC2 : forall n, ContDiff Real 2 (varianceCosineFeature n)
  featureGrowthBound : forall n x k, k <= 2 -> norm (iteratedFDeriv Real k (varianceCosineFeature n) x) <=
    featureGrowth 1 1 0 n * (1+norm x^(n+1-k))
  thirdFeatureExists : forall n x,
    DifferentiableAt Real (fderiv Real (fderiv Real (varianceCosineFeature n))) x
  thirdFeatureGrowth : forall n x, norm (iteratedFDeriv Real 3 (varianceCosineFeature n) x) <=
    featureGrowth 1 1 0 n * (1+norm x^(n+1-3))
  objectiveC3 : ContDiff Real 3 (varianceCosineObjective a beta)
  thirdObjective : forall z, norm (iteratedFDeriv Real 3 (varianceCosineObjective a beta) z) <=
    varianceCosineThirdBound beta
  originalLaw : (varianceCosineModelLaw N mu0).map (fun w => (w.1,w.2.1)) =
    (sourceInitialConfigurationLaw (N := N) mu0).prod (gaussianReal 0 1)
  seedLaw : (varianceCosineModelLaw N mu0).map (varianceCosineCouplingSeed a beta tau) =
    stdGaussian (SourceStepNormal N 1)
  populationODE : forall Z k u t,
    t ∈ Ioo (if k=0 then 0 else tau) (if k=0 then tau else T) ->
    let m := varianceCosineBranchMeanY a beta tau eta T Z k
    let P := fun s => varianceCosineAffine (m s) (Real.exp (-a*s)) u
    HasDerivAt P (momentGradientField (fderiv Real varianceCosineEncodedFeature)
      (gradient (varianceCosineObjective a beta))
      (integral (varianceCosinePopulation mu0 (m t) (Real.exp (-a*t))) varianceCosineEncodedFeature,P t)) t
  empiricalSchedule : forall w,
    SourceRawEmpiricalSchedule mu0 1 2 2 varianceCosineFeature (varianceCosineObjective a beta)
      Set.univ isOpen_univ (varianceCosineObjective_domains 2)
      (varianceCosineObjective_contDiff a beta |>.of_le (by norm_num) |>.contDiffOn) hN
      (varianceCosineTimes tau) (varianceCosineAmplitudes eta)
      (varianceCosineFlowY a beta tau eta T) (varianceCosineField a beta) 1 T
      (fun _ : Fin 1 => w.2) w.1 (fun k t => (varianceCosineModelBranches a beta tau eta T w k t).1)
  allRealMoments : forall k, k <= 1 -> forall t,
    t ∈ Icc (if k=0 then 0 else tau) (if k=0 then tau else T) -> forall i,
    (varianceCosineModelLaw N mu0).map (fun w => (varianceCosineModelBranches a beta tau eta T w k t).1 i)
      ∈ sourceMomentClass 2 (varianceCosineMomentScale a beta R eta) ∧
    (varianceCosineModelLaw N mu0).map (fun w => (varianceCosineModelBranches a beta tau eta T w k t).2 i)
      ∈ sourceMomentClass 2 (varianceCosineMomentScale a beta R eta)
  branchLipschitz : ∀ᵐ w ∂ varianceCosineModelLaw N mu0, forall k i,
    LipschitzOnWith ⟨varianceCosineSpeed a beta R,hSpeed⟩
      (fun t => (varianceCosineModelBranches a beta tau eta T w k t).1 i)
      (Icc (if k=0 then 0 else tau) (if k=0 then tau else T)) ∧
    LipschitzOnWith ⟨varianceCosineSpeed a beta R,hSpeed⟩
      (fun t => (varianceCosineModelBranches a beta tau eta T w k t).2 i)
      (Icc (if k=0 then 0 else tau) (if k=0 then tau else T))
  antiSpikiness : forall w : VarianceCosineCouplingSpace N, SourceRightAntiSpikiness
    (fun t => (varianceCosineModelBranches a beta tau eta T w (if t<tau then 0 else 1) t).1)
    (fun t => (varianceCosineModelBranches a beta tau eta T w (if t<tau then 0 else 1) t).2) T 1
  fieldLaw : forall Y : SourceFiniteConfiguration N 1,
    (gaussianReal 0 1).map (varianceCosineFieldVector N (varianceCosineKernel a beta 0)) =
    multivariateGaussian 0 (populationGramCovariance (varianceCosinePopulation mu0 0 (Real.exp (-a*tau)))
      (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix varianceCosineEncodedFeature
        (varianceCosineObjective a beta)
        (integral (varianceCosinePopulation mu0 0 (Real.exp (-a*tau))) varianceCosineEncodedFeature) (Y i) z)))

/-- The printed model's assumptions are supplied by explicit constructions.
The constants K0 and B have NO N or T argument. The true left branch at tau is
included in allRealMoments and branchLipschitz, and tau=T is not excluded. -/
theorem varianceCosine_comparison_assumptions
    (N : Nat) (hN : 0 < N) (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (a beta tau eta T R : Real) (ha : 0 < a) (hb : 0 < beta)
    (htau : 0 < tau) (heta : 0 < eta) (hR : 0 <= R) (hT : tau <= T)
    (hU : ∀ᵐ u ∂ mu0, norm u <= R) (hmean : varianceCosineMean mu0 = 0) :
    VarianceCosineComparisonCertificate N hN mu0 a beta tau eta T R
      (by unfold varianceCosineSpeed; positivity) := by
  have hreg := varianceCosineCoupling_comparison_regularities hN
    (sourceInitialConfigurationLaw (N := N) mu0) a beta tau eta T R
    ha.le hb.le htau.le hT heta.le hR (varianceCosineInitial_bounded mu0 R hU)
  refine {
    featureC2 := fun n => (varianceCosineFeature_contDiff n).of_le (by norm_num)
    featureGrowthBound := varianceCosineFeature_growth
    thirdFeatureExists := varianceCosineFeature_third_exists
    thirdFeatureGrowth := varianceCosineFeature_growth_three
    objectiveC3 := varianceCosineObjective_contDiff a beta
    thirdObjective := varianceCosine_third_bound a beta hb.le
    originalLaw := varianceCosineCoupling_original_law _
    seedLaw := (varianceCosineCouplingSeed_laws hN _ a beta tau).2.1
    populationODE := ?_
    empiricalSchedule := varianceCosine_raw_empirical_schedule hN mu0 R hR hU hmean
      a beta tau eta T hb.le htau.le hT
    allRealMoments := hreg.1
    branchLipschitz := hreg.2.1
    antiSpikiness := hreg.2.2
    fieldLaw := fun Y => varianceCosinePopulation_field_spec hN mu0 R hR hU hmean
      a beta 0 (Real.exp (-a*tau)) Y }
  intro Z k u t ht
  exact varianceCosine_reference_source_ode mu0 R hR hU hmean a beta tau eta T Z hb.le htau.le k u t ht

/-- Literal first-particle right-path input of the main theorem, derived from
the stronger already constructed closed-label certificate, not newly assumed. -/
theorem varianceCosine_comparison_right_moments
    (N : Nat) (hN : 0 < N) (mu0 : Measure VarianceCosinePoint)
    (a beta tau eta T R : Real) (htau : 0 <= tau) (hT : tau <= T)
    (hSpeed : 0 <= varianceCosineSpeed a beta R)
    (cert : VarianceCosineComparisonCertificate N hN mu0 a beta tau eta T R hSpeed)
    (t : Real) (ht : t ∈ Icc 0 T) (i : Fin N) :
    (varianceCosineModelLaw N mu0).map (fun w =>
      (varianceCosineModelBranches a beta tau eta T w (if t<tau then 0 else 1) t).1 i)
      ∈ sourceMomentClass 2 (varianceCosineMomentScale a beta R eta) ∧
    (varianceCosineModelLaw N mu0).map (fun w =>
      (varianceCosineModelBranches a beta tau eta T w (if t<tau then 0 else 1) t).2 i)
      ∈ sourceMomentClass 2 (varianceCosineMomentScale a beta R eta) := by
  by_cases hj : t<tau
  . simpa only [if_pos hj] using cert.allRealMoments 0 (by omega) t ⟨ht.1,hj.le⟩ i
  . simpa only [if_neg hj] using cert.allRealMoments 1 (by omega) t ⟨le_of_not_gt hj,ht.2⟩ i

/-- Exact coordinates on the SAME one-step auxiliary tower used by M13T.
ULift is only its universe wrapper, not a change of probability model. -/
def varianceCosineTowerCoordinates {N : Nat}
    (z : SourceAuxiliarySpace (SourceFiniteConfiguration N 1 × Real) (SourceStepNormal N 1) 1) :
    VarianceCosineCouplingSpace N := (z.1.down.1,(z.1.down.2,z.2))

/-- Reassociation preserves the entire original and auxiliary law. -/
theorem varianceCosineTower_preserving {N : Nat}
    (rho : Measure (SourceFiniteConfiguration N 1)) [IsProbabilityMeasure rho] :
    MeasurePreserving varianceCosineTowerCoordinates
      (sourceAuxiliaryMeasure (rho.prod (gaussianReal 0 1)) (stdGaussian (SourceStepNormal N 1)) 1)
      (varianceCosineCouplingLaw rho) := by
  have h0 := sourceAuxiliaryOriginal_preserving (rho.prod (gaussianReal 0 1))
    (stdGaussian (SourceStepNormal N 1)) 0
  have hp := h0.prod (MeasurePreserving.id (stdGaussian (SourceStepNormal N 1)))
  have ha := measurePreserving_prodAssoc rho (gaussianReal 0 1) (stdGaussian (SourceStepNormal N 1))
  convert ha.comp hp using 1 <;> rfl

/-- Every stated moment/law can be transported directly to the existing final
tower before any event is formed. No independence after conditioning is used. -/
theorem varianceCosineTower_map {N : Nat} {E : Type*} [MeasurableSpace E]
    (rho : Measure (SourceFiniteConfiguration N 1)) [IsProbabilityMeasure rho]
    (f : VarianceCosineCouplingSpace N -> E) (hf : Measurable f) :
    (sourceAuxiliaryMeasure (rho.prod (gaussianReal 0 1)) (stdGaussian (SourceStepNormal N 1)) 1).map
      (fun z => f (varianceCosineTowerCoordinates z)) = (varianceCosineCouplingLaw rho).map f := by
  have hp := varianceCosineTower_preserving rho
  calc
    _ = ((sourceAuxiliaryMeasure (rho.prod (gaussianReal 0 1))
        (stdGaussian (SourceStepNormal N 1)) 1).map varianceCosineTowerCoordinates).map f :=
      (Measure.map_map hf hp.measurable).symm
    _ = _ := congrArg (fun mu => mu.map f) hp.map_eq
end PaperFormalization.Manuscript
