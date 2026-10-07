import PaperFormalization.Manuscript.SourceScheduledClosureSupport
import PaperFormalization.Manuscript.SourceFiniteTrackingApplication

/-! # Actual source ODE witnesses supply the canonical branch equations
M13s verified unit; see CODEX_HANDOFF_M13S.md. A visited branch needs an actual source solution on that
branch only. We do not demand solutions for arbitrary initial configurations.
Reference coordinate equations are transported from the original population
characteristic with independent seeds, never reconditioned on a good event.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal Topology ProbabilityTheory
namespace PaperFormalization.Manuscript
set_option backward.isDefEq.respectTransparency false
variable {O W : Type*} [MeasurableSpace O] [MeasurableSpace W] {N d : Nat}
variable {H : Nat -> Type*} [∀ m, NormedAddCommGroup (H m)]
  [∀ m, InnerProductSpace Real (H m)] [∀ m, CompleteSpace (H m)]

/-- Original branch existence, restricted to the actually visited initial state. -/
def SourceVisitedEmpiricalSolutions
    (f : SourceFiniteConfiguration N d -> SourceFiniteConfiguration N d)
    (post : SourcePostMap W N d) (tau : Nat -> Real) (J : Nat) (T : Real)
    (h : Fin J -> W × SourceStepNormal N d) (u : SourceFiniteConfiguration N d) : Prop :=
  ∀ k (hk : k ≤ J),
    ∃ x : Real -> SourceFiniteConfiguration N d,
      x (tau k) = (post k (sourceFinitePrefix h k hk) u).1 ∧
      ContinuousOn x (Icc (tau k) (if k < J then tau (k+1) else T)) ∧
      ∀ t, t ∈ Ioo (tau k) (if k < J then tau (k+1) else T) -> HasDerivAt x (f (x t)) t

/-- The fixed canonical branch equals the existing source branch. Therefore its
coordinate equations are the actual empirical ODE, not supplied scalar bounds. -/
theorem source_visited_empirical_coordinate_odes
    (c p : Real) (phi : ∀ m, EuclideanSpace Real (Fin d) -> H m) (G : lp H 2 -> Real)
    (hf : ContDiff Real 1 (sourceExactEmpiricalDrift (N := N) c p phi G))
    (tau : Nat -> Real) (J : Nat) (T : Real)
    (htime : ∀ k, k < J -> tau k < tau (k+1)) (hT : tau J ≤ T)
    (post : SourcePostMap W N d) (flowY)
    (h : Fin J -> W × SourceStepNormal N d) (u : SourceFiniteConfiguration N d)
    (hSolutions : SourceVisitedEmpiricalSolutions (sourceExactEmpiricalDrift c p phi G) post tau J T h u) :
    let flowX := sourceCanonicalEmpiricalFlow c p phi G tau J T htime hT
    let branches := sourceFiniteHorizonBranch post flowX flowY J h u
    ∀ k, k ≤ J -> ∀ i,
      ∀ᵐ t ∂ volume.restrict (Ioo (tau k) (if k < J then tau (k+1) else T)),
        HasDerivAt (fun s => (branches k s).1 i)
          ((sourceExactEmpiricalDrift c p phi G (branches k t).1) i) t := by
  dsimp only
  intro k hk i
  obtain ⟨x,hstart,hcont,hode⟩ := hSolutions k hk
  have hc : ContinuousOn x (Icc (tau k) (sourceHorizonEndpoint tau J T k)) := by
    simpa only [sourceHorizonEndpoint_used tau J T k hk] using hcont
  have hd : ∀ t, t ∈ Ioo (tau k) (sourceHorizonEndpoint tau J T k) ->
      HasDerivAt x (sourceExactEmpiricalDrift c p phi G (x t)) t := by
    simpa only [sourceHorizonEndpoint_used tau J T k hk] using hode
  have hDomain := (sourceCanonicalEmpiricalFlow_eq_source c p phi G hf tau J T htime hT k x hc hd).1
  rw [hstart] at hDomain
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hder := sourceCanonicalEmpiricalFlow_ode c p phi G hf tau J T htime hT k
    (post k (sourceFinitePrefix h k hk) u).1 hDomain t
    (by simpa only [sourceHorizonEndpoint_used tau J T k hk] using ht)
  have hcoord := (PiLp.proj (𝕜 := Real) 2
    (fun _ : Fin N => EuclideanSpace Real (Fin d)) i).hasFDerivAt.comp_hasDerivAt t hder
  simpa only [sourceFiniteHorizonBranch_eq _ _ _ _ _ _ k hk,sourceCoupledBranch,Function.comp_def,PiLp.proj_apply] using hcoord

/-- Original characteristic equations pulled to every reference particle on
one final-law ∀ᵐ set. The time-∀ᵐ quantifier stays inside this common event. -/
theorem source_final_reference_coordinate_odes
    (mu0 : Measure (EuclideanSpace Real (Fin d))) [IsProbabilityMeasure mu0]
    (c p alpha : Real) (phi : ∀ m, EuclideanSpace Real (Fin d) -> H m)
    (G : lp H 2 -> Real) (U : Set (lp H 2)) (hU : IsOpen U)
    (hDomains : SourceAllMomentDomains (sourceWeightedFeatureMap c p phi) alpha U)
    (hG : ContDiffOn Real 2 G U) (hN : 0 < N)
    (tau eta : Nat -> Real) (flowX flowY field) (J : Nat) (T : Real)
    (nu : Measure O) [IsProbabilityMeasure nu]
    (initial : O -> SourceFiniteConfiguration N d) (innovation : Nat -> O -> W)
    (hinit : Measurable initial) (hInnovation : ∀ n, Measurable (innovation n))
    (hind : IndepFun (fun o n => innovation n o) (fun o i => initial o i) nu)
    (hlaw : ∀ i, nu.map (fun o => initial o i) = mu0)
    (hPopODE : let F := sourceWeightedFeatureMap c p phi
      ∀ᵐ z ∂ (nu.map (fun o n => innovation n o)).prod mu0, ∀ k, k ≤ J ->
        ∀ᵐ t ∂ volume.restrict (Ioo (tau k) (if k < J then tau (k+1) else T)),
          HasDerivAt (sourceOriginalCharacteristic tau eta flowY field k z.1 z.2)
            (momentGradientField (fderiv Real F) (gradient G)
              (∫ x, F x ∂ mu0.map (fun u => sourceOriginalCharacteristic tau eta flowY field k z.1 u t),
               sourceOriginalCharacteristic tau eta flowY field k z.1 z.2 t)) t) :
    let post := sourceActualFinitePost mu0 c p alpha phi G U hU hDomains hG hN tau eta flowX flowY field
    let F := sourceWeightedFeatureMap c p phi
    ∀ᵐ z ∂ sourceAuxiliaryMeasure nu (stdGaussian (SourceStepNormal N d)) J,
      let branches := sourceFinalBranch post flowX flowY initial innovation J z
      let Z := sourceFiniteReferenceBranch tau eta flowY field J (sourceTowerPacked innovation J z)
      ∀ k, k ≤ J -> ∀ i,
        ∀ᵐ t ∂ volume.restrict (Ioo (tau k) (if k < J then tau (k+1) else T)),
          HasDerivAt (fun s => (branches k s).2 i)
            ((frozenMomentConfigurationField
              (momentGradientField (fderiv Real F) (gradient G))
              (∫ x, F x ∂ mu0.map (fun u => Z k u t)) (branches k t).2) i) t := by
  let post := sourceActualFinitePost mu0 c p alpha phi G U hU hDomains hG hN tau eta flowX flowY field
  let F := sourceWeightedFeatureMap c p phi
  have hm i : Measurable (fun o => initial o i) :=
    ((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 _)).comp hinit
  have hsamples := source_independent_seed_path_agreement nu mu0 (fun o n => innovation n o)
    (fun i o => initial o i) (measurable_pi_lambda _ hInnovation) hm hind hlaw
    (fun e u => ∀ k, k ≤ J ->
      ∀ᵐ t ∂ volume.restrict (Ioo (tau k) (if k < J then tau (k+1) else T)),
        HasDerivAt (sourceOriginalCharacteristic tau eta flowY field k e u)
          (momentGradientField (fderiv Real F) (gradient G)
            (∫ x, F x ∂ mu0.map (fun v => sourceOriginalCharacteristic tau eta flowY field k e v t),
             sourceOriginalCharacteristic tau eta flowY field k e u t)) t) hPopODE
  have hLift := (sourceAuxiliaryOriginal_preserving nu (stdGaussian (SourceStepNormal N d)) J).quasiMeasurePreserving.ae hsamples
  filter_upwards [hLift] with z hz
  dsimp only
  intro k hk i
  have hbranch : (fun t => (sourceFinalBranch post flowX flowY initial innovation J z k t).2 i) =
      sourceOriginalCharacteristic tau eta flowY field k
        (fun n => innovation n (sourceAuxiliaryOriginal J z)) (initial (sourceAuxiliaryOriginal J z) i) := by
    funext t
    exact sourceFinalBranch_reference_original mu0 c p alpha phi G U hU hDomains hG hN tau eta flowX flowY field
      initial innovation J k hk z t i
  have hpop : ∀ t,
      (fun u => sourceFiniteReferenceBranch tau eta flowY field J (sourceTowerPacked innovation J z) k u t) =
      (fun u => sourceOriginalCharacteristic tau eta flowY field k (fun n => innovation n (sourceAuxiliaryOriginal J z)) u t) := by
    intro t
    funext u
    exact sourceFiniteReferenceBranch_original tau eta flowY field innovation J k hk z u t
  dsimp only [post] at hbranch
  have hbranchAt (s : Real) := congrFun hbranch s
  simpa only [hbranch,hbranchAt,hpop,frozenMomentConfigurationField,F] using hz i k hk
end PaperFormalization.Manuscript
