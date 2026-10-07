import PaperFormalization.Manuscript.VarianceCosineGaussianField
import PaperFormalization.Manuscript.VarianceCosineRegularity
import PaperFormalization.Manuscript.SourceInputPermutationLaw

/-! # The same canonical population-first seed, not an independent replacement
M13u VERIFIED UNIT (full example application remains open). The original initial configuration and population scalar keep
their entire joint product law. Only the existing auxiliary standard Gaussian
is adjoined. Its mean-direction projection is then proved standard normal.
The population scalar Z and the projection zeta are NOT asserted independent.
-/
open MeasureTheory ProbabilityTheory Matrix Set
open scoped BigOperators ProbabilityTheory Matrix.Norms.Frobenius
namespace PaperFormalization.Manuscript

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 400000
attribute [local instance] sourceGramMeasurableMatrix sourceGramBorelMatrix

abbrev VarianceCosineCouplingSpace (N : Nat) :=
  SourceFiniteConfiguration N 1 × (Real × SourceStepNormal N 1)

noncomputable def varianceCosineCouplingLaw {N : Nat}
    (rho : Measure (SourceFiniteConfiguration N 1)) : Measure (VarianceCosineCouplingSpace N) :=
  rho.prod ((gaussianReal 0 1).prod (stdGaussian (SourceStepNormal N 1)))

instance varianceCosineCouplingLaw_probability {N : Nat}
    (rho : Measure (SourceFiniteConfiguration N 1)) [IsProbabilityMeasure rho] :
    IsProbabilityMeasure (varianceCosineCouplingLaw rho) := by
  unfold varianceCosineCouplingLaw
  infer_instance

noncomputable def varianceCosineReferencePre {N : Nat} (a tau : Real)
    (U : SourceFiniteConfiguration N 1) : SourceFiniteConfiguration N 1 :=
  WithLp.toLp 2 (fun i => varianceCosinePoint (Real.exp (-a*tau)*varianceCosineScalar (U i)))

theorem varianceCosineReferencePre_measurable {N : Nat} (a tau : Real) :
    Measurable (varianceCosineReferencePre (N := N) a tau) := by
  unfold varianceCosineReferencePre
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_lambda
  intro i
  change Measurable (fun U : SourceFiniteConfiguration N 1 => varianceCosinePointCLM
    (Real.exp (-a*tau)*varianceCosineScalar (U i)))
  fun_prop

theorem varianceCosineReferencePre_hermitian {N : Nat} (a beta tau : Real)
    (U : SourceFiniteConfiguration N 1) :
    (sourceEmpiricalKernelFactor 1 2 varianceCosineFeature (varianceCosineObjective a beta)
      (varianceCosineReferencePre a tau U)).IsHermitian := by
  rw [varianceCosine_source_empirical_factor]
  exact varianceCosineRankFactor_hermitian N _

noncomputable def varianceCosineCouplingSeed {N : Nat} (a beta tau : Real)
    (w : VarianceCosineCouplingSpace N) : SourceStepNormal N 1 :=
  sourceCanonicalWhiteningSeed
    (sourceEmpiricalKernelFactor 1 2 varianceCosineFeature (varianceCosineObjective a beta)
      (varianceCosineReferencePre a tau w.1))
    (varianceCosineReferencePre_hermitian a beta tau w.1)
    (varianceCosineRankCovariance N (varianceCosineKernel a beta 0))
    (varianceCosineFieldVector N (varianceCosineKernel a beta 0) w.2.1) w.2.2

noncomputable def varianceCosineCouplingZeta {N : Nat} (a beta tau : Real)
    (w : VarianceCosineCouplingSpace N) : Real :=
  varianceCosineNormalMean N (varianceCosineCouplingSeed a beta tau w)

/-- All history-dependent matrices are the actual unlocalised source matrices. -/
theorem varianceCosineCouplingSeed_measurable {N : Nat} (a beta tau : Real) :
    Measurable (varianceCosineCouplingSeed (N := N) a beta tau) := by
  change Measurable (fun w : VarianceCosineCouplingSpace N => varianceCosineCouplingSeed a beta tau w)
  let M := fun U : SourceFiniteConfiguration N 1 => sourceEmpiricalKernelFactor 1 2
    varianceCosineFeature (varianceCosineObjective a beta) (varianceCosineReferencePre a tau U)
  have hM : Measurable M := by
    have hpre := varianceCosineReferencePre_measurable (N := N) a tau
    have hmean : Measurable (varianceCosineEmpiricalMean (N := N)) := by
      unfold varianceCosineEmpiricalMean
      fun_prop
    have hc : Measurable (fun U : SourceFiniteConfiguration N 1 =>
        varianceCosineKernel a beta (varianceCosineEmpiricalMean (varianceCosineReferencePre a tau U))) := by
      have hh := hmean.comp hpre
      unfold varianceCosineKernel
      fun_prop
    have hf := hc.smul (measurable_const : Measurable (fun _ : SourceFiniteConfiguration N 1 =>
      varianceCosineRankFactor N 1))
    have heq : M = fun U =>
        varianceCosineKernel a beta (varianceCosineEmpiricalMean (varianceCosineReferencePre a tau U)) •
          varianceCosineRankFactor N 1 := by
      funext U
      dsimp only [M]
      rw [varianceCosine_source_empirical_factor]
      ext i j
      simp [varianceCosineRankFactor, smul_eq_mul, div_eq_mul_inv]
    rw [heq]
    exact hf
  have hs := sourceCanonicalWhiteningSeed_measurable M
    (fun _ => varianceCosineRankCovariance N (varianceCosineKernel a beta 0))
    (varianceCosineReferencePre_hermitian a beta tau) hM measurable_const
  have hv : Measurable (fun w : VarianceCosineCouplingSpace N =>
      varianceCosineFieldVector N (varianceCosineKernel a beta 0) w.2.1) := by
    unfold varianceCosineFieldVector
    fun_prop
  simpa only [varianceCosineCouplingSeed, Function.comp_def, M] using
    hs.comp (measurable_fst.prodMk (hv.prodMk (measurable_snd.comp measurable_snd)))

theorem varianceCosineCouplingZeta_measurable {N : Nat} (a beta tau : Real) :
    Measurable (varianceCosineCouplingZeta (N := N) a beta tau) :=
  (varianceCosineNormalMean N).measurable.comp (varianceCosineCouplingSeed_measurable a beta tau)

/-- Both the conditional seed law and its full history/seed joint law follow
from the original scalar field law and the fixed spectral whitening formula. -/
theorem varianceCosineCouplingSeed_laws {N : Nat} (hN : 0 < N)
    (rho : Measure (SourceFiniteConfiguration N 1)) [IsProbabilityMeasure rho]
    (a beta tau : Real) :
    (varianceCosineCouplingLaw rho).map (fun w => (w.1,varianceCosineCouplingSeed a beta tau w)) =
      rho.prod (stdGaussian (SourceStepNormal N 1)) ∧
    (varianceCosineCouplingLaw rho).map (varianceCosineCouplingSeed a beta tau) =
      stdGaussian (SourceStepNormal N 1) ∧
    (∀ᵐ w ∂ varianceCosineCouplingLaw rho,
      Matrix.toEuclideanCLM (𝕜 := Real) (alignedCovarianceFactor (varianceCosineReferencePre_hermitian a beta tau w.1)
        (varianceCosineRankCovariance N (varianceCosineKernel a beta 0)))
        (varianceCosineCouplingSeed a beta tau w) =
        varianceCosineFieldVector N (varianceCosineKernel a beta 0) w.2.1) := by
  let M := fun U : SourceFiniteConfiguration N 1 => sourceEmpiricalKernelFactor 1 2
    varianceCosineFeature (varianceCosineObjective a beta) (varianceCosineReferencePre a tau U)
  let C := fun _ : SourceFiniteConfiguration N 1 => varianceCosineRankCovariance N (varianceCosineKernel a beta 0)
  have hM : Measurable M := by
    have hpre := varianceCosineReferencePre_measurable (N := N) a tau
    have hmean : Measurable (varianceCosineEmpiricalMean (N := N)) := by
      unfold varianceCosineEmpiricalMean
      fun_prop
    have hc : Measurable (fun U : SourceFiniteConfiguration N 1 =>
        varianceCosineKernel a beta (varianceCosineEmpiricalMean (varianceCosineReferencePre a tau U))) := by
      have hh := hmean.comp hpre
      unfold varianceCosineKernel
      fun_prop
    have hf := hc.smul (measurable_const : Measurable (fun _ : SourceFiniteConfiguration N 1 =>
      varianceCosineRankFactor N 1))
    have heq : M = fun U =>
        varianceCosineKernel a beta (varianceCosineEmpiricalMean (varianceCosineReferencePre a tau U)) •
          varianceCosineRankFactor N 1 := by
      funext U
      dsimp only [M]
      rw [varianceCosine_source_empirical_factor]
      ext i j
      simp [varianceCosineRankFactor, smul_eq_mul, div_eq_mul_inv]
    rw [heq]
    exact hf
  obtain ⟨hm,hlaw,hjoint,hrep⟩ := sourceCanonicalWhiteningSeed_original_law rho
    (Kernel.const _ (gaussianReal 0 1)) (fun _ z => varianceCosineFieldVector N (varianceCosineKernel a beta 0) z)
    (by unfold varianceCosineFieldVector; fun_prop) M C C
    (varianceCosineReferencePre_hermitian a beta tau) hM measurable_const (Filter.EventuallyEq.rfl)
    (Filter.Eventually.of_forall (fun _ => varianceCosineRankCovariance_pos N _))
    (Filter.Eventually.of_forall (fun _ => varianceCosineFieldVector_gaussian N hN _))
  have hkernel : (Kernel.const (SourceFiniteConfiguration N 1) (gaussianReal 0 1)).prod
      (Kernel.const _ (stdGaussian (SourceStepNormal N 1))) =
      Kernel.const _ ((gaussianReal 0 1).prod (stdGaussian (SourceStepNormal N 1))) := by
    ext s A hA
    simp only [Kernel.prod_apply, Kernel.const_apply]
  rw [hkernel,Measure.compProd_const] at hjoint hrep
  change (varianceCosineCouplingLaw rho).map
    (fun w => (w.1,varianceCosineCouplingSeed a beta tau w)) = _ at hjoint
  have hmarg := congrArg (fun m : Measure (SourceFiniteConfiguration N 1 × SourceStepNormal N 1) =>
    m.map Prod.snd) hjoint
  rw [Measure.map_map measurable_snd
    (measurable_fst.prodMk (varianceCosineCouplingSeed_measurable a beta tau))] at hmarg
  have hsnd : (rho.prod (stdGaussian (SourceStepNormal N 1))).map Prod.snd =
      stdGaussian (SourceStepNormal N 1) := measurePreserving_snd.map_eq
  rw [hsnd] at hmarg
  exact ⟨hjoint,hmarg,hrep⟩

/-- The entire original initial/population joint law is unchanged, not just
individual marginals. This is a product extension, not event conditioning. -/
theorem varianceCosineCoupling_original_law {N : Nat}
    (rho : Measure (SourceFiniteConfiguration N 1)) [IsProbabilityMeasure rho] :
    (varianceCosineCouplingLaw rho).map (fun w => (w.1,w.2.1)) = rho.prod (gaussianReal 0 1) := by
  have hsnd : ((gaussianReal 0 1).prod (stdGaussian (SourceStepNormal N 1))).map Prod.fst =
      gaussianReal 0 1 := measurePreserving_fst.map_eq
  change (rho.prod _).map (Prod.map id Prod.fst) = _
  rw [← Measure.map_prod_map _ _ measurable_id measurable_fst,Measure.map_id,hsnd]

/-- Standardness of zeta is a CONCLUSION about the actual canonical seed. -/
theorem varianceCosineCoupling_normal_marginals {N : Nat} (hN : 0 < N)
    (rho : Measure (SourceFiniteConfiguration N 1)) [IsProbabilityMeasure rho] (a beta tau : Real) :
    (varianceCosineCouplingLaw rho).map (fun w => w.2.1) = gaussianReal 0 1 ∧
    (varianceCosineCouplingLaw rho).map (varianceCosineCouplingZeta a beta tau) = gaussianReal 0 1 := by
  have hZ := (measurePreserving_snd : MeasurePreserving
    (Prod.snd : VarianceCosineCouplingSpace N -> Real × SourceStepNormal N 1)
    (varianceCosineCouplingLaw rho) ((gaussianReal 0 1).prod (stdGaussian (SourceStepNormal N 1))))
  have hZ' := measurePreserving_fst.comp hZ
  exact ⟨hZ'.map_eq,varianceCosineNormalMean_law _ N hN _
    (varianceCosineCouplingSeed_laws hN rho a beta tau).2.1⟩

/-- All labelled moments are now fed by the actual coupling, not by an
assumption that its projection was Gaussian. -/
theorem varianceCosineCoupling_comparison_regularities {N : Nat} (hN : 0 < N)
    (rho : Measure (SourceFiniteConfiguration N 1)) [IsProbabilityMeasure rho]
    (a beta tau eta T R : Real) (ha : 0 <= a) (hb : 0 <= beta)
    (htau : 0 <= tau) (hT : tau <= T) (heta : 0 <= eta) (hR : 0 <= R)
    (hU : ∀ᵐ U ∂ rho, forall i, norm (U i) <= R) :
    let law := varianceCosineCouplingLaw rho
    let P := fun w => varianceCosinePairBranch a beta tau eta T w.1 w.2.1 (varianceCosineCouplingZeta a beta tau w)
    (forall k, k <= 1 -> forall t, t ∈ Icc (if k=0 then 0 else tau) (if k=0 then tau else T) -> forall i,
      law.map (fun w => (P w k t).1 i) ∈ sourceMomentClass 2 (varianceCosineMomentScale a beta R eta) ∧
      law.map (fun w => (P w k t).2 i) ∈ sourceMomentClass 2 (varianceCosineMomentScale a beta R eta)) ∧
    (∀ᵐ w ∂ law, forall k i,
      LipschitzOnWith ⟨varianceCosineSpeed a beta R,by unfold varianceCosineSpeed; positivity⟩
        (fun t => (P w k t).1 i) (Icc (if k=0 then 0 else tau) (if k=0 then tau else T)) ∧
      LipschitzOnWith ⟨varianceCosineSpeed a beta R,by unfold varianceCosineSpeed; positivity⟩
        (fun t => (P w k t).2 i) (Icc (if k=0 then 0 else tau) (if k=0 then tau else T))) ∧
    (forall w, SourceRightAntiSpikiness
      (fun t => (P w (if t<tau then 0 else 1) t).1)
      (fun t => (P w (if t<tau then 0 else 1) t).2) T 1) := by
  have hproj := (measurePreserving_fst : MeasurePreserving
    (Prod.fst : VarianceCosineCouplingSpace N -> SourceFiniteConfiguration N 1)
    (varianceCosineCouplingLaw rho) rho)
  have hU' := hproj.quasiMeasurePreserving.ae hU
  have hnorm := varianceCosineCoupling_normal_marginals hN rho a beta tau
  refine ⟨?_,?_,?_⟩
  . intro k hk t ht i
    exact varianceCosinePairBranch_moments _ hN a beta tau eta T R ha hb htau hT heta hR
      Prod.fst (fun w => w.2.1) (varianceCosineCouplingZeta a beta tau) measurable_fst
      (measurable_fst.comp measurable_snd) (varianceCosineCouplingZeta_measurable a beta tau)
      hU' hnorm.1 hnorm.2 k hk t ht i
  . filter_upwards [hU'] with w hw
    intro k i
    exact varianceCosinePairBranch_lipschitz hN a beta tau eta T R ha hb htau hT hR
      w.1 hw w.2.1 (varianceCosineCouplingZeta a beta tau w) k i
  . intro w
    exact varianceCosineRight_antiSpikiness hN a beta tau eta T w.1 w.2.1 _
end PaperFormalization.Manuscript
