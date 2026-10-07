import PaperFormalization.Manuscript.VarianceCosineCoupling
import Mathlib.MeasureTheory.Constructions.Pi

/-! # The original affine population law and the actual initial product sample
M13u VERIFIED UNIT (full example application remains open). Mean-zero and bounded support are hypotheses only of the
original initial law. The later population has Gaussian translations, not
bounded support by the same radius. Moments are proved before integrations.
-/
open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators ProbabilityTheory
namespace PaperFormalization.Manuscript

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

noncomputable def varianceCosineAffine (m r : Real) (u : VarianceCosinePoint) : VarianceCosinePoint :=
  varianceCosinePoint (m+r*varianceCosineScalar u)

noncomputable def varianceCosinePopulation (mu0 : Measure VarianceCosinePoint) (m r : Real) :
    Measure VarianceCosinePoint := mu0.map (varianceCosineAffine m r)

theorem varianceCosineAffine_measurable (m r : Real) : Measurable (varianceCosineAffine m r) := by
  change Measurable (fun u => varianceCosinePointCLM (m+r*varianceCosineScalar u))
  fun_prop

instance varianceCosinePopulation_probability (mu0 : Measure VarianceCosinePoint)
    [IsProbabilityMeasure mu0] (m r : Real) : IsProbabilityMeasure (varianceCosinePopulation mu0 m r) :=
  Measure.isProbabilityMeasure_map (varianceCosineAffine_measurable m r).aemeasurable

theorem varianceCosine_bounded_initial_memLp (mu0 : Measure VarianceCosinePoint)
    [IsProbabilityMeasure mu0] (R : Real) (hU : ∀ᵐ u ∂ mu0, norm u <= R) (q : ENNReal) :
    MemLp (id : VarianceCosinePoint -> VarianceCosinePoint) q mu0 :=
  MemLp.of_bound aestronglyMeasurable_id R hU

/-- A fixed affine pushforward remains in P2; the bound may depend on that
realized mean, without pretending a uniform conditional K0. -/
theorem varianceCosinePopulation_memLp (mu0 : Measure VarianceCosinePoint)
    [IsProbabilityMeasure mu0] (R : Real) (hR : 0 <= R)
    (hU : ∀ᵐ u ∂ mu0, norm u <= R) (m r : Real) :
    MemLp (id : VarianceCosinePoint -> VarianceCosinePoint) 2 (varianceCosinePopulation mu0 m r) := by
  apply MemLp.of_bound aestronglyMeasurable_id (abs m+abs r*R)
  rw [varianceCosinePopulation,ae_map_iff (varianceCosineAffine_measurable m r).aemeasurable (measurableSet_le measurable_id.norm measurable_const)]
  filter_upwards [hU] with u hu
  rw [varianceCosineAffine,id_eq,varianceCosinePoint_norm]
  apply (abs_add_le _ _).trans
  rw [abs_mul,varianceCosineScalar_abs]
  gcongr

/-- The mean and centered second moment are computed with genuine integrals. -/
theorem varianceCosinePopulation_mean_variance (mu0 : Measure VarianceCosinePoint)
    [IsProbabilityMeasure mu0] (R : Real) (hR : 0 <= R)
    (hU : ∀ᵐ u ∂ mu0, norm u <= R) (hmean : varianceCosineMean mu0 = 0) (m r : Real) :
    varianceCosineMean (varianceCosinePopulation mu0 m r) = m ∧
    varianceCosineVariance (varianceCosinePopulation mu0 m r) = r^2*varianceCosineVariance mu0 := by
  have h2 := varianceCosine_bounded_initial_memLp mu0 R hU 2
  have hi := varianceCosine_integrable_coordinates mu0 h2
  have hpop2 := varianceCosinePopulation_memLp mu0 R hR hU m r
  have hmu : varianceCosineMean (varianceCosinePopulation mu0 m r) = m := by
    unfold varianceCosineMean varianceCosinePopulation
    rw [integral_map (varianceCosineAffine_measurable m r).aemeasurable
      varianceCosineScalar.continuous.aestronglyMeasurable]
    simp only [varianceCosineAffine,varianceCosineScalar_point]
    rw [integral_add (integrable_const _) (hi.1.const_mul _),integral_const_mul]
    simp only [integral_const, probReal_univ, one_smul]
    change m + r*varianceCosineMean mu0 = m
    rw [hmean,mul_zero,add_zero]
  refine ⟨hmu,?_⟩
  unfold varianceCosineVariance
  rw [hmu,varianceCosinePopulation,integral_map (varianceCosineAffine_measurable m r).aemeasurable (by fun_prop)]
  simp only [varianceCosineAffine,varianceCosineScalar_point]
  simp_rw [show forall u : VarianceCosinePoint, (m+r*varianceCosineScalar u-m)^2 =
      r^2*(varianceCosineScalar u)^2 from fun u => by ring]
  rw [integral_const_mul,hmean]
  simp only [sub_zero]

/-- The actual population objective and its nonnegative excess over the minimum. -/
theorem varianceCosinePopulation_objective (mu0 : Measure VarianceCosinePoint)
    [IsProbabilityMeasure mu0] (R : Real) (hR : 0 <= R)
    (hU : ∀ᵐ u ∂ mu0, norm u <= R) (hmean : varianceCosineMean mu0 = 0)
    (a beta m r : Real) :
    Integrable varianceCosineEncodedFeature (varianceCosinePopulation mu0 m r) ∧
    varianceCosineObjective a beta (integral (varianceCosinePopulation mu0 m r) varianceCosineEncodedFeature) =
      a/2*r^2*varianceCosineVariance mu0 + beta*Real.cos (Real.pi*m) := by
  have hi := varianceCosineObjective_population_identity a beta _
    (varianceCosinePopulation_memLp mu0 R hR hU m r)
  have hv := varianceCosinePopulation_mean_variance mu0 R hR hU hmean m r
  refine ⟨hi.1,?_⟩
  rw [hi.2,varianceCosineFunctional,hv.1,hv.2]
  ring

/-- Covariance specification supplied to the original fresh-field construction. -/
theorem varianceCosinePopulation_field_spec {N : Nat} (hN : 0 < N)
    (mu0 : Measure VarianceCosinePoint) [IsProbabilityMeasure mu0]
    (R : Real) (hR : 0 <= R) (hU : ∀ᵐ u ∂ mu0, norm u <= R)
    (hmean : varianceCosineMean mu0 = 0) (a beta m r : Real) (Y : SourceFiniteConfiguration N 1) :
    (gaussianReal 0 1).map (varianceCosineFieldVector N (varianceCosineKernel a beta m)) =
      multivariateGaussian 0 (populationGramCovariance (varianceCosinePopulation mu0 m r)
        (fun z => stackedKernelMatrix (fun i => actualMomentKernelMatrix varianceCosineEncodedFeature
          (varianceCosineObjective a beta)
          (integral (varianceCosinePopulation mu0 m r) varianceCosineEncodedFeature) (Y i) z))) := by
  rw [(varianceCosine_population_covariance a beta _
    (varianceCosinePopulation_memLp mu0 R hR hU m r) Y).2,
    (varianceCosinePopulation_mean_variance mu0 R hR hU hmean m r).1]
  exact varianceCosineFieldVector_gaussian N hN _

/-- Every coordinate has the original marginal under the genuine product law. -/
theorem varianceCosineInitial_marginal {N : Nat} (mu0 : Measure VarianceCosinePoint)
    [IsProbabilityMeasure mu0] (i : Fin N) :
    (sourceInitialConfigurationLaw (N := N) mu0).map (fun U => U i) = mu0 := by
  unfold sourceInitialConfigurationLaw
  rw [Measure.map_map (by fun_prop) (WithLp.measurable_toLp 2 _)]
  exact (measurePreserving_eval (fun _ : Fin N => mu0) i).map_eq

theorem varianceCosineInitial_bounded {N : Nat} (mu0 : Measure VarianceCosinePoint)
    [IsProbabilityMeasure mu0] (R : Real) (hU : ∀ᵐ u ∂ mu0, norm u <= R) :
    ∀ᵐ U ∂ sourceInitialConfigurationLaw (N := N) mu0, forall i, norm (U i) <= R := by
  apply ae_all_iff.mpr
  intro i
  have hp : MeasurePreserving (fun U : SourceFiniteConfiguration N 1 => U i)
      (sourceInitialConfigurationLaw mu0) mu0 :=
    ⟨by fun_prop,varianceCosineInitial_marginal mu0 i⟩
  exact hp.quasiMeasurePreserving.ae hU

/-- Initial iid is derived from the product construction, not claimed for the
later interacting empirical particles. -/
theorem varianceCosineInitial_iid {N : Nat} (mu0 : Measure VarianceCosinePoint)
    [IsProbabilityMeasure mu0] :
    iIndepFun (fun (i : Fin N) (U : SourceFiniteConfiguration N 1) => U i)
      (sourceInitialConfigurationLaw mu0) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => by fun_prop)).mpr
  simp_rw [varianceCosineInitial_marginal]
  unfold sourceInitialConfigurationLaw
  rw [Measure.map_map (by fun_prop) (WithLp.measurable_toLp 2 _)]
  simp only [Function.comp_def, PiLp.toLp_apply, Measure.map_id']

end PaperFormalization.Manuscript
