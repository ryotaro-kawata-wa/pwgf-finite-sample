import PaperFormalization.Manuscript.VarianceCosineFeatures
import PaperFormalization.Manuscript.ExponentialMomentClass
import PaperFormalization.Manuscript.GaussianSquareMoment
import PaperFormalization.Manuscript.GaussianMatrixTail

/-! # Original-law all-real-order Gaussian moment bounds
M13u VERIFIED UNIT (full example application remains open). The Gaussian exponential-square identity yields the printed
2*sqrt(q) bound directly for EVERY real q>=1. No integer-only replacement and
no change of law by a localisation event is used. The two coupling normals
need not be independent: only their separately proved marginals are used.
-/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace PaperFormalization.Manuscript

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

theorem varianceCosineGaussian_exp :
    Integrable (fun x : Real => Real.exp ((norm x/2)^(2 : Real))) (gaussianReal 0 1) ∧
    integral (gaussianReal 0 1) (fun x : Real => Real.exp ((norm x/2)^(2 : Real))) <= 2 := by
  have he (x : Real) : (norm x/2)^(2 : Real) = (1/4 : Real)*x^2 := by
    rw [Real.rpow_two,div_pow,Real.norm_eq_abs,sq_abs]
    ring
  constructor
  . simp_rw [he]
    exact integrable_exp_sq_standardGaussian (1/4) (by norm_num)
  . simp_rw [he]
    rw [integral_exp_sq_standardGaussian (1/4) (by norm_num)]
    norm_num

/-- Exact constant 2, obtained without rounding the real moment order. -/
theorem varianceCosineGaussian_scalar_root (q : Real) (hq : 1 <= q) :
    (2*((2 : Real)^q*(q/(2*Real.exp 1))^(q/2)))^q⁻¹ <= 2*q^(1/2 : Real) := by
  have hq0 : 0 < q := by linarith
  have he2 : 2 <= Real.exp 1 := by linarith [Real.add_one_le_exp (1 : Real)]
  have he : 0 < 2*Real.exp 1 := by positivity
  have hid : (2*((2 : Real)^q*(q/(2*Real.exp 1))^(q/2)))^q⁻¹ =
      (2 : Real)^q⁻¹*2*(q/(2*Real.exp 1))^(1/2 : Real) := by
    rw [Real.mul_rpow (by norm_num) (by positivity),
      Real.mul_rpow (by positivity) (by positivity),
      <- Real.rpow_mul (by norm_num : (0 : Real) <= 2),
      <- Real.rpow_mul (by positivity : 0 <= q/(2*Real.exp 1))]
    rw [mul_inv_cancel₀ hq0.ne',Real.rpow_one]
    rw [show q/2*q⁻¹ = (1/2 : Real) by field_simp]
    ring
  have ht : (2 : Real)^q⁻¹ <= 2 := by
    calc
      _ <= (2 : Real)^1 := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (inv_le_one_of_one_le₀ hq)
      _ = 2 := Real.rpow_one _
  have hden : q/(2*Real.exp 1) <= q/4 := by
    apply (div_le_div_iff₀ he (by norm_num : (0 : Real) < 4)).mpr
    nlinarith
  have hroot := Real.rpow_le_rpow (by positivity : 0 <= q/(2*Real.exp 1)) hden (by norm_num : (0 : Real) <= 1/2)
  have hfour : (4 : Real)^(1/2 : Real) = 2 := by norm_num [<- Real.sqrt_eq_rpow]
  rw [Real.div_rpow hq0.le (by norm_num : (0 : Real) <= 4),hfour] at hroot
  rw [hid]
  have hh := mul_le_mul ht hroot (by positivity) (by norm_num : (0 : Real) <= 2)
  nlinarith

theorem varianceCosineGaussian_moment_class :
    gaussianReal 0 1 ∈ sourceMomentClass 2 2 := by
  apply (sourceMomentClass_iff_integrable_root_bound 2 2 (by norm_num) _).mpr
  refine ⟨inferInstance,?_ ⟩
  intro q hq
  obtain ⟨hi,hb ⟩ := integrable_norm_rpow_of_exp_moment (gaussianReal 0 1)
    2 2 q (by norm_num) (by norm_num) (by linarith) varianceCosineGaussian_exp.1 varianceCosineGaussian_exp.2
  refine ⟨hi,?_ ⟩
  exact (Real.rpow_le_rpow (integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) q))
    hb (inv_nonneg.mpr (by linarith))).trans (varianceCosineGaussian_scalar_root q hq)

/-- The printed affine envelope gives K=M+2S under the unchanged probability
measure. X may depend arbitrarily on Z and on all the other randomness. -/
theorem varianceCosine_moment_of_gaussian_envelope
    {O E : Type*} [MeasurableSpace O] [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    (mu : Measure O) [IsProbabilityMeasure mu] (Z : O -> Real) (X : O -> E)
    (hZ : Measurable Z) (hX : Measurable X) (hlaw : mu.map Z = gaussianReal 0 1)
    (M S : Real) (hM : 0 <= M) (hS : 0 <= S)
    (hbound : ∀ᵐ o ∂mu, norm (X o) <= M+S*abs (Z o)) :
    mu.map X ∈ sourceMomentClass 2 (M+2*S) := by
  refine ⟨Measure.isProbabilityMeasure_map hX.aemeasurable,?_ ⟩
  intro q hq
  have hq0 : 0 < q := by linarith
  have hqe : (1 : ENNReal) <= ENNReal.ofReal q := by simpa using ENNReal.ofReal_le_ofReal hq
  have hroot : 1 <= q^(1/2 : Real) := Real.one_le_rpow hq (by norm_num)
  have hz := varianceCosineGaussian_moment_class.2 q hq
  rw [<- hlaw,eLpNorm_map_measure aestronglyMeasurable_id hZ.aemeasurable] at hz
  change eLpNorm Z (ENNReal.ofReal q) mu <= ENNReal.ofReal (2*q^(1/2 : Real)) at hz
  rw [eLpNorm_map_measure aestronglyMeasurable_id hX.aemeasurable]
  change eLpNorm X (ENNReal.ofReal q) mu <= _
  have hc : eLpNorm (fun _ : O => M) (ENNReal.ofReal q) mu = ENNReal.ofReal M := by
    rw [eLpNorm_const M (ENNReal.ofReal_ne_zero_iff.mpr hq0) (by exact NeZero.ne mu)]
    simp [Real.enorm_eq_ofReal hM]
  calc
    _ <= eLpNorm (fun o => M+S*abs (Z o)) (ENNReal.ofReal q) mu := by
      apply eLpNorm_mono_ae
      filter_upwards [hbound] with o ho
      simpa only [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 <= M+S*abs (Z o))] using ho
    _ <= eLpNorm (fun _ : O => M) (ENNReal.ofReal q) mu +
        eLpNorm (fun o => S*abs (Z o)) (ENNReal.ofReal q) mu :=
      eLpNorm_add_le aestronglyMeasurable_const (by fun_prop) hqe
    _ <= ENNReal.ofReal M + ENNReal.ofReal S*ENNReal.ofReal (2*q^(1/2 : Real)) := by
      rw [hc]
      apply add_le_add le_rfl
      change eLpNorm (S • (fun o => norm (Z o))) (ENNReal.ofReal q) mu <= _
      rw [eLpNorm_const_smul,<- ofReal_norm,Real.norm_eq_abs,abs_of_nonneg hS,eLpNorm_norm]
      exact mul_le_mul_left' hz _
    _ = ENNReal.ofReal (M+S*(2*q^(1/2 : Real))) := by
      rw [ENNReal.ofReal_add hM (by positivity),ENNReal.ofReal_mul hS]
    _ <= _ := ENNReal.ofReal_le_ofReal (by nlinarith [mul_le_mul_of_nonneg_left hroot hM])

noncomputable def varianceCosineConstantDirection (N : Nat) : EuclideanSpace Real (Fin N × Fin 1) :=
  WithLp.toLp 2 (fun _ => (Real.sqrt N)⁻¹)

theorem varianceCosineConstantDirection_norm (N : Nat) (hN : 0 < N) :
    norm (varianceCosineConstantDirection N) = 1 := by
  have hp : 0 < (N : Real) := by exact_mod_cast hN
  have hs := Real.sq_sqrt hp.le
  have hs0 := (Real.sqrt_pos.mpr hp).ne'
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : Real) <= 1)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [varianceCosineConstantDirection,PiLp.toLp_apply,Real.norm_eq_abs,sq_abs]
  simp [Fintype.card_prod,Finset.sum_const,hs,inv_pow,hp.ne']

noncomputable def varianceCosineNormalMean (N : Nat) :
    EuclideanSpace Real (Fin N × Fin 1) →L[Real] Real :=
  InnerProductSpace.toDual Real _ (varianceCosineConstantDirection N)

/-- Applied to the existing canonical coupling seed, this gives zeta's TRUE
marginal law, with no assertion that zeta and the population Z are independent. -/
theorem varianceCosineNormalMean_law
    {O : Type*} [MeasurableSpace O] (mu : Measure O) (N : Nat) (hN : 0 < N)
    (g : O -> EuclideanSpace Real (Fin N × Fin 1))
    (hg : mu.map g = stdGaussian (EuclideanSpace Real (Fin N × Fin 1))) :
    mu.map (fun o => varianceCosineNormalMean N (g o)) = gaussianReal 0 1 := by
  have hgm : AEMeasurable g mu := aemeasurable_of_map_neZero (by rw [hg]; infer_instance)
  have hn : norm (varianceCosineNormalMean N) = 1 := by
    rw [varianceCosineNormalMean,LinearIsometryEquiv.norm_map,varianceCosineConstantDirection_norm N hN]
  change mu.map (varianceCosineNormalMean N ∘ g) = _
  rw [<- AEMeasurable.map_map_of_aemeasurable (varianceCosineNormalMean N).continuous.aemeasurable hgm,
    hg,IsGaussian.map_eq_gaussianReal,integral_strongDual_stdGaussian,variance_dual_stdGaussian,hn]
  norm_num
end PaperFormalization.Manuscript
