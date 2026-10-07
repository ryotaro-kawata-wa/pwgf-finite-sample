import PaperFormalization.Manuscript.VarianceCosineFeatures
import PaperFormalization.Manuscript.EmpiricalMeasureMoment
import PaperFormalization.Manuscript.SourceMomentClass
import PaperFormalization.Manuscript.SourceActualFiniteConstruction

/-! # Decode the source moments before evaluating the variance--cosine objective
M13u VERIFIED UNIT (full example application remains open). The represented Hilbert coordinate is w_m M_m, not M_m.
The two genuine Bochner moments are proved integrable from P2 before they are
used as real integrals. No higher moment or bounded-support condition is needed
for the objective identity itself.
-/
open MeasureTheory Set
open scoped BigOperators
namespace PaperFormalization.Manuscript

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

noncomputable def varianceCosineObjective (a beta : Real) (z : VarianceCosineHilbert) : Real :=
  a/2 * (varianceCosineDecode 1 z - (varianceCosineDecode 0 z)^2) +
    beta * Real.cos (Real.pi * varianceCosineDecode 0 z)

noncomputable def varianceCosineMean (mu : Measure VarianceCosinePoint) : Real :=
  integral mu (fun x => varianceCosineScalar x)

noncomputable def varianceCosineVariance (mu : Measure VarianceCosinePoint) : Real :=
  integral mu (fun x => (varianceCosineScalar x - varianceCosineMean mu)^2)

noncomputable def varianceCosineFunctional (a beta : Real) (mu : Measure VarianceCosinePoint) : Real :=
  a/2 * varianceCosineVariance mu + beta*Real.cos (Real.pi*varianceCosineMean mu)

/-- Decoding leaves exactly the printed two-coordinate formula. -/
theorem varianceCosineObjective_formula (a beta : Real) (z : VarianceCosineHilbert) :
    varianceCosineObjective a beta z =
      a/2*(z 1 / varianceCosineWeight 1 - (z 0 / varianceCosineWeight 0)^2) +
        beta*Real.cos (Real.pi*(z 0 / varianceCosineWeight 0)) := by
  simp only [varianceCosineObjective,varianceCosineDecode,weightedCoordinateProjection_apply,
    smul_eq_mul,div_eq_mul_inv,mul_comm]

theorem varianceCosineObjective_contDiff (a beta : Real) :
    ContDiff Real 3 (varianceCosineObjective a beta) := by
  unfold varianceCosineObjective
  fun_prop

/-- U is the full original weighted Hilbert space, for every scale and radius. -/
theorem varianceCosineObjective_domains (alpha : Real) :
    SourceAllMomentDomains varianceCosineEncodedFeature alpha Set.univ := by
  intro K hK D hD z hz
  trivial

theorem varianceCosine_integrable_coordinates
    (mu : Measure VarianceCosinePoint) [IsProbabilityMeasure mu]
    (h2 : MemLp (id : VarianceCosinePoint -> VarianceCosinePoint) 2 mu) :
    Integrable (fun x => varianceCosineScalar x) mu ∧
      Integrable (fun x => (varianceCosineScalar x)^2) mu := by
  have h1 := h2.integrable (by norm_num)
  refine And.intro (varianceCosineScalar.integrable_comp h1) ?_
  have hs := h2.integrable_norm_pow (by norm_num : (2 : Nat) ≠ 0)
  simpa only [id_eq, <- varianceCosineScalar_abs, sq_abs] using hs

theorem varianceCosineFeature_integrable
    (mu : Measure VarianceCosinePoint) [IsProbabilityMeasure mu]
    (h2 : MemLp (id : VarianceCosinePoint -> VarianceCosinePoint) 2 mu) (n : Nat) :
    Integrable (varianceCosineFeature n) mu := by
  have h := varianceCosine_integrable_coordinates mu h2
  rcases n with _ | _ | n
  . exact h.1
  . exact h.2
  . exact integrable_const (0 : Real)

theorem varianceCosineEncodedFeature_integrable
    (mu : Measure VarianceCosinePoint) [IsProbabilityMeasure mu]
    (h2 : MemLp (id : VarianceCosinePoint -> VarianceCosinePoint) 2 mu) :
    Integrable varianceCosineEncodedFeature mu := by
  have h := varianceCosine_integrable_coordinates mu h2
  have hfirst := (weightedCoordinateEmbedding (H := fun _ => Real) varianceCosineWeight 0).integrable_comp h.1
  have hsecond := (weightedCoordinateEmbedding (H := fun _ => Real) varianceCosineWeight 1).integrable_comp h.2
  rw [show varianceCosineEncodedFeature = (fun x =>
    weightedCoordinateEmbedding varianceCosineWeight 0 (varianceCosineScalar x) +
    weightedCoordinateEmbedding varianceCosineWeight 1 ((varianceCosineScalar x)^2)) from
      funext varianceCosineEncodedFeature_two_terms]
  exact hfirst.add hsecond

theorem varianceCosineDecode_integral
    (mu : Measure VarianceCosinePoint) [IsProbabilityMeasure mu]
    (h2 : MemLp (id : VarianceCosinePoint -> VarianceCosinePoint) 2 mu) (n : Nat) :
    varianceCosineDecode n (integral mu varianceCosineEncodedFeature) =
      integral mu (varianceCosineFeature n) := by
  rw [<- (varianceCosineDecode n).integral_comp_comm
    (varianceCosineEncodedFeature_integrable mu h2)]
  simp only [varianceCosineDecode_feature]

theorem varianceCosineVariance_eq_second_sub_mean_sq
    (mu : Measure VarianceCosinePoint) [IsProbabilityMeasure mu]
    (h2 : MemLp (id : VarianceCosinePoint -> VarianceCosinePoint) 2 mu) :
    varianceCosineVariance mu =
      integral mu (fun x => (varianceCosineScalar x)^2) - (varianceCosineMean mu)^2 := by
  have h := varianceCosine_integrable_coordinates mu h2
  have he (x : VarianceCosinePoint) :
      (varianceCosineScalar x - varianceCosineMean mu)^2 =
      (varianceCosineScalar x)^2 - (2*varianceCosineMean mu)*varianceCosineScalar x +
        (varianceCosineMean mu)^2 := by ring
  unfold varianceCosineVariance
  simp_rw [he]
  calc
    _ = (∫ x, (varianceCosineScalar x)^2 -
        (2*varianceCosineMean mu)*varianceCosineScalar x ∂mu) +
        ∫ _ : VarianceCosinePoint, (varianceCosineMean mu)^2 ∂mu :=
      integral_add (h.2.sub (h.1.const_mul (2*varianceCosineMean mu)))
        (integrable_const ((varianceCosineMean mu)^2))
    _ = _ := by
      rw [integral_sub h.2 (h.1.const_mul (2*varianceCosineMean mu)), integral_const_mul]
      simp only [integral_const, measureReal_univ_eq_one, one_smul]
      unfold varianceCosineMean
      ring

theorem varianceCosineObjective_population_identity
    (a beta : Real) (mu : Measure VarianceCosinePoint) [IsProbabilityMeasure mu]
    (h2 : MemLp (id : VarianceCosinePoint -> VarianceCosinePoint) 2 mu) :
    Integrable varianceCosineEncodedFeature mu ∧
      varianceCosineObjective a beta (integral mu varianceCosineEncodedFeature) =
        varianceCosineFunctional a beta mu := by
  refine And.intro (varianceCosineEncodedFeature_integrable mu h2) ?_
  rw [varianceCosineObjective, varianceCosineDecode_integral mu h2 0,
    varianceCosineDecode_integral mu h2 1, varianceCosineFunctional,
    varianceCosineVariance_eq_second_sub_mean_sq mu h2]
  rfl

theorem varianceCosineFunctional_lower (a beta : Real) (ha : 0 <= a) (hb : 0 <= beta)
    (mu : Measure VarianceCosinePoint) [IsProbabilityMeasure mu]
    (h2 : MemLp (id : VarianceCosinePoint -> VarianceCosinePoint) 2 mu) :
    -beta <= varianceCosineFunctional a beta mu := by
  have hcoord := varianceCosine_integrable_coordinates mu h2
  have hcenter : Integrable (fun x => (varianceCosineScalar x-varianceCosineMean mu)^2) mu := by
    have he (x : VarianceCosinePoint) : (varianceCosineScalar x-varianceCosineMean mu)^2 =
        (varianceCosineScalar x)^2-(2*varianceCosineMean mu)*varianceCosineScalar x+(varianceCosineMean mu)^2 := by ring
    simp_rw [he]
    exact (hcoord.2.sub (hcoord.1.const_mul _)).add (integrable_const _)
  have hv : 0 <= varianceCosineVariance mu := integral_nonneg (fun _ => sq_nonneg _)
  have hc := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos (Real.pi*varianceCosineMean mu)) hb
  unfold varianceCosineFunctional
  nlinarith

/-- An odd-integer Dirac measure attains the minimum; it is not only an infimum. -/
theorem varianceCosineFunctional_dirac_one (a beta : Real) :
    varianceCosineFunctional a beta (Measure.dirac (varianceCosinePoint 1)) = -beta := by
  simp [varianceCosineFunctional,varianceCosineVariance,varianceCosineMean,
    varianceCosineScalar_point]

/-- The empirical normalisation is exactly 1/N. -/
theorem varianceCosineDecode_empirical (N : Nat) (X : SourceFiniteConfiguration N 1) (n : Nat) :
    varianceCosineDecode n (empiricalMomentMap varianceCosineEncodedFeature X) =
      (N : Real)⁻¹ * ∑ i : Fin N, varianceCosineFeature n (X i) := by
  simpa only [varianceCosineDecode, varianceCosineWeight, varianceCosineEncodedFeature,
    finiteFeatureMean, smul_eq_mul, Fintype.card_fin] using weightedCoordinateProjection_empirical_sourceWeightedFeatureMap
    1 1 1 2 0 varianceCosineFeature (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun m x => by simpa only [norm_iteratedFDeriv_zero,Nat.sub_zero] using
      varianceCosineFeature_growth m x 0 (by omega)) X n
end PaperFormalization.Manuscript
