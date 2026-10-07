import PaperFormalization.MatrixFactorization.SourceGaussianL4
import PaperFormalization.MatrixFactorization.PoleContractionFeatureRemainder
import PaperFormalization.MatrixFactorization.FiniteMeasureL4Average

/-! # Exact source L4 bounds for individual pole contractions

The actual first jet is integrated over the unit interval. The endpoint
remainder integrates the actual second jet with the time weight s, whose
measure has mass one-half. Polynomial Gaussian envelopes justify all joint
integrals, while the source constants are retained in the fourth-norm bounds.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The actual time/input first and second jets are jointly continuous. -/
theorem sphericalFeature_jets_continuous_time_input {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (y : UnitSphere d) (v : Weight d)
    (hv : inner Real y.val v = 0) :
    Continuous (fun sz : Real × Weight d => sphericalFeatureFirst 0 O a y v hv sz.2 sz.1) ∧
    Continuous (fun sz : Real × Weight d => sphericalFeatureSecond 0 O a y v hv sz.2 sz.1) := by
  have hc : Continuous (sphereExpVelocity y v) :=
    continuous_iff_continuousAt.mpr (fun t => (sphereExpVelocity_hasDerivAt y v t).continuousAt)
  have hp : Continuous (fun sz : Real × Weight d =>
      inner Real (geodesicPoint y v hv sz.1).val sz.2) :=
    ((continuous_subtype_val.comp (geodesicPoint_continuous y v hv)).comp continuous_fst).inner
      (𝕜 := Real) continuous_snd
  have ht : Continuous (fun sz : Real × Weight d =>
      inner Real (sphereExpVelocity y v sz.1) sz.2) :=
    (hc.comp continuous_fst).inner (𝕜 := Real) continuous_snd
  constructor
  · exact ht.smul ((finiteHermiteActivationJet_continuous 1 O a).comp hp)
  · exact ((ht.pow 2).smul ((finiteHermiteActivationJet_continuous 2 O a).comp hp)).sub
      ((continuous_const.mul hp).smul ((finiteHermiteActivationJet_continuous 1 O a).comp hp))

/-- Every required time/Gaussian moment is derived from the original polynomial
envelopes, for any finite time measure. -/
theorem sphericalFeature_jets_time_gaussian_integrable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (y : UnitSphere d) (v : Weight d)
    (hv : inner Real y.val v = 0) (nu : Measure Real) [IsFiniteMeasure nu] :
    Integrable (fun sz : Real × Weight d => sphericalFeatureFirst 0 O a y v hv sz.2 sz.1)
      (nu.prod (stdGaussian (Weight d))) ∧
    Integrable (fun sz : Real × Weight d => norm (sphericalFeatureFirst 0 O a y v hv sz.2 sz.1)^4)
      (nu.prod (stdGaussian (Weight d))) ∧
    Integrable (fun sz : Real × Weight d => sphericalFeatureSecond 0 O a y v hv sz.2 sz.1)
      (nu.prod (stdGaussian (Weight d))) ∧
    Integrable (fun sz : Real × Weight d => norm (sphericalFeatureSecond 0 O a y v hv sz.2 sz.1)^4)
      (nu.prod (stdGaussian (Weight d))) := by
  have hc := sphericalFeature_jets_continuous_time_input O a y v hv
  have hi1 (q : Nat) : Integrable (fun sz : Real × Weight d =>
      norm (sphericalFeatureFirst 0 O a y v hv sz.2 sz.1)^q)
      (nu.prod (stdGaussian (Weight d))) := by
    have hd := (((featureEnvelopes_gaussian_pow_integrable (d := d) 0 O a q).2.1).const_mul
      (norm v^q)).comp_snd nu
    apply hd.mono' (hc.1.norm.pow q).aestronglyMeasurable
    filter_upwards with sz
    change norm (norm (sphericalFeatureFirst 0 O a y v hv sz.2 sz.1)^q) ≤
      norm v^q * (featureFirstEnvelope 0 O a sz.2)^q
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _), ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (sphericalFeatureFirst_bound 0 O a y v hv sz.2 sz.1) q
  have hi2 (q : Nat) : Integrable (fun sz : Real × Weight d =>
      norm (sphericalFeatureSecond 0 O a y v hv sz.2 sz.1)^q)
      (nu.prod (stdGaussian (Weight d))) := by
    have hd := (((featureEnvelopes_gaussian_pow_integrable (d := d) 0 O a q).2.2).const_mul
      ((norm v^2)^q)).comp_snd nu
    apply hd.mono' (hc.2.norm.pow q).aestronglyMeasurable
    filter_upwards with sz
    change norm (norm (sphericalFeatureSecond 0 O a y v hv sz.2 sz.1)^q) ≤
      (norm v^2)^q * (featureSecondEnvelope 0 O a sz.2)^q
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _), ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (sphericalFeatureSecond_bound 0 O a y v hv sz.2 sz.1) q
  refine ⟨?_, hi1 4, ?_, hi2 4⟩
  · apply (integrable_norm_iff hc.1.aestronglyMeasurable).mp
    simpa only [pow_one] using hi1 1
  · apply (integrable_norm_iff hc.2.aestronglyMeasurable).mp
    simpa only [pow_one] using hi2 1

/-- The time weight s on the unit interval gives exactly the weighted FTC integral. -/
theorem unitInterval_timeWeight_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] [CompleteSpace E] (g : Real → E) :
    (∫ s, g s ∂(volume.restrict (Icc (0 : Real) 1)).withDensity (fun s => ENNReal.ofReal s)) =
      ∫ s in (0 : Real)..1, s • g s := by
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Eventually.of_forall (fun s => ENNReal.ofReal_lt_top)),
    intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  rw [ENNReal.toReal_ofReal hs.1]

/-- The actual feature difference along the shortest contraction has the exact
source first-jet L4 bound, with the spherical angular distance. -/
theorem poleContractionFeatureDifference_lpNorm_four_le {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (y w : UnitSphere d) (hs : sphericalDistance y w < Real.pi) :
    lpNorm (fun z : Weight d => finiteHermiteActivation O a (inner Real w.val z) -
      finiteHermiteActivation O a (inner Real y.val z)) 4 (stdGaussian (Weight d)) ≤
      gaussianFirstJetL4 O a * sphericalDistance y w := by
  let v := sphericalLog y w hs
  have hv : inner Real y.val v = 0 := sphericalLog_tangent y w hs
  let nu : Measure Real := volume.restrict (Icc 0 1)
  have hc := sphericalFeature_jets_continuous_time_input O a y v hv
  have hi := sphericalFeature_jets_time_gaussian_integrable O a y v hv nu
  have hb := finiteMeasure_lpNorm_four_average_le nu (stdGaussian (Weight d))
    (fun s z => sphericalFeatureFirst 0 O a y v hv z s)
    (norm v * gaussianFirstJetL4 O a) (mul_nonneg (norm_nonneg _) lpNorm_nonneg)
    hi.1 hi.2.1 (Eventually.of_forall (fun s =>
      (sphericalFeatureFirst_lpNorm_four O a y v hv s).le))
  have hpoint : geodesicPoint y v hv 1 = w := poleContraction_one y w hs
  have he : (fun z : Weight d => finiteHermiteActivation O a (inner Real w.val z) -
      finiteHermiteActivation O a (inner Real y.val z)) =
      (fun z => ∫ s, sphericalFeatureFirst 0 O a y v hv z s ∂nu) := by
    funext z
    have hit := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s (_ : s ∈ uIcc (0 : Real) 1) => sphericalFeatureJet_hasDerivAt 0 O a y v hv z s)
      ((hc.1.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1)
    rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc] at hit
    simpa only [sphericalFeatureJet_zero_order, hpoint, geodesicPoint_zero] using hit.symm
  rw [← he] at hb
  have hmass : nu.real univ = 1 := by simp [nu, Measure.real]
  rw [hmass, mul_one, sphericalLog_norm y w hs] at hb
  simpa only [mul_comm] using hb

/-- The actual endpoint remainder retains exactly one-half of the source
second-jet L4 bound, from the weighted time integral. -/
theorem poleContractionFeatureRemainder_lpNorm_four_le {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (y w : UnitSphere d) (hs : sphericalDistance y w < Real.pi) :
    lpNorm (poleContractionFeatureRemainder O a y w) 4 (stdGaussian (Weight d)) ≤
      gaussianSecondJetL4 O a * (sphericalDistance y w)^2 / 2 := by
  let v := sphericalLog y w hs
  have hv : inner Real y.val v = 0 := sphericalLog_tangent y w hs
  let nu : Measure Real := (volume.restrict (Icc (0 : Real) 1)).withDensity (fun s => ENNReal.ofReal s)
  have hid : Integrable (fun s : Real => s) (volume.restrict (Icc 0 1)) :=
    continuous_id.integrableOn_Icc
  letI : IsFiniteMeasure nu := isFiniteMeasure_withDensity_ofReal hid.hasFiniteIntegral
  have hi := sphericalFeature_jets_time_gaussian_integrable O a y v hv nu
  have hb := finiteMeasure_lpNorm_four_average_le nu (stdGaussian (Weight d))
    (fun s z => sphericalFeatureSecond 0 O a y v hv z s)
    (norm v^2 * gaussianSecondJetL4 O a) (mul_nonneg (sq_nonneg _) lpNorm_nonneg)
    hi.2.2.1 hi.2.2.2 (Eventually.of_forall (fun s =>
      (sphericalFeatureSecond_lpNorm_four O a y v hv s).le))
  have hpoint : geodesicPoint y v hv 1 = w := poleContraction_one y w hs
  have hvelocity : sphereExpVelocity y v 1 = poleGradient y w := poleContractionVelocity_one y w hs
  have he : poleContractionFeatureRemainder O a y w =
      (fun z => ∫ s, sphericalFeatureSecond 0 O a y v hv z s ∂nu) := by
    funext z
    have hrem := first_jet_remainder_integral
      (sphericalFeatureJet 0 O a y v hv z) (sphericalFeatureFirst 0 O a y v hv z)
      (sphericalFeatureSecond 0 O a y v hv z)
      (sphericalFeatureJet_hasDerivAt 0 O a y v hv z)
      (sphericalFeatureFirst_hasDerivAt 0 O a y v hv z)
      (sphericalFeatureSecond_continuous_time 0 O a y v hv z)
    change _ = ∫ s, sphericalFeatureSecond 0 O a y v hv z s
      ∂(volume.restrict (Icc (0 : Real) 1)).withDensity (fun s => ENNReal.ofReal s)
    rw [unitInterval_timeWeight_integral]
    simpa only [sphericalFeatureFirst, sphericalFeatureJet, Nat.zero_add,
      hpoint, hvelocity, geodesicPoint_zero, finiteHermiteActivationJet_zero,
      poleContractionFeatureRemainder] using hrem
  rw [← he] at hb
  have hmass : nu.real univ = 1/2 := by
    calc
      _ = ∫ _s, (1 : Real) ∂nu := by simp
      _ = ∫ s in (0 : Real)..1, s • (1 : Real) := unitInterval_timeWeight_integral _
      _ = _ := by simp only [smul_eq_mul, mul_one]; rw [integral_id]; norm_num
  rw [hmass, sphericalLog_norm y w hs] at hb
  convert hb using 1
  ring

end PaperFormalization.MatrixFactorization
