import PaperFormalization.MatrixFactorization.GaussianOutputL4Bounds
import PaperFormalization.MatrixFactorization.GaussianFourthHolder
import PaperFormalization.MatrixFactorization.AntisymmetricRadialFittingPairing
import PaperFormalization.MatrixFactorization.ContractionRadialFittingBound

/-! # The actual radial fitting pairing with its exact L4 remainder coefficient

The original cap measure and actual assigned-pole contraction are retained.
Polynomial bounds establish finiteness, while the quantitative lower bound
uses the true L4 norms and the exact one-half square completion. A sharp
remainder estimate is a separate analytic input to be derived from this model.
-/
open MeasureTheory ProbabilityTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The actual mean-feature contraction remainder has a finite fourth moment;
its quantitative norm is not replaced by the domination envelope. -/
theorem contractionMeanRemainder_memLp_four {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (r : Real) (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu) :
    MemLp (contractionMeanRemainder O a pole mu) 4 (stdGaussian (Weight d)) := by
  letI : IsProbabilityMeasure mu := hcap.probability
  let Z := productAntipodalTransportSq pole mu (reflectedMeasure mu)
  have hZ : 0 ≤ Z := add_nonneg (sphericalWassersteinSq_nonneg mu (antipodalMeasure pole))
    (sphericalWassersteinSq_nonneg (reflectedMeasure mu) (antipodalMeasure pole))
  have hm := contractionMeanRemainder_stronglyMeasurable O a hO pole r mu hcap
  have hi : Integrable (fun z : Weight d => (Z/4)^4*(fittingFeatureEnvelope O a z)^4)
      (stdGaussian (Weight d)) := by
    simpa only [one_mul] using
      (fittingFeatureEnvelope_gaussian_integrable (d := d) O a 1 4).const_mul ((Z/4)^4)
  have he : Integrable (fun z : Weight d => norm (contractionMeanRemainder O a pole mu z)^4)
      (stdGaussian (Weight d)) := by
    apply hi.mono' (hm.norm.pow 4).aestronglyMeasurable
    apply Eventually.of_forall
    intro z
    change norm (norm (contractionMeanRemainder O a pole mu z)^4) ≤
      (Z/4)^4*(fittingFeatureEnvelope O a z)^4
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    have hb : norm (contractionMeanRemainder O a pole mu z) ≤ Z/4*fittingFeatureEnvelope O a z :=
      (contractionMeanRemainder_product_norm_le O a hO pole r mu hcap z).trans
        (mul_le_mul_of_nonneg_left (fittingFeatureEnvelope_bounds O a z).2.2.1 (by positivity))
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hb 4
  apply (integrable_norm_rpow_iff hm.aestronglyMeasurable (by norm_num : (4 : ENNReal) ≠ 0)
    (by norm_num : (4 : ENNReal) ≠ ⊤)).mp
  simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using he

/-- The actual two-factor radial pairing satisfies the exact source square
completion bound before any quantitative remainder estimate is substituted. -/
theorem antisymmetricRadialFittingPairing_lower_L4 {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (r : Real) (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    -(1/2 : Real)*((gaussianActivationL4 O a)^2+(teacherFeatureL4 d O a teacher)^2)*
      (lpNorm (contractionMeanRemainder O a pole mu) 4 (stdGaussian (Weight d)))^2 ≤
        antisymmetricRadialFittingPairing O a pole mu teacher := by
  letI : IsProbabilityMeasure mu := hcap.probability
  let H := meanFeature (finiteHermiteActivation O a) mu
  let B := meanFeature (finiteHermiteActivation O a) teacher
  let E := contractionMeanRemainder O a pole mu
  let Q := fun z => (norm (H z)^2+norm (B z)^2)*norm (E z)^2
  have hH : MemLp H 4 (stdGaussian (Weight d)) := teacherFeature_memLp_four O a mu
  have hB : MemLp B 4 (stdGaussian (Weight d)) := teacherFeature_memLp_four O a teacher
  have hE : MemLp E 4 (stdGaussian (Weight d)) := contractionMeanRemainder_memLp_four O a hO pole r mu hcap
  have h1 := four_norm_integrable_and_le hH hH hE hE
  have h2 := four_norm_integrable_and_le hB hB hE hE
  have hQeq : Q = fun z => norm (H z)*norm (H z)*norm (E z)*norm (E z)+
      norm (B z)*norm (B z)*norm (E z)*norm (E z) := by funext z; dsimp only [Q]; ring
  have hQi : Integrable Q (stdGaussian (Weight d)) := by
    rw [hQeq]
    exact h1.1.add h2.1
  have hQle : (∫ z, Q z ∂stdGaussian (Weight d)) ≤
      ((gaussianActivationL4 O a)^2+(teacherFeatureL4 d O a teacher)^2)*
        (lpNorm E 4 (stdGaussian (Weight d)))^2 := by
    rw [hQeq,integral_add h1.1 h2.1]
    have hh := add_le_add h1.2 h2.2
    have hmean := meanFeature_lpNorm_four_le_gaussianActivationL4 O a mu
    calc
      _ ≤ lpNorm H 4 (stdGaussian (Weight d))*lpNorm H 4 (stdGaussian (Weight d))*
          lpNorm E 4 (stdGaussian (Weight d))*lpNorm E 4 (stdGaussian (Weight d)) +
        lpNorm B 4 (stdGaussian (Weight d))*lpNorm B 4 (stdGaussian (Weight d))*
          lpNorm E 4 (stdGaussian (Weight d))*lpNorm E 4 (stdGaussian (Weight d)) := hh
      _ = ((lpNorm H 4 (stdGaussian (Weight d)))^2+(teacherFeatureL4 d O a teacher)^2)*
          (lpNorm E 4 (stdGaussian (Weight d)))^2 := by
        change _ = ((lpNorm H 4 _)^2+(lpNorm B 4 _)^2)*(lpNorm E 4 _)^2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (add_le_add (pow_le_pow_left₀ lpNorm_nonneg hmean 2) le_rfl) (sq_nonneg _)
  have hpoint (z : Weight d) : (-1/2 : Real)*Q z ≤
      2*inner Real (antisymmetricOutputForce O a mu teacher z)
        (meanFeatureAlongContractionFirst 0 O a pole mu z 1) := by
    have hsq := antibranch_force_square_completion (H z) (B z) (E z)
    have he : H z+E z = meanFeatureAlongContractionFirst 0 O a pole mu z 1 := by
      dsimp only [H,E,contractionMeanRemainder]
      module
    rw [he] at hsq
    simpa only [Q,H,B,antisymmetricOutputForce,mul_assoc,neg_div] using hsq
  have hs := integral_mono (hQi.const_mul (-1/2 : Real))
    ((contraction_radial_gaussian_integrable O a hO pole r mu hcap teacher).const_mul 2) hpoint
  simp only [integral_const_mul] at hs
  calc
    _ = (-1/2 : Real)*(((gaussianActivationL4 O a)^2+(teacherFeatureL4 d O a teacher)^2)*
        (lpNorm E 4 (stdGaussian (Weight d)))^2) := by ring
    _ ≤ (-1/2 : Real)*(∫ z, Q z ∂stdGaussian (Weight d)) :=
      mul_le_mul_of_nonpos_left hQle (by norm_num)
    _ ≤ 2*∫ z, inner Real (antisymmetricOutputForce O a mu teacher z)
        (meanFeatureAlongContractionFirst 0 O a pole mu z 1) ∂stdGaussian (Weight d) := hs
    _ = _ := (antisymmetricRadialFittingPairing_eq O a hO pole r mu hcap teacher).symm

end PaperFormalization.MatrixFactorization
