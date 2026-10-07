import PaperFormalization.MatrixFactorization.SphericalFittingGradientVariation

/-! # The original fitting force on the antisymmetric branch

The output force and its Gaussian spherical field are derived from the
literal matrix residual. The square-completion estimate is the algebraic
step of the pole-contraction argument; an actual contraction remainder
bound is still needed before concluding radial dissipation.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def antisymmetricOutputForce {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (mu teacher : Measure (UnitSphere d)) (z : Weight d) : Weight h :=
  let hmu := meanFeature (finiteHermiteActivation O a) mu z
  let b := meanFeature (finiteHermiteActivation O a) teacher z
  norm hmu^2 • hmu + inner Real hmu b • b

/-- The first output derivative has the positive branch sign. -/
theorem fittingOutputGradient_antibranch_zero {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n)
    (mu teacher : Measure (UnitSphere d)) [IsFiniteMeasure mu] (z : Weight d) :
    fittingOutputGradient O a mu (reflectedMeasure mu) teacher teacher 0 z =
      antisymmetricOutputForce O a mu teacher z := by
  have hr := meanFeature_reflected _ (finiteHermiteActivation_continuous O a)
    (finiteHermiteActivation_odd O a hO) mu z
  simp only [fittingOutputGradient, ite_true, hr, norm_neg, inner_neg_right,
    neg_smul, sub_neg_eq_add, antisymmetricOutputForce]
  rw [real_inner_comm]

/-- The second output derivative is the negative of the first. -/
theorem fittingOutputGradient_antibranch_one {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n)
    (mu teacher : Measure (UnitSphere d)) [IsFiniteMeasure mu] (z : Weight d) :
    fittingOutputGradient O a mu (reflectedMeasure mu) teacher teacher 1 z =
      -antisymmetricOutputForce O a mu teacher z := by
  have hr := meanFeature_reflected _ (finiteHermiteActivation_continuous O a)
    (finiteHermiteActivation_odd O a hO) mu z
  simp only [fittingOutputGradient, show (1 : Fin 2) ≠ 0 by decide, if_false, hr,
    smul_neg, antisymmetricOutputForce]
  rw [real_inner_comm]
  module

/-- A norm bound retaining the vanishing student feature factor. -/
theorem antisymmetricOutputForce_norm_le {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (mu teacher : Measure (UnitSphere d)) (z : Weight d) :
    norm (antisymmetricOutputForce O a mu teacher z) ≤
      (norm (meanFeature (finiteHermiteActivation O a) mu z)^2 +
        norm (meanFeature (finiteHermiteActivation O a) teacher z)^2)*
        norm (meanFeature (finiteHermiteActivation O a) mu z) := by
  unfold antisymmetricOutputForce
  dsimp only
  calc
    _ ≤ norm (norm (meanFeature (finiteHermiteActivation O a) mu z)^2 •
        meanFeature (finiteHermiteActivation O a) mu z) +
        norm (inner Real (meanFeature (finiteHermiteActivation O a) mu z)
          (meanFeature (finiteHermiteActivation O a) teacher z) •
          meanFeature (finiteHermiteActivation O a) teacher z) := norm_add_le _ _
    _ ≤ norm (meanFeature (finiteHermiteActivation O a) mu z)^2*
        norm (meanFeature (finiteHermiteActivation O a) mu z) +
        (norm (meanFeature (finiteHermiteActivation O a) mu z)*
          norm (meanFeature (finiteHermiteActivation O a) teacher z))*
          norm (meanFeature (finiteHermiteActivation O a) teacher z) := by
      simp only [norm_smul, Real.norm_eq_abs, abs_pow,
        abs_of_nonneg (norm_nonneg (meanFeature (finiteHermiteActivation O a) mu z))]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (abs_real_inner_le_norm (meanFeature (finiteHermiteActivation O a) mu z)
          (meanFeature (finiteHermiteActivation O a) teacher z))
        (norm_nonneg (meanFeature (finiteHermiteActivation O a) teacher z)))
    _ = _ := by ring

/-- The field remains the actual Gaussian integral after branch specialization. -/
theorem sphericalFittingGradient_antibranch_formula {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n)
    (mu teacher : Measure (UnitSphere d)) [IsFiniteMeasure mu] (w : UnitSphere d) :
    sphericalFittingGradient O a mu (reflectedMeasure mu) teacher teacher 0 w =
      ∫ z, inner Real (antisymmetricOutputForce O a mu teacher z)
        (finiteHermiteActivationJet 1 O a (inner Real w.val z)) •
        transverseProjection w z ∂stdGaussian (Weight d) := by
  simp only [sphericalFittingGradient, fittingGradientIntegrand,
    fittingOutputGradient_antibranch_zero O a hO]

/-- Both factors move along the antisymmetric branch in this output derivative. -/
theorem matrixPointFirst_antibranch {h : Nat} (x b dx : Weight h) :
    matrixPointFirst (outer b b) x (-x) dx (-dx) =
      2*inner Real (norm x^2 • x+inner Real x b • b) dx := by
  rw [matrixPointFirst_output_gradients]
  simp only [norm_neg, inner_neg_right, neg_smul, sub_neg_eq_add, smul_neg,
    inner_sub_left, inner_neg_left, inner_add_left, real_inner_smul_left]
  rw [real_inner_comm b x]
  ring

/-- The exact source square completion preserves the factor one-half.
The actual analytic contraction remainder must subsequently be supplied. -/
theorem antibranch_force_square_completion {h : Nat} (x b e : Weight h) :
    -(1/2 : Real)*(norm x^2+norm b^2)*norm e^2 ≤
      2*inner Real (norm x^2 • x+inner Real x b • b) (x+e) := by
  have hxe := neg_le_of_abs_le (abs_real_inner_le_norm x e)
  have hxe' := mul_le_mul_of_nonneg_left hxe (sq_nonneg (norm x))
  have hs := mul_nonneg (sq_nonneg (norm x)) (sq_nonneg (2*norm x-norm e))
  have he := pow_le_pow_left₀ (abs_nonneg (inner Real b e))
    (abs_real_inner_le_norm b e) 2
  simp only [sq_abs, mul_pow] at he
  have hb := sq_nonneg (2*inner Real x b+inner Real b e)
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_self_eq_norm_sq]
  have hbx : inner Real b x = inner Real x b := real_inner_comm _ _
  rw [hbx]
  nlinarith

end PaperFormalization.MatrixFactorization
