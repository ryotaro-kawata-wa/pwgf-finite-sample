import PaperFormalization.MatrixFactorization.SphericalFittingGradient
import PaperFormalization.MatrixFactorization.TransverseFeatureSignal

/-! # Exchange and reflection covariance of the actual fitting field

All identities concern the original finite-Hermite mean features and the
actual Gaussian integral defining the particle field. They do not assume a
flow exists or infer branch invariance without a uniqueness argument.
-/
open MeasureTheory ProbabilityTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Reflection acts on the original marginal rather than only on moments. -/
theorem finiteHermite_mean_reflected {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n)
    (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu] (z : Weight d) :
    meanFeature (finiteHermiteActivation O a) (reflectedMeasure mu) z =
      -meanFeature (finiteHermiteActivation O a) mu z :=
  meanFeature_reflected _ (finiteHermiteActivation_continuous O a)
    (finiteHermiteActivation_odd O a hO) mu z

/-- Antipodal points have the same orthogonal tangent projection. -/
theorem transverseProjection_reflect {d : Nat} (w : UnitSphere d) (z : Weight d) :
    transverseProjection (reflect w) z = transverseProjection w z := by
  simp only [transverseProjection, reflect_val, inner_neg_left, neg_smul, smul_neg, neg_neg]

/-- Exchange covariance also permits distinct teacher factors when exchanged. -/
theorem fittingOutputGradient_exchange {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d))
    (i : Fin 2) (z : Weight d) :
    fittingOutputGradient O a mu2 mu1 teacher2 teacher1 i z =
      fittingOutputGradient O a mu1 mu2 teacher1 teacher2 i.rev z := by
  fin_cases i <;> simp [fittingOutputGradient]

theorem sphericalFittingGradient_exchange {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d))
    (i : Fin 2) (w : UnitSphere d) :
    sphericalFittingGradient O a mu2 mu1 teacher2 teacher1 i w =
      sphericalFittingGradient O a mu1 mu2 teacher1 teacher2 i.rev w := by
  fin_cases i <;> simp [sphericalFittingGradient, fittingGradientIntegrand, fittingOutputGradient]

/-- Oddness changes the actual output field by a sign after reflection and exchange. -/
theorem fittingOutputGradient_reflection_exchange {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n)
    (mu1 mu2 teacher : Measure (UnitSphere d)) [IsFiniteMeasure mu1] [IsFiniteMeasure mu2]
    (i : Fin 2) (z : Weight d) :
    fittingOutputGradient O a (reflectedMeasure mu2) (reflectedMeasure mu1) teacher teacher i z =
      -fittingOutputGradient O a mu1 mu2 teacher teacher i.rev z := by
  fin_cases i <;> simp [fittingOutputGradient, finiteHermite_mean_reflected O a hO] <;> module

theorem fittingGradientIntegrand_reflection_exchange {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n)
    (mu1 mu2 teacher : Measure (UnitSphere d)) [IsFiniteMeasure mu1] [IsFiniteMeasure mu2]
    (i : Fin 2) (w : UnitSphere d) (z : Weight d) :
    fittingGradientIntegrand O a (reflectedMeasure mu2) (reflectedMeasure mu1)
      teacher teacher i (reflect w) z =
      -fittingGradientIntegrand O a mu1 mu2 teacher teacher i.rev w z := by
  simp only [fittingGradientIntegrand, fittingOutputGradient_reflection_exchange O a hO,
    reflect_val, inner_neg_left, finiteHermiteActivationJet_one_even O a hO,
    transverseProjection_reflect, neg_smul]

/-- This is the actual Gaussian force identity, with the same input in both factors. -/
theorem sphericalFittingGradient_reflection_exchange {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n)
    (mu1 mu2 teacher : Measure (UnitSphere d)) [IsFiniteMeasure mu1] [IsFiniteMeasure mu2]
    (i : Fin 2) (w : UnitSphere d) :
    sphericalFittingGradient O a (reflectedMeasure mu2) (reflectedMeasure mu1)
      teacher teacher i (reflect w) =
      -sphericalFittingGradient O a mu1 mu2 teacher teacher i.rev w := by
  simp only [sphericalFittingGradient, fittingGradientIntegrand_reflection_exchange O a hO,
    integral_neg]

/-- The antisymmetric branch has the source's reflected component relation. -/
theorem sphericalFittingGradient_antibranch {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n)
    (mu teacher : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    (i : Fin 2) (w : UnitSphere d) :
    sphericalFittingGradient O a mu (reflectedMeasure mu) teacher teacher i (reflect w) =
      -sphericalFittingGradient O a mu (reflectedMeasure mu) teacher teacher i.rev w := by
  simpa only [reflectedMeasure_involutive] using
    sphericalFittingGradient_reflection_exchange O a hO mu (reflectedMeasure mu) teacher i w

/-- The same-density branch has identical fitting fields in its two components. -/
theorem sphericalFittingGradient_same_density {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (mu teacher : Measure (UnitSphere d)) (w : UnitSphere d) :
    sphericalFittingGradient O a mu mu teacher teacher 0 w =
      sphericalFittingGradient O a mu mu teacher teacher 1 w :=
  sphericalFittingGradient_exchange O a mu mu teacher teacher 0 w

/-- Both fitting fields vanish at the antipodal zero-output center. -/
theorem sphericalFittingGradient_antipodal {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n)
    (pole : UnitSphere d) (teacher1 teacher2 : Measure (UnitSphere d))
    (i : Fin 2) (w : UnitSphere d) :
    sphericalFittingGradient O a (antipodalMeasure pole) (antipodalMeasure pole)
      teacher1 teacher2 i w = 0 := by
  unfold sphericalFittingGradient fittingGradientIntegrand fittingOutputGradient
  simp only [finiteHermite_mean_antipodal O a hO, norm_zero, zero_pow (by decide : 2 ≠ 0),
    zero_smul, inner_zero_right, sub_self, ite_self, inner_zero_left, integral_zero]

end PaperFormalization.MatrixFactorization
