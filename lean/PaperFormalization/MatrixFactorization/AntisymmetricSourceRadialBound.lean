import PaperFormalization.MatrixFactorization.AntisymmetricRadialL4
import PaperFormalization.MatrixFactorization.ContractionMeanL4

/-! # The printed sharp radial fitting constant for the original cap measure

This endpoint combines the proved actual L4 remainder estimate with the
actual two-factor radial pairing. The coefficient is exactly the source Cstar,
with no identification with the older polynomial envelope coefficient.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The exact source Cstar bounds the original radial fitting derivative. -/
theorem antisymmetricRadialFittingPairing_lower_source {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (r : Real) (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    -sourceRadialConstant d O a teacher *
      (productAntipodalTransportSq pole mu (reflectedMeasure mu))^2 ≤
        antisymmetricRadialFittingPairing O a pole mu teacher := by
  have he := contractionMeanRemainder_lpNorm_four_le O a hO pole r mu hcap
  have hs := pow_le_pow_left₀ lpNorm_nonneg he 2
  have hm := mul_le_mul_of_nonpos_left hs (show
      -(1/2 : Real)*((gaussianActivationL4 O a)^2+(teacherFeatureL4 d O a teacher)^2) ≤ 0 by
    have h : 0 ≤ (gaussianActivationL4 O a)^2+(teacherFeatureL4 d O a teacher)^2 :=
      add_nonneg (sq_nonneg _) (sq_nonneg _)
    nlinarith)
  calc
    _ = -(1/2 : Real)*((gaussianActivationL4 O a)^2+(teacherFeatureL4 d O a teacher)^2)*
        (gaussianSecondJetL4 O a*productAntipodalTransportSq pole mu (reflectedMeasure mu)/4)^2 := by
      unfold sourceRadialConstant
      ring
    _ ≤ _ := hm
    _ ≤ _ := antisymmetricRadialFittingPairing_lower_L4 O a hO pole r mu hcap teacher

end PaperFormalization.MatrixFactorization
