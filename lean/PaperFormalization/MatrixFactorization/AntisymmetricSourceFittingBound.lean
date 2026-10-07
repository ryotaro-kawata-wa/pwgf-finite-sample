import PaperFormalization.MatrixFactorization.AntisymmetricFittingL4
import PaperFormalization.MatrixFactorization.AntisymmetricMeanL4

/-! # The printed fitting constant on the antisymmetric branch

The bound combines the actual Gaussian field estimate and the proved sharp
mean-feature estimate. It applies to both output factors at every sphere point,
and keeps the manuscript's factor of one over the square root of two.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The manuscript's Lfit controls both actual fitting fields in terms of the
true reflected product transport distance, including distance zero. -/
theorem antisymmetric_sphericalFittingGradient_norm_source {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (r : Real) (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (i : Fin 2) (w : UnitSphere d) :
    norm (sphericalFittingGradient O a mu (reflectedMeasure mu) teacher teacher i w) ≤
      sourceFittingConstant d O a teacher *
        Real.sqrt (productAntipodalTransportSq pole mu (reflectedMeasure mu)) := by
  letI : IsProbabilityMeasure mu := hcap.probability
  have hm := antisymmetric_mean_lpNorm_four_le O a hO pole r mu hcap
  have hc : 0 ≤ gaussianFirstJetL4 O a *
      ((gaussianActivationL4 O a)^2+(teacherFeatureL4 d O a teacher)^2) :=
    mul_nonneg lpNorm_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
  calc
    _ ≤ gaussianFirstJetL4 O a *
        ((gaussianActivationL4 O a)^2+(teacherFeatureL4 d O a teacher)^2) *
        lpNorm (meanFeature (finiteHermiteActivation O a) mu) 4 (stdGaussian (Weight d)) :=
      antisymmetric_sphericalFittingGradient_norm_L4 O a hO mu teacher i w
    _ ≤ gaussianFirstJetL4 O a *
        ((gaussianActivationL4 O a)^2+(teacherFeatureL4 d O a teacher)^2) *
        (gaussianFirstJetL4 O a *
          Real.sqrt (productAntipodalTransportSq pole mu (reflectedMeasure mu)/2)) :=
      mul_le_mul_of_nonneg_left hm hc
    _ = _ := by
      rw [Real.sqrt_div' _ (by norm_num : (0 : Real) ≤ 2)]
      unfold sourceFittingConstant
      ring

end PaperFormalization.MatrixFactorization
