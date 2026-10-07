import PaperFormalization.MatrixFactorization.SourceGaussianL4
import PaperFormalization.MatrixFactorization.GaussianMeanFourthBound

/-! # Exact source fourth-norm bounds and printed branch coefficients

The real L4 norms refer to the original scalar Gaussian activation and actual
teacher output. The mean bound follows from proved fourth-moment integrability,
Jensen and the exact Gaussian observation law. The printed coefficients are
recorded literally; this module does not assert the later sharp force estimates.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Every original sphere probability has its actual feature L4 norm bounded
by the source scalar-Gaussian activation norm. -/
theorem meanFeature_lpNorm_four_le_gaussianActivationL4 {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] :
    lpNorm (meanFeature (finiteHermiteActivation O a) mu) 4 (stdGaussian (Weight d)) ≤
      gaussianActivationL4 O a := by
  unfold gaussianActivationL4
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      (meanFeature_stronglyMeasurable _ (finiteHermiteActivation_continuous O a) mu).aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      (finiteHermiteActivation_continuous O a).aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat,Real.rpow_ofNat]
  exact Real.rpow_le_rpow (integral_nonneg (fun z => pow_nonneg (norm_nonneg _) 4))
    (finiteHermite_mean_fourth_le_scalar O a mu) (by norm_num)

/-- The source teacher constant is bounded by M4 for the actual teacher law. -/
theorem teacherFeatureL4_le_gaussianActivationL4 {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    teacherFeatureL4 d O a teacher ≤ gaussianActivationL4 O a :=
  meanFeature_lpNorm_four_le_gaussianActivationL4 O a teacher

/-- The manuscript's Cstar, using its exact Gaussian fourth norms. Its later
radial lower bound still requires the sharp contraction-remainder estimate. -/
noncomputable def sourceRadialConstant (d : Nat) {h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (teacher : Measure (UnitSphere d)) : Real :=
  (gaussianSecondJetL4 O a)^2*
    ((gaussianActivationL4 O a)^2+(teacherFeatureL4 d O a teacher)^2)/32

/-- The manuscript's Lfit. It is not equated with the previous polynomial
fittingCurvatureConstant, nor assumed to bound the actual fitting force here. -/
noncomputable def sourceFittingConstant (d : Nat) {h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (teacher : Measure (UnitSphere d)) : Real :=
  (gaussianFirstJetL4 O a)^2*
    ((gaussianActivationL4 O a)^2+(teacherFeatureL4 d O a teacher)^2)/Real.sqrt 2

theorem sourceBranchConstants_nonneg (d : Nat) {h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (teacher : Measure (UnitSphere d)) :
    0 ≤ sourceRadialConstant d O a teacher ∧ 0 ≤ sourceFittingConstant d O a teacher := by
  constructor
  · unfold sourceRadialConstant
    positivity
  · unfold sourceFittingConstant
    positivity

end PaperFormalization.MatrixFactorization
