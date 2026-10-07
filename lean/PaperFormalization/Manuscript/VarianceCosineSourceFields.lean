import PaperFormalization.Manuscript.VarianceCosineDifferential
import PaperFormalization.Manuscript.MomentKernelMatrix
import PaperFormalization.Manuscript.SourceCanonicalEmpiricalFlow

/-! # Identify the printed scalar fields with the actual weighted source fields
M13u VERIFIED UNIT (full example application remains open). The sign in momentGradientField is the NEGATIVE gradient.
Neither a target Hessian nor a surrogate curvature is supplied as a premise.
-/
open MeasureTheory Matrix Set
open scoped BigOperators
namespace PaperFormalization.Manuscript

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

noncomputable def varianceCosineFeatureD1 (x : VarianceCosinePoint) :
    VarianceCosinePoint →L[Real] VarianceCosineHilbert :=
  (weightedCoordinateEmbedding (H := fun _ => Real) varianceCosineWeight 0).comp varianceCosineScalar +
    (2*varianceCosineScalar x) •
      (weightedCoordinateEmbedding (H := fun _ => Real) varianceCosineWeight 1).comp varianceCosineScalar

noncomputable def varianceCosineFeatureD2 :
    VarianceCosinePoint →L[Real] (VarianceCosinePoint →L[Real] VarianceCosineHilbert) :=
  2 • varianceCosineScalar.smulRight
    ((weightedCoordinateEmbedding (H := fun _ => Real) varianceCosineWeight 1).comp varianceCosineScalar)

theorem varianceCosineEncodedFeature_contDiff :
    ContDiff Real 3 varianceCosineEncodedFeature := by
  rw [show varianceCosineEncodedFeature = fun x =>
      weightedCoordinateEmbedding (H := fun _ => Real) varianceCosineWeight 0 (varianceCosineScalar x) +
      weightedCoordinateEmbedding (H := fun _ => Real) varianceCosineWeight 1 ((varianceCosineScalar x)^2) from
    funext varianceCosineEncodedFeature_two_terms]
  fun_prop

theorem varianceCosineEncodedFeature_hasFDerivAt (x : VarianceCosinePoint) :
    HasFDerivAt varianceCosineEncodedFeature (varianceCosineFeatureD1 x) x := by
  have h := ((weightedCoordinateEmbedding (H := fun _ => Real) varianceCosineWeight 0).hasFDerivAt.comp x
    varianceCosineScalar.hasFDerivAt).add
    ((weightedCoordinateEmbedding (H := fun _ => Real) varianceCosineWeight 1).hasFDerivAt.comp x
      (varianceCosineScalar.hasFDerivAt.pow 2))
  convert h using 1 <;> try rfl
  · exact funext varianceCosineEncodedFeature_two_terms
  · ext v n
    simp [varianceCosineFeatureD1]
    <;> ring

theorem varianceCosineEncodedFeature_fderiv :
    fderiv Real varianceCosineEncodedFeature = varianceCosineFeatureD1 := by
  funext x
  exact (varianceCosineEncodedFeature_hasFDerivAt x).fderiv

theorem varianceCosineEncodedFeature_second :
    fderiv Real (fderiv Real varianceCosineEncodedFeature) = fun _ => varianceCosineFeatureD2 := by
  rw [varianceCosineEncodedFeature_fderiv]
  funext x
  have h := (((varianceCosineScalar.hasFDerivAt (x := x)).const_mul 2).smul_const
    ((weightedCoordinateEmbedding (H := fun _ => Real) varianceCosineWeight 1).comp varianceCosineScalar)).const_add
      ((weightedCoordinateEmbedding (H := fun _ => Real) varianceCosineWeight 0).comp varianceCosineScalar)
  convert h.fderiv using 1 <;> try rfl
  ext v w n
  simp [varianceCosineFeatureD2]
  <;> ring

theorem varianceCosineDecode_featureD1 (x v : VarianceCosinePoint) :
    varianceCosineDecode 0 (varianceCosineFeatureD1 x v) = varianceCosineScalar v ∧
    varianceCosineDecode 1 (varianceCosineFeatureD1 x v) =
      2*varianceCosineScalar x*varianceCosineScalar v := by
  have hw0 := (sourceFeatureScale_pos 1 2 0).ne'
  have hw1 := (sourceFeatureScale_pos 1 2 1).ne'
  constructor <;> simp [varianceCosineDecode,varianceCosineFeatureD1,
    weightedCoordinateProjection,weightedCoordinateEmbedding,lp.evalCLM,lp.single_apply,Pi.single_apply,
    varianceCosineWeight,hw0,hw1,smul_eq_mul] <;> field_simp [hw0, hw1] <;> ring

theorem varianceCosineDecode_featureD2 (v w : VarianceCosinePoint) :
    varianceCosineDecode 0 (varianceCosineFeatureD2 v w) = 0 ∧
    varianceCosineDecode 1 (varianceCosineFeatureD2 v w) =
      2*varianceCosineScalar v*varianceCosineScalar w := by
  have hw := (sourceFeatureScale_pos 1 2 1).ne'
  constructor <;> simp [varianceCosineDecode,varianceCosineFeatureD2,
    weightedCoordinateProjection,weightedCoordinateEmbedding,lp.evalCLM,lp.single_apply,Pi.single_apply,
    varianceCosineWeight,hw,smul_eq_mul] <;> field_simp [hw] <;> ring

theorem varianceCosine_inner_point (v : VarianceCosinePoint) (x : Real) :
    inner Real v (varianceCosinePoint x) = varianceCosineScalar v*x := by
  simp [PiLp.inner_apply,varianceCosinePoint,varianceCosineScalar, mul_comm]

/-- The source field is -a(x-m)+beta*pi*sin(pi*m), including its exact sign. -/
theorem varianceCosine_source_field (a beta : Real) (z : VarianceCosineHilbert)
    (x : VarianceCosinePoint) :
    momentGradientField (fderiv Real varianceCosineEncodedFeature)
      (gradient (varianceCosineObjective a beta)) (z,x) =
    varianceCosinePoint (-a*(varianceCosineScalar x-varianceCosineDecode 0 z) +
      varianceCosineMeanDrift beta (varianceCosineDecode 0 z)) := by
  apply ext_inner_left Real
  intro v
  rw [momentGradientField,inner_neg_right,ContinuousLinearMap.adjoint_inner_right,
    gradient, real_inner_comm,InnerProductSpace.toDual_symm_apply,
    varianceCosine_fderiv,varianceCosineEncodedFeature_fderiv,varianceCosine_inner_point]
  simp only [varianceCosineD1,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    smul_eq_mul,(varianceCosineDecode_featureD1 x v).1,(varianceCosineDecode_featureD1 x v).2]
  ring

/-- The diagonal spatial block is a times identity, not the kernel coefficient. -/
theorem varianceCosine_source_spatial (a beta : Real) (z : VarianceCosineHilbert)
    (x : VarianceCosinePoint) :
    momentSpatialHessian (fderiv Real (fderiv Real varianceCosineEncodedFeature) x)
      (gradient (varianceCosineObjective a beta) z) = a • ContinuousLinearMap.id Real VarianceCosinePoint := by
  ext v : 1
  apply ext_inner_left Real
  intro w
  rw [inner_momentSpatialHessian,varianceCosineEncodedFeature_second,
    gradient,InnerProductSpace.toDual_symm_apply,varianceCosine_fderiv]
  have he := varianceCosineDecode_featureD2 v w
  simp only [varianceCosineD1,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    smul_eq_mul,he.1,he.2,ContinuousLinearMap.id_apply,inner_smul_right]
  rw [<- varianceCosinePoint_scalar v,varianceCosine_inner_point]
  simp only [varianceCosineScalar_point]
  ring

/-- The two-slot source Hessian kernel is spatially constant. -/
theorem varianceCosine_source_integral_hessian (a beta : Real) (z : VarianceCosineHilbert)
    (x y : VarianceCosinePoint) :
    momentIntegralHessian (fderiv Real varianceCosineEncodedFeature x)
      (fderiv Real varianceCosineEncodedFeature y) (momentObjectiveHessian (varianceCosineObjective a beta) z) =
      varianceCosineKernel a beta (varianceCosineDecode 0 z) • ContinuousLinearMap.id Real VarianceCosinePoint := by
  ext v : 1
  apply ext_inner_left Real
  intro u
  rw [inner_momentIntegralHessian,inner_momentObjectiveHessian,varianceCosine_second_fderiv,
    varianceCosineEncodedFeature_fderiv]
  simp only [varianceCosineD2,ContinuousLinearMap.smul_apply,ContinuousLinearMap.smulRight_apply,
    smul_eq_mul,(varianceCosineDecode_featureD1 x u).1,(varianceCosineDecode_featureD1 y v).1,
    ContinuousLinearMap.id_apply,inner_smul_right]
  rw [<- varianceCosinePoint_scalar v,varianceCosine_inner_point]
  simp only [varianceCosineScalar_point]
  ring

theorem varianceCosine_source_kernel_matrix (a beta : Real) (z : VarianceCosineHilbert)
    (x y : VarianceCosinePoint) (i j : Fin 1) :
    actualMomentKernelMatrix varianceCosineEncodedFeature (varianceCosineObjective a beta) z x y i j =
      varianceCosineKernel a beta (varianceCosineDecode 0 z) := by
  rw [actualMomentKernelMatrix,varianceCosine_source_integral_hessian,euclideanOperatorMatrix_entry]
  have hi : i=0 := Subsingleton.elim _ _
  have hj : j=0 := Subsingleton.elim _ _
  subst i; subst j
  simp

noncomputable def varianceCosineEmpiricalMean {N : Nat} (X : SourceFiniteConfiguration N 1) : Real :=
  (N : Real)⁻¹ * ∑ i : Fin N, varianceCosineScalar (X i)

/-- This is the existing source drift, not a newly postulated particle ODE. -/
theorem varianceCosine_source_empirical_drift {N : Nat} (a beta : Real)
    (X : SourceFiniteConfiguration N 1) (i : Fin N) :
    sourceExactEmpiricalDrift 1 2 varianceCosineFeature (varianceCosineObjective a beta) X i =
      varianceCosinePoint (-a*(varianceCosineScalar (X i)-varianceCosineEmpiricalMean X) +
        varianceCosineMeanDrift beta (varianceCosineEmpiricalMean X)) := by
  change momentGradientField (fderiv Real varianceCosineEncodedFeature)
    (gradient (varianceCosineObjective a beta))
    (empiricalMomentMap varianceCosineEncodedFeature X,X i) = _
  rw [varianceCosine_source_field,varianceCosineDecode_empirical]
  rfl
end PaperFormalization.Manuscript
