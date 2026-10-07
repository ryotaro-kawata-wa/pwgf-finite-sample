import PaperFormalization.Manuscript.WeightedFeatureMap
import PaperFormalization.Manuscript.SourceFinalTrackingStatement
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # The actual two-coordinate source feature of the variance--cosine example
M13u verified unit (full example application remains open). Source index m=1,2 is Lean index n=0,1.
The particle space is the original EuclideanSpace R (Fin 1), not a replacement
normed space. All other feature coordinates vanish identically.
-/
open MeasureTheory Set
open scoped BigOperators NNReal
namespace PaperFormalization.Manuscript

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

abbrev VarianceCosinePoint := EuclideanSpace Real (Fin 1)
abbrev VarianceCosineHilbert := lp (fun _ : Nat => Real) 2

noncomputable def varianceCosineScalar : VarianceCosinePoint →L[Real] Real :=
  PiLp.proj 2 (fun _ : Fin 1 => Real) 0

noncomputable def varianceCosinePoint (x : Real) : VarianceCosinePoint :=
  WithLp.toLp 2 (fun _ => x)

theorem varianceCosinePoint_scalar (x : VarianceCosinePoint) :
    varianceCosinePoint (varianceCosineScalar x) = x := by
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

theorem varianceCosineScalar_point (x : Real) :
    varianceCosineScalar (varianceCosinePoint x) = x := rfl

theorem varianceCosinePoint_norm (x : Real) :
    norm (varianceCosinePoint x) = abs x := by
  rw [PiLp.norm_eq_of_L2]
  simp [varianceCosinePoint, Real.sqrt_sq_eq_abs]

theorem varianceCosineScalar_abs (x : VarianceCosinePoint) :
    abs (varianceCosineScalar x) = norm x := by
  rw [<- varianceCosinePoint_norm, varianceCosinePoint_scalar]

theorem varianceCosineScalar_norm_le : norm varianceCosineScalar <= 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simp only [Real.norm_eq_abs, varianceCosineScalar_abs, one_mul, le_refl]

noncomputable def varianceCosinePointCLM : Real →L[Real] VarianceCosinePoint :=
  LinearMap.mkContinuous
    { toFun := varianceCosinePoint
      map_add' := by intro x y; ext i; rfl
      map_smul' := by intro c x; ext i; rfl }
    1 (fun x => by simp [varianceCosinePoint_norm, Real.norm_eq_abs])

theorem varianceCosinePointCLM_apply (x : Real) :
    varianceCosinePointCLM x = varianceCosinePoint x := rfl

noncomputable def varianceCosineFeature : Nat -> VarianceCosinePoint -> Real
  | 0, x => varianceCosineScalar x
  | 1, x => (varianceCosineScalar x)^2
  | _+2, _ => 0

theorem varianceCosineFeature_contDiff (n : Nat) :
    ContDiff Real 3 (varianceCosineFeature n) := by
  rcases n with _ | _ | n
  · exact varianceCosineScalar.contDiff
  · exact varianceCosineScalar.contDiff.pow 2
  · exact contDiff_const

theorem varianceCosineFeature_fderiv (n : Nat) (x : VarianceCosinePoint) :
    fderiv Real (varianceCosineFeature n) x =
      if n = 0 then varianceCosineScalar else
      if n = 1 then (2*varianceCosineScalar x) • varianceCosineScalar else 0 := by
  rcases n with _ | _ | n
  · change fderiv Real (fun y => varianceCosineScalar y) x = varianceCosineScalar
    exact varianceCosineScalar.hasFDerivAt.fderiv
  · change fderiv Real (fun y => (varianceCosineScalar y)^2) x =
      (2*varianceCosineScalar x) • varianceCosineScalar
    have h := varianceCosineScalar.hasFDerivAt.pow 2 (x := x)
    simpa [pow_one, nsmul_eq_mul] using h.fderiv
  · change fderiv Real (fun _ : VarianceCosinePoint => (0 : Real)) x = 0
    simp

theorem varianceCosineFeature_second (n : Nat) (x : VarianceCosinePoint) :
    fderiv Real (fderiv Real (varianceCosineFeature n)) x =
      if n = 1 then 2 • varianceCosineScalar.smulRight varianceCosineScalar else 0 := by
  have heq := funext (varianceCosineFeature_fderiv n)
  rw [heq]
  rcases n with _ | _ | n
  · simp
  · change fderiv Real (fun y => (2*varianceCosineScalar y) • varianceCosineScalar) x =
      2 • varianceCosineScalar.smulRight varianceCosineScalar
    have h := (varianceCosineScalar.hasFDerivAt.const_mul 2).smul_const varianceCosineScalar (x := x)
    rw [h.fderiv]
    ext y z
    simp [mul_assoc]
  · simp

theorem varianceCosineFeature_third (n : Nat) (x : VarianceCosinePoint) :
    fderiv Real (fderiv Real (fderiv Real (varianceCosineFeature n))) x = 0 := by
  rw [funext (varianceCosineFeature_second n)]
  simp

theorem varianceCosineFeature_third_exists (n : Nat) (x : VarianceCosinePoint) :
    DifferentiableAt Real (fderiv Real (fderiv Real (varianceCosineFeature n))) x := by
  rw [funext (varianceCosineFeature_second n)]
  exact differentiableAt_const _

/-- Exactly the manuscript's C_phi=1, c_gr=1, kappa_gr=0. -/
theorem varianceCosineFeature_growth (n : Nat) (x : VarianceCosinePoint)
    (k : Nat) (hk : k <= 2) :
    norm (iteratedFDeriv Real k (varianceCosineFeature n) x) <=
      featureGrowth 1 1 0 n * (1 + norm x ^ (n+1-k)) := by
  have he : 1 <= Real.exp 1 := Real.one_le_exp (by norm_num)
  have hx : 0 <= norm x := norm_nonneg x
  have hl := varianceCosineScalar_norm_le
  have hbil : norm (varianceCosineScalar.smulRight varianceCosineScalar) <= 1 := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    nlinarith [norm_nonneg varianceCosineScalar]
  rcases n with _ | _ | n
  · interval_cases k
    · norm_num [norm_iteratedFDeriv_zero, varianceCosineFeature, Real.norm_eq_abs,
        varianceCosineScalar_abs, featureGrowth]
      nlinarith
    · rw [norm_iteratedFDeriv_one, varianceCosineFeature_fderiv]
      norm_num [featureGrowth]
      nlinarith
    · rw [<- norm_second_fderiv_eq_iterated, varianceCosineFeature_second]
      simp only [if_neg (by norm_num : (0 : Nat) ≠ 1), ContinuousLinearMap.opNorm_zero]
      unfold featureGrowth
      positivity
  · interval_cases k
    · simp only [norm_iteratedFDeriv_zero, varianceCosineFeature, Real.norm_eq_abs, abs_pow,
        varianceCosineScalar_abs]
      norm_num [featureGrowth]
      nlinarith [sq_nonneg (norm x)]
    · rw [norm_iteratedFDeriv_one, varianceCosineFeature_fderiv]
      norm_num [featureGrowth, norm_smul, Real.norm_eq_abs, abs_mul, varianceCosineScalar_abs]
      nlinarith
    · rw [<- norm_second_fderiv_eq_iterated, varianceCosineFeature_second]
      norm_num only [ite_true]
      have hn : norm (2 • varianceCosineScalar.smulRight varianceCosineScalar) ≤
          2 * norm (varianceCosineScalar.smulRight varianceCosineScalar) := norm_nsmul_le
      have hbound : norm (2 • varianceCosineScalar.smulRight varianceCosineScalar) ≤ 2 := by
        nlinarith
      refine hbound.trans ?_
      norm_num [featureGrowth]
      nlinarith
  · have hz : varianceCosineFeature (n+2) = fun _ => 0 := rfl
    rw [hz]
    interval_cases k
    · simp only [norm_iteratedFDeriv_zero, norm_zero]
      unfold featureGrowth
      positivity
    · simp only [norm_iteratedFDeriv_one, fderiv_const_apply, ContinuousLinearMap.opNorm_zero]
      unfold featureGrowth
      positivity
    · simp [featureGrowth]
      positivity

theorem varianceCosineFeature_growth_three (n : Nat) (x : VarianceCosinePoint) :
    norm (iteratedFDeriv Real 3 (varianceCosineFeature n) x) <=
      featureGrowth 1 1 0 n * (1+norm x^(n+1-3)) := by
  rw [<- norm_third_fderiv_eq_iterated, varianceCosineFeature_third, ContinuousLinearMap.opNorm_zero]
  unfold featureGrowth
  positivity

noncomputable def varianceCosineWeight : Nat -> Real := sourceFeatureScale 1 2

noncomputable def varianceCosineDecode (n : Nat) : VarianceCosineHilbert →L[Real] Real :=
  weightedCoordinateProjection varianceCosineWeight n

noncomputable def varianceCosineEncodedFeature : VarianceCosinePoint -> VarianceCosineHilbert :=
  sourceWeightedFeatureMap 1 2 varianceCosineFeature

theorem varianceCosineEncodedFeature_coordinate (x : VarianceCosinePoint) (n : Nat) :
    varianceCosineEncodedFeature x n = varianceCosineWeight n * varianceCosineFeature n x := by
  exact sourceWeightedFeatureMap_apply 1 1 1 2 0 varianceCosineFeature
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun n x => by simpa only [norm_iteratedFDeriv_zero, Nat.sub_zero] using
      varianceCosineFeature_growth n x 0 (by omega)) x n

theorem varianceCosineDecode_feature (x : VarianceCosinePoint) (n : Nat) :
    varianceCosineDecode n (varianceCosineEncodedFeature x) = varianceCosineFeature n x := by
  rw [varianceCosineDecode, weightedCoordinateProjection_apply, varianceCosineEncodedFeature_coordinate]
  have hw := (sourceFeatureScale_pos 1 2 n).ne'
  simp only [smul_eq_mul]
  change (sourceFeatureScale 1 2 n)⁻¹ *
    (sourceFeatureScale 1 2 n * varianceCosineFeature n x) = _
  simp [hw]

/-- Finite support in the actual infinite-dimensional weighted Hilbert space. -/
theorem varianceCosineEncodedFeature_two_terms (x : VarianceCosinePoint) :
    varianceCosineEncodedFeature x =
      weightedCoordinateEmbedding varianceCosineWeight 0 (varianceCosineScalar x) +
      weightedCoordinateEmbedding varianceCosineWeight 1 ((varianceCosineScalar x)^2) := by
  ext n
  rw [varianceCosineEncodedFeature_coordinate]
  rcases n with _ | _ | n <;>
    simp [varianceCosineFeature, weightedCoordinateEmbedding, Pi.single_apply]
end PaperFormalization.Manuscript
