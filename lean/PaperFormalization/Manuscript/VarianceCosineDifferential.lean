import PaperFormalization.Manuscript.VarianceCosineObjective
import PaperFormalization.Manuscript.LocalMomentHessian

/-! # Actual first, second, and third objective derivatives
M13u VERIFIED UNIT (full example application remains open). These are derivatives on the original infinite-dimensional
weighted Hilbert space, with the inverse coordinate weights retained.
-/
open MeasureTheory Set
namespace PaperFormalization.Manuscript

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

noncomputable def varianceCosineMeanDrift (beta x : Real) : Real :=
  beta*Real.pi*Real.sin (Real.pi*x)

noncomputable def varianceCosineKernel (a beta m : Real) : Real :=
  -a-beta*Real.pi^2*Real.cos (Real.pi*m)

noncomputable def varianceCosineD1 (a beta : Real) (z : VarianceCosineHilbert) :
    VarianceCosineHilbert →L[Real] Real :=
  (-a*varianceCosineDecode 0 z-varianceCosineMeanDrift beta (varianceCosineDecode 0 z)) •
    varianceCosineDecode 0 + (a/2) • varianceCosineDecode 1

noncomputable def varianceCosineD2 (a beta : Real) (z : VarianceCosineHilbert) :
    VarianceCosineHilbert →L[Real] (VarianceCosineHilbert →L[Real] Real) :=
  varianceCosineKernel a beta (varianceCosineDecode 0 z) •
    (varianceCosineDecode 0).smulRight (varianceCosineDecode 0)

noncomputable def varianceCosineD3 (beta : Real) (z : VarianceCosineHilbert) :
    VarianceCosineHilbert →L[Real]
      (VarianceCosineHilbert →L[Real] (VarianceCosineHilbert →L[Real] Real)) :=
  (beta*Real.pi^3*Real.sin (Real.pi*varianceCosineDecode 0 z)) •
    (varianceCosineDecode 0).smulRight
      ((varianceCosineDecode 0).smulRight (varianceCosineDecode 0))

theorem varianceCosine_hasFDerivAt (a beta : Real) (z : VarianceCosineHilbert) :
    HasFDerivAt (varianceCosineObjective a beta) (varianceCosineD1 a beta z) z := by
  have h := ((((varianceCosineDecode 1).hasFDerivAt (x := z)).sub
    (((varianceCosineDecode 0).hasFDerivAt (x := z)).pow 2)).const_mul (a/2)).add
      (((((varianceCosineDecode 0).hasFDerivAt (x := z)).const_mul Real.pi).cos).const_mul beta)
  convert h using 1 <;> try rfl
  all_goals ext <;> simp [varianceCosineD1, varianceCosineMeanDrift, pow_one] <;> ring

theorem varianceCosineD1_hasFDerivAt (a beta : Real) (z : VarianceCosineHilbert) :
    HasFDerivAt (varianceCosineD1 a beta) (varianceCosineD2 a beta z) z := by
  have hs := ((((varianceCosineDecode 0).hasFDerivAt (x := z)).const_mul Real.pi).sin).const_mul (beta*Real.pi)
  have hc := (((varianceCosineDecode 0).hasFDerivAt (x := z)).const_mul (-a)).sub hs
  have h := (hc.smul_const (varianceCosineDecode 0)).add_const ((a/2) • varianceCosineDecode 1)
  convert h using 1 <;> try rfl
  all_goals ext <;> simp [varianceCosineD1, varianceCosineMeanDrift,
    varianceCosineD2, varianceCosineKernel] <;> ring

theorem varianceCosineD2_hasFDerivAt (a beta : Real) (z : VarianceCosineHilbert) :
    HasFDerivAt (varianceCosineD2 a beta) (varianceCosineD3 beta z) z := by
  have hc := (((((varianceCosineDecode 0).hasFDerivAt (x := z)).const_mul Real.pi).cos).const_mul
    (beta*Real.pi^2)).const_sub (-a)
  have h := hc.smul_const ((varianceCosineDecode 0).smulRight (varianceCosineDecode 0))
  convert h using 1 <;> try rfl
  all_goals ext <;> simp [varianceCosineD3] <;> ring

theorem varianceCosine_fderiv (a beta : Real) :
    fderiv Real (varianceCosineObjective a beta) = varianceCosineD1 a beta := by
  funext z
  exact (varianceCosine_hasFDerivAt a beta z).fderiv

theorem varianceCosine_second_fderiv (a beta : Real) :
    fderiv Real (fderiv Real (varianceCosineObjective a beta)) = varianceCosineD2 a beta := by
  rw [varianceCosine_fderiv]
  funext z
  exact (varianceCosineD1_hasFDerivAt a beta z).fderiv

theorem varianceCosine_third_fderiv (a beta : Real) :
    fderiv Real (fderiv Real (fderiv Real (varianceCosineObjective a beta))) = varianceCosineD3 beta := by
  rw [varianceCosine_second_fderiv]
  funext z
  exact (varianceCosineD2_hasFDerivAt a beta z).fderiv

theorem varianceCosineDecode_norm_le (n : Nat) :
    norm (varianceCosineDecode n) <= (varianceCosineWeight n)⁻¹ := by
  have hw : 0 < varianceCosineWeight n := sourceFeatureScale_pos 1 2 n
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hw.le)
  intro z
  rw [varianceCosineDecode, weightedCoordinateProjection_apply, norm_smul]
  rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hw)]
  exact mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by norm_num) z n) (inv_nonneg.mpr hw.le)

noncomputable def varianceCosineThirdBound (beta : Real) : Real :=
  beta*Real.pi^3*((varianceCosineWeight 0)⁻¹)^3

theorem varianceCosine_third_bound (a beta : Real) (hb : 0 <= beta)
    (z : VarianceCosineHilbert) :
    norm (iteratedFDeriv Real 3 (varianceCosineObjective a beta) z) <= varianceCosineThirdBound beta := by
  rw [<- norm_third_fderiv_eq_iterated,varianceCosine_third_fderiv]
  have hp : 0 <= (varianceCosineWeight 0)⁻¹ := inv_nonneg.mpr (sourceFeatureScale_pos 1 2 0).le
  have hp1 := varianceCosineDecode_norm_le 0
  have hb2 := (ContinuousLinearMap.norm_smulRight_apply (varianceCosineDecode 0) (varianceCosineDecode 0)).le
  have hb3 := (ContinuousLinearMap.norm_smulRight_apply (varianceCosineDecode 0)
    ((varianceCosineDecode 0).smulRight (varianceCosineDecode 0))).le
  have hrank : norm ((varianceCosineDecode 0).smulRight
      ((varianceCosineDecode 0).smulRight (varianceCosineDecode 0))) <= ((varianceCosineWeight 0)⁻¹)^3 := by
    calc
      _ <= norm (varianceCosineDecode 0) * norm ((varianceCosineDecode 0).smulRight (varianceCosineDecode 0)) := hb3
      _ <= norm (varianceCosineDecode 0) * (norm (varianceCosineDecode 0)*norm (varianceCosineDecode 0)) :=
        mul_le_mul_of_nonneg_left hb2 (norm_nonneg _)
      _ <= _ := by nlinarith [pow_le_pow_left₀ (norm_nonneg _) hp1 3]
  have hcoeff : abs (beta*Real.pi^3*Real.sin (Real.pi*varianceCosineDecode 0 z)) <= beta*Real.pi^3 := by
    rw [abs_mul,abs_of_nonneg (mul_nonneg hb (pow_nonneg Real.pi_pos.le _))]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)
  unfold varianceCosineD3 varianceCosineThirdBound
  rw [norm_smul,Real.norm_eq_abs]
  exact mul_le_mul hcoeff hrank (norm_nonneg _) (by positivity)

theorem varianceCosineKernel_bound (a beta m : Real) (ha : 0 <= a) (hb : 0 <= beta) :
    abs (varianceCosineKernel a beta m) <= a+beta*Real.pi^2 := by
  calc
    _ <= abs (-a) + abs (beta*Real.pi^2*Real.cos (Real.pi*m)) := abs_sub _ _
    _ <= a + beta*Real.pi^2 := by
      rw [abs_neg,abs_of_nonneg ha,abs_mul,abs_of_nonneg (by positivity : 0 <= beta*Real.pi^2)]
      exact add_le_add le_rfl (mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _))

theorem varianceCosineMeanDrift_bound (beta x : Real) (hb : 0 <= beta) :
    abs (varianceCosineMeanDrift beta x) <= beta*Real.pi := by
  rw [varianceCosineMeanDrift,abs_mul,abs_of_nonneg (mul_nonneg hb Real.pi_pos.le)]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)

theorem varianceCosineMeanDrift_hasDerivAt (beta x : Real) :
    HasDerivAt (varianceCosineMeanDrift beta)
      (beta*Real.pi^2*Real.cos (Real.pi*x)) x := by
  convert (((hasDerivAt_id x).const_mul Real.pi).sin).const_mul (beta*Real.pi) using 1 <;> try rfl
  all_goals simp [varianceCosineMeanDrift] <;> ring

theorem varianceCosineMeanDrift_contDiff (beta : Real) :
    ContDiff Real 1 (varianceCosineMeanDrift beta) := by
  unfold varianceCosineMeanDrift
  fun_prop

theorem varianceCosineMeanDrift_lipschitz (beta : Real) (hb : 0 <= beta) :
    LipschitzWith ⟨beta*Real.pi^2,by positivity⟩ (varianceCosineMeanDrift beta) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x => (varianceCosineMeanDrift_hasDerivAt beta x).differentiableAt)
  intro x
  change abs (deriv (varianceCosineMeanDrift beta) x) <= beta*Real.pi^2
  rw [(varianceCosineMeanDrift_hasDerivAt beta x).deriv,abs_mul,
    abs_of_nonneg (by positivity : 0 <= beta*Real.pi^2)]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
end PaperFormalization.Manuscript
