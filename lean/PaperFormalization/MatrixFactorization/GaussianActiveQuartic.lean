import PaperFormalization.MatrixFactorization.ActiveGaussianFeature
import PaperFormalization.MatrixFactorization.OuterProduct

/-! # MF38: a genuine Gaussian four-linear form for matrix fitting

We integrate a norm-integrable family of continuous multilinear maps. Thus
quartic coefficients are actual Gaussian integrals, and applying the integral
to active tensors is justified by Bochner integration, not stipulated.
-/
open MeasureTheory ProbabilityTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

noncomputable def outerQuartic (h : Nat) :
    ContinuousMultilinearMap Real (fun _ : Fin 4 => Weight h) Real where
  toFun v := inner Real (v 0) (v 2) * inner Real (v 1) (v 3)
  map_update_add' := by
    intro hDec v i x y
    have hDecEq : hDec = instDecidableEqFin 4 := Subsingleton.elim _ _
    subst hDec
    fin_cases i <;> simp [Function.update_apply, inner_add_left, inner_add_right, add_mul, mul_add]
  map_update_smul' := by
    intro hDec v i c x
    have hDecEq : hDec = instDecidableEqFin 4 := Subsingleton.elim _ _
    subst hDec
    fin_cases i <;> simp [Function.update_apply, real_inner_smul_left, real_inner_smul_right,
      smul_eq_mul, mul_assoc, mul_left_comm]
  cont := by fun_prop

@[simp] theorem outerQuartic_apply {h : Nat} (v : Fin 4 → Weight h) :
    outerQuartic h v = inner Real (v 0) (v 2) * inner Real (v 1) (v 3) := rfl

/-- This is precisely the Frobenius matrix pairing in the original fitting energy. -/
theorem outerQuartic_eq_matrix_pairing {h : Nat} (v : Fin 4 → Weight h) :
    outerQuartic h v = inner Real (outer (v 0) (v 1)) (outer (v 2) (v 3)) :=
  (outer_inner (v 0) (v 1) (v 2) (v 3)).symm

noncomputable def activeQuarticAtInput {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (z : Weight d) :
    ContinuousMultilinearMap Real (fun _ : Fin 4 => ActiveMomentSpace d O) Real :=
  (outerQuartic h).compContinuousLinearMap (fun _ => activeHermiteFeature O a z)

/-- Continuity holds in operator norm, before the Gaussian integral is formed. -/
theorem activeQuarticAtInput_continuous {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) :
    Continuous (activeQuarticAtInput (d := d) O a) := by
  exact (map_continuous ((outerQuartic h).compContinuousLinearMapLRight (E := fun _ : Fin 4 => ActiveMomentSpace d O))).comp
    (continuous_pi (fun _ => activeHermiteFeature_operator_continuous O a))

/-- A norm-integrable operator family can be integrated before any input is chosen. -/
theorem quarticFeature_operator_integrable {d h : Nat} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    (L : Weight d → E →L[Real] Weight h) (hc : Continuous L)
    (hi : Integrable (fun z => ‖L z‖ ^ 4) (stdGaussian (Weight d))) :
    Integrable (fun z => (outerQuartic h).compContinuousLinearMap (fun _ : Fin 4 => L z))
      (stdGaussian (Weight d)) := by
  have hc4 : Continuous (fun z => (outerQuartic h).compContinuousLinearMap (fun _ : Fin 4 => L z)) :=
    (map_continuous ((outerQuartic h).compContinuousLinearMapLRight (E := fun _ : Fin 4 => E))).comp
    (continuous_pi (fun _ => hc))
  apply (hi.const_mul ‖outerQuartic h‖).mono' hc4.aestronglyMeasurable
  filter_upwards [] with z
  simpa only [Function.comp_apply, ContinuousMultilinearMap.compContinuousLinearMapLRight_apply,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (outerQuartic h).norm_compContinuousLinearMap_le (fun _ : Fin 4 => L z)

noncomputable def quarticFeatureIntegral {d h : Nat} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] (L : Weight d → E →L[Real] Weight h) :
    ContinuousMultilinearMap Real (fun _ : Fin 4 => E) Real :=
  ∫ z : Weight d, (outerQuartic h).compContinuousLinearMap (fun _ : Fin 4 => L z)
    ∂stdGaussian (Weight d)

/-- Evaluation commutes with this genuinely integrable Bochner integral. -/
theorem quarticFeatureIntegral_apply {d h : Nat} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    (L : Weight d → E →L[Real] Weight h) (hc : Continuous L)
    (hi : Integrable (fun z => ‖L z‖ ^ 4) (stdGaussian (Weight d))) (X : Fin 4 → E) :
    quarticFeatureIntegral L X = ∫ z : Weight d,
      inner Real (L z (X 0)) (L z (X 2)) * inner Real (L z (X 1)) (L z (X 3))
      ∂stdGaussian (Weight d) :=
  ContinuousMultilinearMap.integral_apply (quarticFeature_operator_integrable L hc hi) X

/-- The scalar cross terms have true integrability, not merely a totalized integral. -/
theorem quarticFeature_scalar_integrable {d h : Nat} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    (L : Weight d → E →L[Real] Weight h) (hc : Continuous L)
    (hi : Integrable (fun z => ‖L z‖ ^ 4) (stdGaussian (Weight d))) (X : Fin 4 → E) :
    Integrable (fun z : Weight d =>
      inner Real (L z (X 0)) (L z (X 2)) * inner Real (L z (X 1)) (L z (X 3)))
      (stdGaussian (Weight d)) :=
  (ContinuousMultilinearMap.apply Real (fun _ : Fin 4 => E) Real X).integrable_comp
    (quarticFeature_operator_integrable L hc hi)

noncomputable def activeGaussianQuartic {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) :
    ContinuousMultilinearMap Real (fun _ : Fin 4 => ActiveMomentSpace d O) Real :=
  quarticFeatureIntegral (activeHermiteFeature O a)

/-- The coefficients are actual Gaussian integrals on the original source tensor norm. -/
theorem activeGaussianQuartic_apply {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (X : Fin 4 → ActiveMomentSpace d O) :
    activeGaussianQuartic O a X = ∫ z : Weight d,
      inner Real (activeHermiteFeature O a z (X 0)) (activeHermiteFeature O a z (X 2)) *
      inner Real (activeHermiteFeature O a z (X 1)) (activeHermiteFeature O a z (X 3))
      ∂stdGaussian (Weight d) := by
  unfold activeGaussianQuartic
  exact quarticFeatureIntegral_apply (d := d) (h := h) (E := ActiveMomentSpace d O)
    (activeHermiteFeature (d := d) O a)
    (activeHermiteFeature_operator_continuous (d := d) O a)
    (activeHermiteFeature_operator_power_integrable (d := d) O a 4) X

/-- Every matrix cross term in the polynomial is a true integrable scalar function. -/
theorem activeQuartic_scalar_integrable {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (X : Fin 4 → ActiveMomentSpace d O) :
    Integrable (fun z : Weight d =>
      inner Real (activeHermiteFeature O a z (X 0)) (activeHermiteFeature O a z (X 2)) *
      inner Real (activeHermiteFeature O a z (X 1)) (activeHermiteFeature O a z (X 3)))
      (stdGaussian (Weight d)) := by
  exact quarticFeature_scalar_integrable (d := d) (h := h) (E := ActiveMomentSpace d O)
    (activeHermiteFeature (d := d) O a)
    (activeHermiteFeature_operator_continuous (d := d) O a)
    (activeHermiteFeature_operator_power_integrable (d := d) O a 4) X

end PaperFormalization.MatrixFactorization
