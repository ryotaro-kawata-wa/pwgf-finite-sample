import PaperFormalization.MatrixFactorization.SphericalRadialPairing
import Mathlib.Algebra.QuadraticDiscriminant

/-! # Actual radial pairing controls the full gradient energy

Every required squared-norm and pairing integral is derived on the original
cap measures. Cauchy--Schwarz is obtained from the nonnegative integral of a
squared vector norm. The product estimate uses the original transport as the
exact radial energy, without assuming differentiability of a solution law.
-/
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- An integral Cauchy--Schwarz inequality obtained by a real quadratic discriminant. -/
theorem integral_inner_sq_le_norm_sq_integrals {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace Real E] (mu : Measure α) (f g : α → E)
    (hf : Integrable (fun x => norm (f x)^2) mu)
    (hg : Integrable (fun x => norm (g x)^2) mu)
    (hfg : Integrable (fun x => inner Real (f x) (g x)) mu) :
    (∫ x, inner Real (f x) (g x) ∂mu)^2 ≤
      (∫ x, norm (f x)^2 ∂mu)*(∫ x, norm (g x)^2 ∂mu) := by
  have hpoly (t : Real) :
      0 ≤ (∫ x, norm (g x)^2 ∂mu)*(t*t) +
        (-2*(∫ x, inner Real (f x) (g x) ∂mu))*t + (∫ x, norm (f x)^2 ∂mu) := by
    have he : (∫ x, norm (f x-t • g x)^2 ∂mu) =
        (∫ x, norm (g x)^2 ∂mu)*(t*t) +
        (-2*(∫ x, inner Real (f x) (g x) ∂mu))*t + (∫ x, norm (f x)^2 ∂mu) := by
      calc
        _ = ∫ x, (norm (f x)^2-2*t*inner Real (f x) (g x))+t^2*norm (g x)^2 ∂mu := by
          apply integral_congr_ae
          filter_upwards with x
          simp only [norm_sub_sq_real,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,real_inner_smul_right]
          ring
        _ = _ := by
          have hi : Integrable (fun x => norm (f x)^2-2*t*inner Real (f x) (g x)) mu :=
            hf.sub (hfg.const_mul (2*t))
          rw [integral_add hi (hg.const_mul (t^2)),
            integral_sub hf (hfg.const_mul (2*t)),integral_const_mul,integral_const_mul]
          ring
    rw [← he]
    exact integral_nonneg (fun x => sq_nonneg _)
  have hd := discrim_le_zero hpoly
  unfold discrim at hd
  nlinarith

/-- The actual full field has a finite second moment on every original cap marginal. -/
theorem sphericalObjectiveGradient_norm_sq_integrable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (r lambda p : Real)
    (mu : Fin 2 → Measure (UnitSphere d)) (hcap : ∀ i, TwoCapClass pole r (mu i))
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (i : Fin 2) :
    Integrable (fun w => norm (sphericalObjectiveGradient O a pole lambda p
      (mu 0) (mu 1) teacher1 teacher2 i w)^2) (mu i) := by
  letI : IsProbabilityMeasure (mu 0) := (hcap 0).probability
  letI : IsProbabilityMeasure (mu 1) := (hcap 1).probability
  letI : IsProbabilityMeasure (mu i) := (hcap i).probability
  let C := fittingCurvatureConstant d O a
  let K := lambda*(productAntipodalTransportSq pole (mu 0) (mu 1))^(p/2-1)
  apply Integrable.of_bound
    (((sphericalObjectiveGradient_measurable O a pole lambda p (mu 0) (mu 1)
      teacher1 teacher2 i).norm.pow_const 2).aestronglyMeasurable) ((C+|K| * r)^2)
  filter_upwards [Measure.support_mem_ae (μ := mu i)] with w hw
  have hq : norm (assignedGradient pole w) ≤ r := by
    rw [assignedGradient_norm_on_support pole r (mu i) (hcap i) w hw]
    exact (assignedPole_distance_lt_cap pole r (hcap i).radius_lt ((hcap i).support_subset hw)).le
  have hb : norm (sphericalObjectiveGradient O a pole lambda p (mu 0) (mu 1) teacher1 teacher2 i w)
      ≤ C+|K| * r := by
    unfold sphericalObjectiveGradient metricGradient
    apply (norm_add_le _ _).trans
    rw [norm_smul,Real.norm_eq_abs]
    exact add_le_add (sphericalFittingGradient_norm_le O a (mu 0) (mu 1) teacher1 teacher2 i w)
      (mul_le_mul_of_nonneg_left hq (abs_nonneg _))
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) hb 2

theorem objective_radial_pairing_integrable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (r lambda p : Real)
    (mu : Fin 2 → Measure (UnitSphere d)) (hcap : ∀ i, TwoCapClass pole r (mu i))
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (i : Fin 2) :
    Integrable (fun w => inner Real
      (sphericalObjectiveGradient O a pole lambda p (mu 0) (mu 1) teacher1 teacher2 i w)
      (assignedGradient pole w)) (mu i) := by
  apply ((fitting_radial_pairing_integrable O a pole r mu hcap teacher1 teacher2 i).add
    (metric_radial_pairing_integrable pole r lambda p mu hcap i)).congr
  filter_upwards with w
  simp [sphericalObjectiveGradient,inner_add_left]

/-- The product Cauchy bound has the true spherical transport as its radial factor. -/
theorem objective_radial_pairing_sq_le_gradient_energy {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (r lambda p : Real)
    (mu : Fin 2 → Measure (UnitSphere d)) (hcap : ∀ i, TwoCapClass pole r (mu i))
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    (∑ i : Fin 2, ∫ w, inner Real
      (sphericalObjectiveGradient O a pole lambda p (mu 0) (mu 1) teacher1 teacher2 i w)
      (assignedGradient pole w) ∂mu i)^2 ≤
    (∑ i : Fin 2, ∫ w, norm (sphericalObjectiveGradient O a pole lambda p
      (mu 0) (mu 1) teacher1 teacher2 i w)^2 ∂mu i) *
      productAntipodalTransportSq pole (mu 0) (mu 1) := by
  have hi (i : Fin 2) := integral_inner_sq_le_norm_sq_integrals (mu i)
    (sphericalObjectiveGradient O a pole lambda p (mu 0) (mu 1) teacher1 teacher2 i)
    (assignedGradient pole)
    (sphericalObjectiveGradient_norm_sq_integrable O a pole r lambda p mu hcap teacher1 teacher2 i)
    (assignedGradient_norm_sq_integrable pole r (mu i) (hcap i))
    (objective_radial_pairing_integrable O a pole r lambda p mu hcap teacher1 teacher2 i)
  have hs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun (i : Fin 2) _ => integral_nonneg (fun w => sq_nonneg
      (norm (sphericalObjectiveGradient O a pole lambda p (mu 0) (mu 1) teacher1 teacher2 i w))))
    (fun (i : Fin 2) _ => integral_nonneg (fun w => sq_nonneg (norm (assignedGradient pole w))))
    (fun (i : Fin 2) _ => hi i)
  have he : (∑ i : Fin 2, ∫ w, norm (assignedGradient pole w)^2 ∂mu i) =
      productAntipodalTransportSq pole (mu 0) (mu 1) := by
    simp only [Fin.sum_univ_two,assignedGradient_energy pole r (mu 0) (hcap 0),
      assignedGradient_energy pole r (mu 1) (hcap 1),productAntipodalTransportSq]
  rw [he] at hs
  exact hs

end PaperFormalization.MatrixFactorization
