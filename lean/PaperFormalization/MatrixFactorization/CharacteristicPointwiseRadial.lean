import PaperFormalization.MatrixFactorization.SphericalCharacteristicPersistence
import PaperFormalization.MatrixFactorization.AntisymmetricFittingGradientBounds

/-! # Actual supported-particle radial inequalities

The radius is the angular distance to the original assigned pole. Its cost
and continuity are derived from the existing assignment formula. The actual
characteristic ODE and source branch uniqueness give a pointwise half-cost
inequality, including both poles. The fitting coefficient remains the
explicit coarse Gaussian polynomial bound, not the manuscript's sharp L_fit.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def sphericalPoleRadius {d : Nat} (pole w : UnitSphere d) : Real :=
  sphericalDistance w (assignedPole pole w)

theorem sphericalPoleRadius_nonneg {d : Nat} (pole w : UnitSphere d) :
    0 ≤ sphericalPoleRadius pole w := sphericalDistance_nonneg _ _

/-- This identity uses the actual assigned angular half-cost. -/
theorem assignedCost_eq_half_poleRadius_sq {d : Nat} (pole w : UnitSphere d) :
    assignedCost pole w = (sphericalPoleRadius pole w)^2/2 := rfl

theorem sphericalPoleRadius_eq_sqrt_cost {d : Nat} (pole w : UnitSphere d) :
    sphericalPoleRadius pole w = Real.sqrt (2*assignedCost pole w) := by
  rw [assignedCost_eq_half_poleRadius_sq]
  have he : 2*(sphericalPoleRadius pole w^2/2) = sphericalPoleRadius pole w^2 := by ring
  rw [he,Real.sqrt_sq (sphericalPoleRadius_nonneg pole w)]

/-- The nearest-pole radius is continuous even at the assignment tie set. -/
theorem sphericalPoleRadius_continuous {d : Nat} (pole : UnitSphere d) :
    Continuous (sphericalPoleRadius pole) := by
  have he : sphericalPoleRadius pole = fun w => Real.sqrt (2*assignedCost pole w) :=
    funext (sphericalPoleRadius_eq_sqrt_cost pole)
  rw [he]
  exact Real.continuous_sqrt.comp (continuous_const.mul (assignedCost_continuous pole))

variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}

/-- The actual pointwise fitting force is bounded by the current true product distance. -/
theorem SphericalCharacteristicSolution.fittingGradient_norm_le_transport
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (t : Real) (ht : t ∈ Icc 0 T) (i : Fin 2) (w : UnitSphere d) :
    norm (sphericalFittingGradient O a (X.measure 0 t) (X.measure 1 t) teacher teacher i w) ≤
      fittingCurvatureConstant d O a*Real.sqrt (X.transport t) := by
  letI : IsProbabilityMeasure (X.measure 0 t) := (X.cap 0 t ht).probability
  have hb := spherical_characteristic_antibranch_invariant hO X hunique hinitial t ht
  simpa only [SphericalCharacteristicSolution.transport,hb] using
    antisymmetric_sphericalFittingGradient_product_bound O a hO pole (X.measure 0 t) teacher i w

/-- The original characteristic has this differential upper bound also at either pole.
No positive-time branch condition or pointwise radial estimate is assumed. -/
theorem SphericalCharacteristicSolution.assignedCost_deriv_le_antibranch
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (initial i).support)
    (t : Real) (ht : t ∈ Ioo 0 T) :
    deriv (fun s => assignedCost pole (X.characteristic i s w)) t ≤
      fittingCurvatureConstant d O a*Real.sqrt (X.transport t)*
        sphericalPoleRadius pole (X.characteristic i t w) -
      lambda*(X.transport t)^(p/2-1)*(sphericalPoleRadius pole (X.characteristic i t w))^2 := by
  have htc : t ∈ Icc (0 : Real) T := ⟨ht.1.le,ht.2.le⟩
  have hq : norm (assignedGradient pole (X.characteristic i t w)) =
      sphericalPoleRadius pole (X.characteristic i t w) :=
    assignedGradient_norm_on_support pole radius (X.measure i t) (X.cap i t htc)
      (X.characteristic i t w) (X.characteristic_mem_support i t htc w hw)
  have hfit := X.fittingGradient_norm_le_transport hO hunique hinitial t htc i
    (X.characteristic i t w)
  have hpair : -inner Real
      (sphericalFittingGradient O a (X.measure 0 t) (X.measure 1 t) teacher teacher i
        (X.characteristic i t w)) (assignedGradient pole (X.characteristic i t w)) ≤
      fittingCurvatureConstant d O a*Real.sqrt (X.transport t)*
        sphericalPoleRadius pole (X.characteristic i t w) := by
    calc
      _ ≤ |inner Real
          (sphericalFittingGradient O a (X.measure 0 t) (X.measure 1 t) teacher teacher i
            (X.characteristic i t w)) (assignedGradient pole (X.characteristic i t w))| :=
        neg_le_abs _
      _ ≤ _ := (abs_real_inner_le_norm _ _).trans (by
        rw [← hq]
        exact mul_le_mul_of_nonneg_right hfit (norm_nonneg _))
  rw [(X.assignedCost_hasDerivAt i w hw t ht).deriv]
  simp only [sphericalObjectiveGradient,inner_add_left,metricGradient,
    real_inner_smul_left,real_inner_self_eq_norm_sq,hq]
  change -(_ + lambda*(X.transport t)^(p/2-1)*
    (sphericalPoleRadius pole (X.characteristic i t w))^2) ≤ _
  linarith

end PaperFormalization.MatrixFactorization
