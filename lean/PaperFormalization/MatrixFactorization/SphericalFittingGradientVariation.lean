import PaperFormalization.MatrixFactorization.SphericalFittingGradient
import PaperFormalization.MatrixFactorization.GeneralRetractionObjective

/-! # The actual spherical fitting gradient represents source variations

The field is the Gaussian integral of the literal finite-activation particle
variation. Product integrability and Fubini connect its tangent pairing to
the already verified derivative of the original product fitting objective.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Differentiating both outputs gives the two literal output gradients. -/
theorem matrixPointFirst_output_gradients {h : Nat} (x y u v dx dy : Weight h) :
    matrixPointFirst (outer u v) x y dx dy =
      inner Real (norm y^2 • x-inner Real v y • u) dx +
      inner Real (norm x^2 • y-inner Real u x • v) dy := by
  simp only [matrixPointFirst, outerFirst, inner_add_right, inner_sub_left,
    outer_inner, real_inner_smul_left, real_inner_self_eq_norm_sq]
  ring

/-- The particle variation is paired with the original continuous tangent field. -/
noncomputable def fittingGradientSourceIntegrand {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher1 teacher2 : Measure (UnitSphere d)) (i : Fin 2)
    (w : UnitSphere d) (z : Weight d) : Real :=
  inner Real (fittingGradientIntegrand O a (P.measure 0) (P.measure 1) teacher1 teacher2 i w z)
    (P.velocity i w)

theorem fittingGradientSourceIntegrand_integrable_prod {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (i : Fin 2) :
    Integrable (fun wz : UnitSphere d × Weight d =>
      fittingGradientSourceIntegrand O a P teacher1 teacher2 i wz.1 wz.2)
      ((P.measure i).prod (stdGaussian (Weight d))) := by
  letI : IsProbabilityMeasure (P.measure 0) := (P.cap 0).probability
  letI : IsProbabilityMeasure (P.measure 1) := (P.cap 1).probability
  letI : IsProbabilityMeasure (P.measure i) := (P.cap i).probability
  have hspeed := sphere_integrable (P.measure i) _ (P.continuous_velocity i).norm
  have hbound := hspeed.mul_prod ((fittingCurvatureConstant_integrable d O a).const_mul 4)
  have hm := (fittingGradientIntegrand_stronglyMeasurable O a (P.measure 0) (P.measure 1)
    teacher1 teacher2 i).inner (𝕜 := Real) ((P.continuous_velocity i).stronglyMeasurable.comp_measurable measurable_fst)
  apply hbound.mono' hm.aestronglyMeasurable
  apply Eventually.of_forall
  intro wz
  dsimp only [fittingGradientSourceIntegrand, Function.comp_apply]
  rw [Real.norm_eq_abs]
  calc
    _ ≤ norm (fittingGradientIntegrand O a (P.measure 0) (P.measure 1)
        teacher1 teacher2 i wz.1 wz.2)*norm (P.velocity i wz.1) := abs_real_inner_le_norm _ _
    _ ≤ (4*(fittingFeatureEnvelope O a wz.2)^4)*norm (P.velocity i wz.1) :=
      mul_le_mul_of_nonneg_right (fittingGradientIntegrand_norm_le O a
        (P.measure 0) (P.measure 1) teacher1 teacher2 i wz.1 wz.2) (norm_nonneg _)
    _ = _ := mul_comm _ _

/-- Tangency removes the normal component of the ambient Gaussian input. -/
theorem fittingGradientSourceIntegrand_eq {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher1 teacher2 : Measure (UnitSphere d)) (i : Fin 2)
    (w : UnitSphere d) (z : Weight d) :
    fittingGradientSourceIntegrand O a P teacher1 teacher2 i w z =
      inner Real (fittingOutputGradient O a (P.measure 0) (P.measure 1) teacher1 teacher2 i z)
        (sphericalFeatureFirst 0 O a w (P.velocity i w) (P.tangent i w) z 0) := by
  simp only [fittingGradientSourceIntegrand, fittingGradientIntegrand,
    real_inner_smul_left, sphericalFeatureFirst_at_zero, real_inner_smul_right]
  have hc : inner Real (transverseProjection w z) (P.velocity i w) =
      inner Real (P.velocity i w) (transverseProjection w z) := real_inner_comm _ _
  rw [hc, transverseProjection_pairing w (P.velocity i w) z (P.tangent i w)]
  ring

/-- Integrating the particle variation gives the previously proved mean-feature derivative. -/
theorem fittingGradientSourceIntegrand_sphere_integral {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher1 teacher2 : Measure (UnitSphere d)) (i : Fin 2) (z : Weight d) :
    (∫ w, fittingGradientSourceIntegrand O a P teacher1 teacher2 i w z ∂P.measure i) =
      inner Real (fittingOutputGradient O a (P.measure 0) (P.measure 1) teacher1 teacher2 i z)
        (variationFeatureFirst O a P i 0 z) := by
  letI : IsProbabilityMeasure (P.measure i) := (P.cap i).probability
  simp_rw [fittingGradientSourceIntegrand_eq]
  exact integral_inner
    (sphericalFeature_integrable 0 O a (P.measure i) (P.velocity i) (P.tangent i)
      (P.continuous_velocity i) z 0).2.1 _

/-- Both sides of the source pairing are genuinely integrable before Fubini is used. -/
theorem sphericalFittingGradient_source_integrable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (i : Fin 2) :
    Integrable (fun w => inner Real
      (sphericalFittingGradient O a (P.measure 0) (P.measure 1) teacher1 teacher2 i w)
      (P.velocity i w)) (P.measure i) ∧
    Integrable (fun z => inner Real
      (fittingOutputGradient O a (P.measure 0) (P.measure 1) teacher1 teacher2 i z)
      (variationFeatureFirst O a P i 0 z)) (stdGaussian (Weight d)) := by
  letI : IsProbabilityMeasure (P.measure 0) := (P.cap 0).probability
  letI : IsProbabilityMeasure (P.measure 1) := (P.cap 1).probability
  letI : IsProbabilityMeasure (P.measure i) := (P.cap i).probability
  have hi := fittingGradientSourceIntegrand_integrable_prod O a P teacher1 teacher2 i
  constructor
  · apply hi.integral_prod_left.congr
    apply Eventually.of_forall
    intro w
    dsimp only
    rw [real_inner_comm, sphericalFittingGradient, ← integral_inner
      (fittingGradientIntegrand_integrable O a (P.measure 0) (P.measure 1) teacher1 teacher2 i w)]
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => real_inner_comm _ _)
  · exact hi.integral_prod_right.congr (Eventually.of_forall
      (fittingGradientSourceIntegrand_sphere_integral O a P teacher1 teacher2 i))

/-- This is the required exchange between the original measure and Gaussian input. -/
theorem sphericalFittingGradient_source_pairing {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] (i : Fin 2) :
    (∫ w, inner Real
      (sphericalFittingGradient O a (P.measure 0) (P.measure 1) teacher1 teacher2 i w)
      (P.velocity i w) ∂P.measure i) =
    ∫ z, inner Real
      (fittingOutputGradient O a (P.measure 0) (P.measure 1) teacher1 teacher2 i z)
      (variationFeatureFirst O a P i 0 z) ∂stdGaussian (Weight d) := by
  letI : IsProbabilityMeasure (P.measure 0) := (P.cap 0).probability
  letI : IsProbabilityMeasure (P.measure 1) := (P.cap 1).probability
  letI : IsProbabilityMeasure (P.measure i) := (P.cap i).probability
  have he (w : UnitSphere d) : inner Real
      (sphericalFittingGradient O a (P.measure 0) (P.measure 1) teacher1 teacher2 i w)
      (P.velocity i w) =
        ∫ z, fittingGradientSourceIntegrand O a P teacher1 teacher2 i w z ∂stdGaussian (Weight d) := by
    rw [real_inner_comm, sphericalFittingGradient, ← integral_inner
      (fittingGradientIntegrand_integrable O a (P.measure 0) (P.measure 1) teacher1 teacher2 i w)]
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => real_inner_comm _ _)
  simp_rw [he]
  rw [integral_integral_swap (fittingGradientSourceIntegrand_integrable_prod O a P teacher1 teacher2 i)]
  exact integral_congr_ae (Eventually.of_forall
    (fittingGradientSourceIntegrand_sphere_integral O a P teacher1 teacher2 i))

theorem variationMatrixFirst_output_gradients {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher1 teacher2 : Measure (UnitSphere d)) (z : Weight d) :
    variationMatrixFirst O a P teacher1 teacher2 0 z =
      inner Real (fittingOutputGradient O a (P.measure 0) (P.measure 1) teacher1 teacher2 0 z)
        (variationFeatureFirst O a P 0 0 z) +
      inner Real (fittingOutputGradient O a (P.measure 0) (P.measure 1) teacher1 teacher2 1 z)
        (variationFeatureFirst O a P 1 0 z) := by
  simp only [variationMatrixFirst, variationFeature_initial, teacherOutput,
    matrixPointFirst_output_gradients, fittingOutputGradient]
  norm_num

/-- The Gaussian field represents the actual product fitting first variation. -/
theorem sphericalFittingGradient_first_variation {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    (∑ i : Fin 2, ∫ w, inner Real
      (sphericalFittingGradient O a (P.measure 0) (P.measure 1) teacher1 teacher2 i w)
      (P.velocity i w) ∂P.measure i) = variationFittingFirst O a P teacher1 teacher2 0 := by
  simp_rw [sphericalFittingGradient_source_pairing]
  rw [Fin.sum_univ_two, ← integral_add
    (sphericalFittingGradient_source_integrable O a P teacher1 teacher2 0).2
    (sphericalFittingGradient_source_integrable O a P teacher1 teacher2 1).2]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => (variationMatrixFirst_output_gradients O a P teacher1 teacher2 z).symm)

/-- Source differentiation of the literal EXP-pushed Gaussian fit. -/
theorem spherical_fitting_gradient_variation {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    HasDerivAt (variationFitting O a P teacher1 teacher2)
      (∑ i : Fin 2, ∫ w, inner Real
        (sphericalFittingGradient O a (P.measure 0) (P.measure 1) teacher1 teacher2 i w)
        (P.velocity i w) ∂P.measure i) 0 :=
  (spherical_fitting_source_variations O a P teacher1 teacher2 0).1.congr_deriv
    (sphericalFittingGradient_first_variation O a P teacher1 teacher2).symm

/-- The same field represents the actual normalized source perturbation. -/
theorem normalized_fitting_gradient_variation {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    HasDerivAt (variationRetractedFitting O a P teacher1 teacher2)
      (∑ i : Fin 2, ∫ w, inner Real
        (sphericalFittingGradient O a (P.measure 0) (P.measure 1) teacher1 teacher2 i w)
        (P.velocity i w) ∂P.measure i) 0 :=
  (variationRetractedFitting_initial_variations O a P teacher1 teacher2).1.congr_deriv
    (sphericalFittingGradient_first_variation O a P teacher1 teacher2).symm

end PaperFormalization.MatrixFactorization
