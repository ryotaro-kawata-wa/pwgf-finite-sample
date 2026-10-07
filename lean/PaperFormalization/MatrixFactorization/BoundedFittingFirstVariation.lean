import PaperFormalization.MatrixFactorization.BoundedFeatureVariation
import PaperFormalization.MatrixFactorization.SphereFirstVariationAlgebra

/-! # MF24: the original Gaussian fit on bounded Borel tangent directions

Verification status and conditional scope: see `MF24_VALIDATION.md`. The weight-measure derivative is supplied by the preceding
module; this module separately justifies the Gaussian derivative exchange.
The field is the existing literal finite-Hermite fitting field. No smoothness
of the perturbation in its weight label and no extra gradient-existence
hypothesis is imposed for the fitting term.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def partialFittingFunctional {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (other teacher1 teacher2 : Measure (UnitSphere d))
    (mu : Measure (UnitSphere d)) : Real := modelFitting O a mu other teacher1 teacher2

noncomputable def boundedFittingLoss {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu other teacher1 teacher2 : Measure (UnitSphere d)) (V : BoundedTangentTest d)
    (t : Real) (z : Weight d) : Real :=
  matrixPointLoss
    (outer (meanFeature (finiteHermiteActivation O a) teacher1 z)
      (meanFeature (finiteHermiteActivation O a) teacher2 z))
    (boundedMeanFeature O a mu V t z) (meanFeature (finiteHermiteActivation O a) other z)

noncomputable def boundedFittingSlope {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu other teacher1 teacher2 : Measure (UnitSphere d)) (V : BoundedTangentTest d)
    (t : Real) (z : Weight d) : Real :=
  inner Real (fittingOutputGradient O a (V.push mu t) other teacher1 teacher2 0 z)
    (boundedMeanFeatureSlope O a mu V t z)

/-- The two scalar output derivatives are the actual Frobenius loss derivatives. -/
theorem boundedFittingLoss_hasDerivAt {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu other teacher1 teacher2 : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    (V : BoundedTangentTest d) (z : Weight d) (t : Real) :
    HasDerivAt (fun s => boundedFittingLoss O a mu other teacher1 teacher2 V s z)
      (boundedFittingSlope O a mu other teacher1 teacher2 V t z) t := by
  have hd := matrixPointLoss_hasDerivAt
    (outer (meanFeature (finiteHermiteActivation O a) teacher1 z)
      (meanFeature (finiteHermiteActivation O a) teacher2 z))
    (boundedMeanFeature_hasDerivAt O a mu V z t)
    (hasDerivAt_const t (meanFeature (finiteHermiteActivation O a) other z))
  apply hd.congr_deriv
  rw [matrixPointFirst_output_gradients]
  simp [boundedFittingSlope, fittingOutputGradient, boundedMeanFeature]

/-- All Gaussian integrals below have independently established measurability. -/
theorem boundedFitting_measurable {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu other teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure other]
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2]
    (V : BoundedTangentTest d) (t : Real) :
    StronglyMeasurable (boundedFittingLoss O a mu other teacher1 teacher2 V t) ∧
    StronglyMeasurable (boundedFittingSlope O a mu other teacher1 teacher2 V t) := by
  letI := V.push_probability mu t
  have hm (nu : Measure (UnitSphere d)) [IsProbabilityMeasure nu] :=
    meanFeature_stronglyMeasurable (finiteHermiteActivation O a)
      (finiteHermiteActivation_continuous O a) nu
  have hR := (outer_stronglyMeasurable _ _ (boundedMeanFeature_stronglyMeasurable O a mu V t)
    (hm other)).sub (outer_stronglyMeasurable _ _ (hm teacher1) (hm teacher2))
  exact ⟨(hR.norm.pow 2).div stronglyMeasurable_const,
    (fittingOutputGradient_stronglyMeasurable O a (V.push mu t) other teacher1 teacher2 0).inner
      (𝕜 := Real) (boundedMeanFeatureSlope_stronglyMeasurable O a mu V t)⟩

theorem boundedFittingLoss_integrable {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu other teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure other]
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2]
    (V : BoundedTangentTest d) (t : Real) :
    Integrable (boundedFittingLoss O a mu other teacher1 teacher2 V t) (stdGaussian (Weight d)) := by
  letI := V.push_probability mu t
  unfold boundedFittingLoss matrixPointLoss boundedMeanFeature
  exact (modelFitting_integrable O a (V.push mu t) other teacher1 teacher2).div_const 2

/-- One Gaussian polynomial dominates the derivative at EVERY time. -/
theorem boundedFittingSlope_bound {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu other teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure other]
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2]
    (V : BoundedTangentTest d) (t : Real) (z : Weight d) :
    norm (boundedFittingSlope O a mu other teacher1 teacher2 V t z) ≤
      (2*V.bound)*(fittingFeatureEnvelope O a z)^4 := by
  letI := V.push_probability mu t
  have hB := fittingFeatureEnvelope_nonneg O a z
  calc
    _ ≤ norm (fittingOutputGradient O a (V.push mu t) other teacher1 teacher2 0 z)*
        norm (boundedMeanFeatureSlope O a mu V t z) := abs_real_inner_le_norm _ _
    _ ≤ (2*(fittingFeatureEnvelope O a z)^3)*(V.bound*fittingFeatureEnvelope O a z) :=
      mul_le_mul (fittingOutputGradient_norm_le O a (V.push mu t) other teacher1 teacher2 0 z)
        (boundedMeanFeatureSlope_norm_le O a mu V t z) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Actual Gaussian differentiation and actual sphere/Gaussian Fubini, not a
supplied derivative certificate for the source fitting functional. -/
theorem BoundedTangentTest.fitting_derivative {d h : Nat} (V : BoundedTangentTest d)
    (O : Finset Nat) (a : Nat → Weight h)
    (mu other teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure other]
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    HasDerivAt (fun t => partialFittingFunctional O a other teacher1 teacher2 (V.push mu t))
      (∫ w, inner Real (sphericalFittingGradient O a mu other teacher1 teacher2 0 w)
        (V.field w) ∂mu) 0 := by
  have hbound : Integrable (fun z : Weight d => (2*V.bound)*(fittingFeatureEnvelope O a z)^4)
      (stdGaussian (Weight d)) := by
    simpa only [one_mul] using (fittingFeatureEnvelope_gaussian_integrable (d := d) O a 1 4).const_mul (2*V.bound)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := boundedFittingLoss O a mu other teacher1 teacher2 V)
    (F' := boundedFittingSlope O a mu other teacher1 teacher2 V)
    (bound := fun z => (2*V.bound)*(fittingFeatureEnvelope O a z)^4)
    (s := Set.univ) (x₀ := 0) (by simp)
    (Eventually.of_forall (fun t => (boundedFitting_measurable O a mu other teacher1 teacher2 V t).1.aestronglyMeasurable))
    (boundedFittingLoss_integrable O a mu other teacher1 teacher2 V 0)
    (boundedFitting_measurable O a mu other teacher1 teacher2 V 0).2.aestronglyMeasurable
    (Eventually.of_forall (fun z t _ => boundedFittingSlope_bound O a mu other teacher1 teacher2 V t z))
    hbound (Eventually.of_forall (fun z t _ => boundedFittingLoss_hasDerivAt O a mu other teacher1 teacher2 V z t))
  have he : (fun t => partialFittingFunctional O a other teacher1 teacher2 (V.push mu t)) =ᶠ[𝓝 (0 : Real)]
      (fun t => ∫ z, boundedFittingLoss O a mu other teacher1 teacher2 V t z ∂stdGaussian (Weight d)) := by
    filter_upwards with t
    simp only [partialFittingFunctional, modelFitting, fittingEnergy,
      boundedFittingLoss, matrixPointLoss, boundedMeanFeature, integral_div]
    ring
  have hp := fitting_measurable_velocity_pairing O a mu other teacher1 teacher2 mu 0 V.field
    V.measurable_field (V.norm_integrable mu) (Eventually.of_forall V.tangent)
  apply (hd.2.congr_of_eventuallyEq he).congr_deriv
  simpa only [boundedFittingSlope, V.push_zero, boundedMeanFeatureSlope_zero] using hp.2.2.symm

/-- The fitting term supplies its first variation on all bounded Borel tests. -/
theorem partialFitting_firstVariation {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu other teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure other]
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    HasSphereFirstVariation mu (partialFittingFunctional O a other teacher1 teacher2)
      (sphericalFittingGradient O a mu other teacher1 teacher2 0) := by
  have hc := sphericalFittingGradient_continuous O a mu other teacher1 teacher2 0
  exact ⟨hc.measurable, Eventually.of_forall (sphericalFittingGradient_tangent O a mu other teacher1 teacher2 0),
    sphere_integrable mu _ (hc.norm.pow 2), fun V => V.fitting_derivative O a mu other teacher1 teacher2⟩

end PaperFormalization.MatrixFactorization
