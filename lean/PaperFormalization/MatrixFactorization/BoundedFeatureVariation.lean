import PaperFormalization.MatrixFactorization.CapPrimalFirstVariation
import PaperFormalization.MatrixFactorization.MeasurableFeatureVelocity

/-! # MF24: actual finite-Hermite means along bounded Borel EXP tests

Verification status and conditional scope: see `MF24_VALIDATION.md`. The perturbation field is not assumed continuous in the
weight. Pointwise EXP derivatives and the previously proved finite-Hermite
bounds supply a uniform integrable bound before original-measure differentiation.
The Gaussian input is unrestricted; there is no input cutoff or new moment assumption.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def boundedMeanFeature {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu : Measure (UnitSphere d)) (V : BoundedTangentTest d) (t : Real) (z : Weight d) : Weight h :=
  meanFeature (finiteHermiteActivation O a) (V.push mu t) z

noncomputable def boundedMeanFeatureSlope {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu : Measure (UnitSphere d)) (V : BoundedTangentTest d) (t : Real) (z : Weight d) : Weight h :=
  ∫ w, sphericalFeatureFirst 0 O a w (V.field w) (V.tangent w) z t ∂mu

theorem boundedFeatureSlope_stronglyMeasurable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (V : BoundedTangentTest d) (t : Real) :
    StronglyMeasurable (fun zw : Weight d × UnitSphere d =>
      sphericalFeatureFirst 0 O a zw.2 (V.field zw.2) (V.tangent zw.2) zw.1 t) := by
  have hv : Measurable (fun zw : Weight d × UnitSphere d =>
      sphereExpVelocity zw.2 (V.field zw.2) t) :=
    (V.expVelocity_measurable t).comp measurable_snd
  have hp : Measurable (fun zw : Weight d × UnitSphere d => (V.expMap t zw.2).val) :=
    continuous_subtype_val.measurable.comp ((V.expMap_measurable t).comp measurable_snd)
  have hj := (finiteHermiteActivationJet_continuous 1 O a).measurable.comp
    (hp.inner (𝕜 := Real) measurable_fst)
  exact ((hv.inner (𝕜 := Real) measurable_fst).smul hj).stronglyMeasurable

theorem boundedMeanFeatureSlope_stronglyMeasurable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu]
    (V : BoundedTangentTest d) (t : Real) :
    StronglyMeasurable (boundedMeanFeatureSlope O a mu V t) :=
  (boundedFeatureSlope_stronglyMeasurable O a V t).integral_prod_right

/-- Actual original-law Bochner integrability, at every signed time. -/
theorem boundedFeatureSlope_integrable {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu] (V : BoundedTangentTest d)
    (t : Real) (z : Weight d) :
    Integrable (fun w => sphericalFeatureFirst 0 O a w (V.field w) (V.tangent w) z t) mu := by
  apply ((V.norm_integrable mu).mul_const (featureFirstEnvelope 0 O a z)).mono'
    (((boundedFeatureSlope_stronglyMeasurable O a V t).comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  exact Eventually.of_forall (fun w => sphericalFeatureFirst_bound 0 O a w (V.field w) (V.tangent w) z t)

theorem boundedMeanFeature_stronglyMeasurable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    (V : BoundedTangentTest d) (t : Real) : StronglyMeasurable (boundedMeanFeature O a mu V t) := by
  letI := V.push_probability mu t
  exact meanFeature_stronglyMeasurable _ (finiteHermiteActivation_continuous O a) (V.push mu t)

theorem boundedMeanFeature_norm_le {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] (V : BoundedTangentTest d)
    (t : Real) (z : Weight d) : norm (boundedMeanFeature O a mu V t z) ≤ fittingFeatureEnvelope O a z := by
  letI := V.push_probability mu t
  exact (finiteHermite_mean_growth O a (V.push mu t) z).trans (fittingFeatureEnvelope_bounds O a z).2.2.2

theorem boundedMeanFeatureSlope_norm_le {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] (V : BoundedTangentTest d)
    (t : Real) (z : Weight d) :
    norm (boundedMeanFeatureSlope O a mu V t z) ≤ V.bound*fittingFeatureEnvelope O a z := by
  have hi := boundedFeatureSlope_integrable O a mu V t z
  calc
    _ ≤ ∫ w, norm (sphericalFeatureFirst 0 O a w (V.field w) (V.tangent w) z t) ∂mu :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _ : UnitSphere d, V.bound*fittingFeatureEnvelope O a z ∂mu := by
      apply integral_mono hi.norm (integrable_const _)
      intro w
      exact (sphericalFeatureFirst_bound 0 O a w (V.field w) (V.tangent w) z t).trans
        (mul_le_mul (V.norm_le w) (fittingFeatureEnvelope_bounds O a z).2.1
          (featureFirstEnvelope_nonneg 0 O a z) V.bound_nonneg)
    _ = _ := by simp

/-- Differentiation is under the original mu, not an unproved regularity
assumption on the time-dependent pushed measure. -/
theorem boundedMeanFeature_hasDerivAt {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] (V : BoundedTangentTest d)
    (z : Weight d) (t : Real) :
    HasDerivAt (fun s => boundedMeanFeature O a mu V s z) (boundedMeanFeatureSlope O a mu V t z) t := by
  let F := fun s w => finiteHermiteActivation O a (inner Real (V.expMap s w).val z)
  let F' := fun s w => sphericalFeatureFirst 0 O a w (V.field w) (V.tangent w) z s
  have hm (s : Real) : Measurable (F s) := (finiteHermiteActivation_continuous O a).measurable.comp
    ((continuous_subtype_val.measurable.comp (V.expMap_measurable s)).inner (𝕜 := Real) measurable_const)
  have hi : Integrable (F t) mu := by
    apply Integrable.of_bound (hm t).aestronglyMeasurable (featureEnvelope 0 O a z)
    filter_upwards with w
    simpa only [finiteHermiteActivationJet_zero] using
      finiteHermiteActivationJet_sphere_bound 0 O a (V.expMap t w) z
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun _ => V.bound*featureFirstEnvelope 0 O a z)
    (s := Set.univ) (x₀ := t) (by simp)
    (Eventually.of_forall (fun s => (hm s).aestronglyMeasurable)) hi
    (((boundedFeatureSlope_stronglyMeasurable O a V t).comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (Eventually.of_forall (fun w s _ =>
      (sphericalFeatureFirst_bound 0 O a w (V.field w) (V.tangent w) z s).trans
        (mul_le_mul_of_nonneg_right (V.norm_le w) (featureFirstEnvelope_nonneg 0 O a z))))
    (integrable_const _)
    (Eventually.of_forall (fun w s _ => by
      apply (sphericalFeatureJet_hasDerivAt 0 O a w (V.field w) (V.tangent w) z s).congr_of_eventuallyEq
      filter_upwards with u
      exact (sphericalFeatureJet_zero_order O a w (V.field w) (V.tangent w) z u).symm))
  apply hd.2.congr_of_eventuallyEq
  filter_upwards with s
  exact integral_map (V.expMap_measurable s).aemeasurable
    (((finiteHermiteActivation_continuous O a).comp
      (continuous_subtype_val.inner (𝕜 := Real) continuous_const)).aestronglyMeasurable)

@[simp] theorem boundedMeanFeature_zero {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu : Measure (UnitSphere d)) (V : BoundedTangentTest d) (z : Weight d) :
    boundedMeanFeature O a mu V 0 z = meanFeature (finiteHermiteActivation O a) mu z := by
  simp only [boundedMeanFeature, V.push_zero]

@[simp] theorem boundedMeanFeatureSlope_zero {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu : Measure (UnitSphere d)) (V : BoundedTangentTest d) (z : Weight d) :
    boundedMeanFeatureSlope O a mu V 0 z = meanFeatureVelocity O a mu V.field z := by
  simp only [boundedMeanFeatureSlope, meanFeatureVelocity, featureVelocity, sphericalFeatureFirst_at_zero]

end PaperFormalization.MatrixFactorization
