import PaperFormalization.MatrixFactorization.AssignedPoleContraction
import PaperFormalization.MatrixFactorization.SphericalMetricGradient
import PaperFormalization.MatrixFactorization.PoleContractionFeatureRemainder

/-! # Feature differentiation on actual assigned-pole pushforwards

The original assignment is merely measurable on the full sphere. Uniform
finite-Hermite envelopes justify differentiation under the original measure
without assuming global continuity of the assigned radial field.
-/
open MeasureTheory ProbabilityTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def contractionFeatureJet {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (pole w : UnitSphere d) (z : Weight d) (s : Real) : Weight h :=
  sphericalFeatureJet k O a (assignedPole pole w) (assignedPoleLog pole w)
    (assignedPoleLog_tangent pole w) z s

noncomputable def contractionFeatureFirst {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (pole w : UnitSphere d) (z : Weight d) (s : Real) : Weight h :=
  sphericalFeatureFirst k O a (assignedPole pole w) (assignedPoleLog pole w)
    (assignedPoleLog_tangent pole w) z s

noncomputable def contractionFeatureSecond {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (pole w : UnitSphere d) (z : Weight d) (s : Real) : Weight h :=
  sphericalFeatureSecond k O a (assignedPole pole w) (assignedPoleLog pole w)
    (assignedPoleLog_tangent pole w) z s

set_option maxHeartbeats 1000000 in
theorem contractionFeature_measurable {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (z : Weight d) (s : Real) :
    Measurable (fun w => contractionFeatureJet k O a pole w z s) ∧
    Measurable (fun w => contractionFeatureFirst k O a pole w z s) ∧
    Measurable (fun w => contractionFeatureSecond k O a pole w z s) := by
  have hx : Measurable (fun w => (assignedContraction pole s w).val) :=
    (measurable_subtype_coe : Measurable (fun w : UnitSphere d => w.val)).comp
      (f := fun w : UnitSphere d => assignedContraction pole s w)
      ((assignedContraction_measurable pole).comp (f := fun w : UnitSphere d => (s,w))
        (measurable_const.prodMk measurable_id))
  have hv : Measurable (fun w => assignedContractionVelocity pole s w) :=
    (assignedContractionVelocity_measurable pole).comp (f := fun w : UnitSphere d => (s,w))
      (measurable_const.prodMk measurable_id)
  have hJ (j : Nat) : Measurable (fun w => contractionFeatureJet j O a pole w z s) :=
    (finiteHermiteActivationJet_continuous j O a).measurable.comp (hx.inner (𝕜 := Real) measurable_const)
  refine ⟨hJ k, ?_, ?_⟩
  · exact (hv.inner (𝕜 := Real) measurable_const).smul (hJ (k+1))
  · exact (((hv.inner (𝕜 := Real) measurable_const).pow_const 2).smul (hJ (k+2))).sub
      ((((assignedPoleLog_measurable pole).norm.pow_const 2).mul
        (hx.inner (𝕜 := Real) measurable_const)).smul (hJ (k+1)))

theorem contractionFeature_bounds {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (pole w : UnitSphere d) (z : Weight d) (s : Real) :
    norm (contractionFeatureJet k O a pole w z s) ≤ featureEnvelope k O a z ∧
    norm (contractionFeatureFirst k O a pole w z s) ≤ Real.pi*featureFirstEnvelope k O a z ∧
    norm (contractionFeatureSecond k O a pole w z s) ≤ Real.pi^2*featureSecondEnvelope k O a z := by
  have hn : norm (assignedPoleLog pole w) ≤ Real.pi := by
    rw [assignedPoleLog_norm]
    exact (assignedPole_short pole w).le
  exact ⟨sphericalFeatureJet_bound k O a _ _ _ z s,
    (sphericalFeatureFirst_bound k O a _ _ _ z s).trans
      (mul_le_mul_of_nonneg_right hn (featureFirstEnvelope_nonneg k O a z)),
    (sphericalFeatureSecond_bound k O a _ _ _ z s).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hn 2)
        (featureSecondEnvelope_nonneg k O a z))⟩

theorem contractionFeature_integrable {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (z : Weight d) (s : Real) :
    Integrable (fun w => contractionFeatureJet k O a pole w z s) mu ∧
    Integrable (fun w => contractionFeatureFirst k O a pole w z s) mu ∧
    Integrable (fun w => contractionFeatureSecond k O a pole w z s) mu := by
  have hm := contractionFeature_measurable k O a pole z s
  have hb := contractionFeature_bounds k O a pole
  exact ⟨Integrable.of_bound hm.1.aestronglyMeasurable _ (Eventually.of_forall (fun w => (hb w z s).1)),
    Integrable.of_bound hm.2.1.aestronglyMeasurable _ (Eventually.of_forall (fun w => (hb w z s).2.1)),
    Integrable.of_bound hm.2.2.aestronglyMeasurable _ (Eventually.of_forall (fun w => (hb w z s).2.2))⟩

noncomputable def meanFeatureAlongContraction {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (mu : Measure (UnitSphere d))
    (z : Weight d) (s : Real) : Weight h :=
  meanFeature (finiteHermiteActivationJet k O a) (mu.map (assignedContraction pole s)) z

noncomputable def meanFeatureAlongContractionFirst {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (mu : Measure (UnitSphere d))
    (z : Weight d) (s : Real) : Weight h :=
  ∫ w, contractionFeatureFirst k O a pole w z s ∂mu

noncomputable def meanFeatureAlongContractionSecond {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (mu : Measure (UnitSphere d))
    (z : Weight d) (s : Real) : Weight h :=
  ∫ w, contractionFeatureSecond k O a pole w z s ∂mu

theorem meanFeatureAlongContraction_integral {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (mu : Measure (UnitSphere d))
    (z : Weight d) (s : Real) :
    meanFeatureAlongContraction k O a pole mu z s =
      ∫ w, contractionFeatureJet k O a pole w z s ∂mu := by
  exact integral_map
    (((assignedContraction_measurable pole).comp (measurable_const.prodMk measurable_id)).aemeasurable)
    (((finiteHermiteActivationJet_continuous k O a).comp
      (continuous_subtype_val.inner (𝕜 := Real) continuous_const)).aestronglyMeasurable)

/-- Both derivative exchanges are proved for every real contraction parameter. -/
theorem meanFeatureAlongContraction_variations {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (z : Weight d) (s : Real) :
    HasDerivAt (meanFeatureAlongContraction k O a pole mu z)
      (meanFeatureAlongContractionFirst k O a pole mu z s) s ∧
    HasDerivAt (meanFeatureAlongContractionFirst k O a pole mu z)
      (meanFeatureAlongContractionSecond k O a pole mu z s) s := by
  have hi := contractionFeature_integrable k O a pole mu z s
  have hm := contractionFeature_measurable k O a pole z
  have hb := contractionFeature_bounds k O a pole
  have hfirst := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t w => contractionFeatureJet k O a pole w z t)
    (F' := fun t w => contractionFeatureFirst k O a pole w z t)
    (bound := fun _ => Real.pi*featureFirstEnvelope k O a z) (s := Set.univ) (x₀ := s) univ_mem
    (Eventually.of_forall (fun t => (hm t).1.aestronglyMeasurable)) hi.1
    (hm s).2.1.aestronglyMeasurable
    (Eventually.of_forall (fun w t _ => (hb w z t).2.1)) (integrable_const _)
    (Eventually.of_forall (fun w t _ => sphericalFeatureJet_hasDerivAt k O a _ _ _ z t))
  have hsecond := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t w => contractionFeatureFirst k O a pole w z t)
    (F' := fun t w => contractionFeatureSecond k O a pole w z t)
    (bound := fun _ => Real.pi^2*featureSecondEnvelope k O a z) (s := Set.univ) (x₀ := s) univ_mem
    (Eventually.of_forall (fun t => (hm t).2.1.aestronglyMeasurable)) hi.2.1
    (hm s).2.2.aestronglyMeasurable
    (Eventually.of_forall (fun w t _ => (hb w z t).2.2)) (integrable_const _)
    (Eventually.of_forall (fun w t _ => sphericalFeatureFirst_hasDerivAt k O a _ _ _ z t))
  have he : meanFeatureAlongContraction k O a pole mu z =
      (fun t => ∫ w, contractionFeatureJet k O a pole w z t ∂mu) :=
    funext (meanFeatureAlongContraction_integral k O a pole mu z)
  exact ⟨he ▸ hfirst.2, hsecond.2⟩

@[simp] theorem meanFeatureAlongContraction_one {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (mu : Measure (UnitSphere d)) (z : Weight d) :
    meanFeatureAlongContraction k O a pole mu z 1 =
      meanFeature (finiteHermiteActivationJet k O a) mu z := by
  have he : assignedContraction pole 1 = id := funext (assignedContraction_one pole)
  simp only [meanFeatureAlongContraction, he, Measure.map_id]

/-- The source cap and half-mass hypotheses give the true zero feature at the
start of contraction. No pointwise cancellation of the original teacher is assumed. -/
theorem meanFeatureAlongContraction_zero {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (pole : UnitSphere d)
    (r : Real) (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu) (z : Weight d) :
    meanFeatureAlongContraction 0 O a pole mu z 0 = 0 := by
  have he : assignedContraction pole 0 = assignedPole pole := funext (assignedContraction_zero pole)
  have ha : finiteHermiteActivationJet 0 O a = finiteHermiteActivation O a :=
    funext (finiteHermiteActivationJet_zero O a)
  rw [meanFeatureAlongContraction, he, assignedPole_pushforward pole r mu hcap, ha]
  exact finiteHermite_mean_antipodal O a hO pole z

/-- The endpoint velocity is the original outward assigned-cost gradient. -/
theorem meanFeatureAlongContractionFirst_one {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (mu : Measure (UnitSphere d)) (z : Weight d) :
    meanFeatureAlongContractionFirst 0 O a pole mu z 1 =
      ∫ w, inner Real (assignedGradient pole w) z •
        finiteHermiteActivationJet 1 O a (inner Real w.val z) ∂mu := by
  apply integral_congr_ae
  apply Eventually.of_forall
  intro w
  change inner Real (assignedContractionVelocity pole 1 w) z •
    finiteHermiteActivationJet 1 O a (inner Real (assignedContraction pole 1 w).val z) = _
  rw [assignedContractionVelocity_one, assignedContraction_one]

end PaperFormalization.MatrixFactorization
