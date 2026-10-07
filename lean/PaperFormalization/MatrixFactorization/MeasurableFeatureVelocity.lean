import PaperFormalization.MatrixFactorization.SphericalFittingGradientVariation

/-! # MF15: measurable velocities in the literal Gaussian first variation

The actual negative gradient is not continuous across
an equatorial assigned-pole tie. These generic integral lemmas require only
measurability, integrable speed and almost-everywhere tangency; the subsequent
characteristic application derives these from its existing cap fields.
No new regularity condition is imposed on the original particle model.
-/
open MeasureTheory ProbabilityTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def featureVelocity {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (v : UnitSphere d → Weight d) (w : UnitSphere d) (z : Weight d) : Weight h :=
  inner Real (v w) z • finiteHermiteActivationJet 1 O a (inner Real w.val z)

noncomputable def meanFeatureVelocity {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu : Measure (UnitSphere d)) (v : UnitSphere d → Weight d) (z : Weight d) : Weight h :=
  ∫ w, featureVelocity O a v w z ∂mu

theorem featureVelocity_stronglyMeasurable {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (v : UnitSphere d → Weight d) (hv : Measurable v) :
    StronglyMeasurable (fun zw : Weight d × UnitSphere d => featureVelocity O a v zw.2 zw.1) := by
  have hlin := (hv.comp measurable_snd).inner (𝕜 := Real) measurable_fst
  have hj : Continuous (fun zw : Weight d × UnitSphere d =>
      finiteHermiteActivationJet 1 O a (inner Real zw.2.val zw.1)) := by
    exact (finiteHermiteActivationJet_continuous 1 O a).comp (by fun_prop)
  exact (hlin.smul hj.measurable).stronglyMeasurable

theorem featureVelocity_norm_le {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (v : UnitSphere d → Weight d) (w : UnitSphere d) (z : Weight d) :
    norm (featureVelocity O a v w z) ≤ fittingFeatureEnvelope O a z * norm (v w) := by
  have hj := finiteHermiteActivationJet_sphere_bound 1 O a w z
  have he := (fittingFeatureEnvelope_bounds O a z).2.1
  rw [featureVelocity,norm_smul,Real.norm_eq_abs]
  calc
    _ ≤ (norm (v w)*norm z)*featureEnvelope 1 O a z :=
      mul_le_mul (abs_real_inner_le_norm _ _) hj (norm_nonneg _) (by positivity)
    _ = featureFirstEnvelope 0 O a z * norm (v w) := by
      unfold featureFirstEnvelope
      norm_num
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right he (norm_nonneg _)

theorem featureVelocity_integrable {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu : Measure (UnitSphere d)) (v : UnitSphere d → Weight d)
    (hv : Measurable v) (hi : Integrable (fun w => norm (v w)) mu) (z : Weight d) :
    Integrable (fun w => featureVelocity O a v w z) mu := by
  apply (hi.const_mul (fittingFeatureEnvelope O a z)).mono'
    (((featureVelocity_stronglyMeasurable O a v hv).comp_measurable
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  exact Eventually.of_forall (fun w => featureVelocity_norm_le O a v w z)

theorem meanFeatureVelocity_stronglyMeasurable {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu]
    (v : UnitSphere d → Weight d) (hv : Measurable v) :
    StronglyMeasurable (meanFeatureVelocity O a mu v) :=
  (featureVelocity_stronglyMeasurable O a v hv).integral_prod_right

theorem meanFeatureVelocity_norm_le {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    (v : UnitSphere d → Weight d) (hv : Measurable v)
    (M : Real) (hM : ∀ᵐ w ∂mu, norm (v w) ≤ M) (z : Weight d) :
    norm (meanFeatureVelocity O a mu v z) ≤ fittingFeatureEnvelope O a z * M := by
  have hi : Integrable (fun w => norm (v w)) mu :=
    Integrable.of_bound hv.norm.aestronglyMeasurable M (by simpa only [norm_norm] using hM)
  have hfi := featureVelocity_integrable O a mu v hv hi z
  calc
    _ ≤ ∫ w, norm (featureVelocity O a v w z) ∂mu := norm_integral_le_integral_norm _
    _ ≤ ∫ _ : UnitSphere d, fittingFeatureEnvelope O a z * M ∂mu := by
      apply integral_mono_ae hfi.norm (integrable_const _)
      filter_upwards [hM] with w hw
      exact (featureVelocity_norm_le O a v w z).trans
        (mul_le_mul_of_nonneg_left hw (fittingFeatureEnvelope_nonneg O a z))
    _ = _ := by simp

/-- Actual Fubini for a measurable L1 velocity, without extending it as a
continuous field on the whole sphere. Both pairings are integrable outputs. -/
theorem fitting_measurable_velocity_pairing {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu1 mu2 teacher1 teacher2 nu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu1] [IsProbabilityMeasure mu2]
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] [IsProbabilityMeasure nu]
    (i : Fin 2) (v : UnitSphere d → Weight d) (hv : Measurable v)
    (hi : Integrable (fun w => norm (v w)) nu)
    (htan : ∀ᵐ w ∂nu, inner Real w.val (v w) = 0) :
    Integrable (fun w => inner Real (sphericalFittingGradient O a mu1 mu2 teacher1 teacher2 i w)
      (v w)) nu ∧
    Integrable (fun z => inner Real (fittingOutputGradient O a mu1 mu2 teacher1 teacher2 i z)
      (meanFeatureVelocity O a nu v z)) (stdGaussian (Weight d)) ∧
    (∫ w, inner Real (sphericalFittingGradient O a mu1 mu2 teacher1 teacher2 i w) (v w) ∂nu) =
      ∫ z, inner Real (fittingOutputGradient O a mu1 mu2 teacher1 teacher2 i z)
        (meanFeatureVelocity O a nu v z) ∂stdGaussian (Weight d) := by
  let K := fun (w : UnitSphere d) (z : Weight d) =>
    inner Real (fittingGradientIntegrand O a mu1 mu2 teacher1 teacher2 i w z) (v w)
  have hK : Integrable (fun wz : UnitSphere d × Weight d => K wz.1 wz.2)
      (nu.prod (stdGaussian (Weight d))) := by
    have hbound := hi.mul_prod ((fittingCurvatureConstant_integrable d O a).const_mul 4)
    have hm := (fittingGradientIntegrand_stronglyMeasurable O a mu1 mu2 teacher1 teacher2 i).inner
      (𝕜 := Real) (hv.stronglyMeasurable.comp_measurable measurable_fst)
    apply hbound.mono' hm.aestronglyMeasurable
    filter_upwards with wz
    dsimp [K]
    exact (abs_real_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_right
        (fittingGradientIntegrand_norm_le O a mu1 mu2 teacher1 teacher2 i wz.1 wz.2)
        (norm_nonneg _)).trans_eq (mul_comm _ _))
  have hleft (w : UnitSphere d) :
      inner Real (sphericalFittingGradient O a mu1 mu2 teacher1 teacher2 i w) (v w) =
        ∫ z, K w z ∂stdGaussian (Weight d) := by
    rw [real_inner_comm,sphericalFittingGradient,← integral_inner
      (fittingGradientIntegrand_integrable O a mu1 mu2 teacher1 teacher2 i w)]
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => real_inner_comm _ _)
  have hright (z : Weight d) : (∫ w, K w z ∂nu) =
      inner Real (fittingOutputGradient O a mu1 mu2 teacher1 teacher2 i z)
        (meanFeatureVelocity O a nu v z) := by
    rw [meanFeatureVelocity,← integral_inner (featureVelocity_integrable O a nu v hv hi z)]
    apply integral_congr_ae
    filter_upwards [htan] with w hw
    dsimp [K,featureVelocity]
    calc
      _ = inner Real (v w) (fittingGradientIntegrand O a mu1 mu2 teacher1 teacher2 i w z) :=
        real_inner_comm _ _
      _ = inner Real (fittingOutputGradient O a mu1 mu2 teacher1 teacher2 i z)
          (finiteHermiteActivationJet 1 O a (inner Real w.val z)) * inner Real (v w) z :=
        fittingGradientIntegrand_pairing O a mu1 mu2 teacher1 teacher2 i w (v w) z hw
      _ = _ := by rw [real_inner_smul_right]; ring
  refine ⟨?_,?_,?_⟩
  · exact hK.integral_prod_left.congr (Eventually.of_forall (fun w => (hleft w).symm))
  · exact hK.integral_prod_right.congr (Eventually.of_forall hright)
  · simp_rw [hleft]
    rw [integral_integral_swap hK]
    exact integral_congr_ae (Eventually.of_forall hright)

end PaperFormalization.MatrixFactorization
