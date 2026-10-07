import PaperFormalization.MatrixFactorization.SphericalCharacteristicContinuity
import PaperFormalization.MatrixFactorization.MeasurableFeatureVelocity

/-! # MF15: actual characteristic mean-feature derivatives

The supported ODE and the cap-derived speed bound supply
one integrable bound for all interior times. The derivative is exchanged with
the ORIGINAL initial law before it is identified under the current pushed law.
Neither global continuity of the assigned gradient nor a new measure-valued
chain-rule premise is assumed.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}

noncomputable def SphericalCharacteristicSolution.velocity
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (i : Fin 2) (t : Real) (w : UnitSphere d) : Weight d :=
  -sphericalObjectiveGradient O a pole lambda p (X.measure 0 t) (X.measure 1 t)
    teacher teacher i w

noncomputable def SphericalCharacteristicSolution.feature
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (i : Fin 2) (t : Real) (z : Weight d) : Weight h :=
  meanFeature (finiteHermiteActivation O a) (X.measure i t) z

noncomputable def SphericalCharacteristicSolution.featureSlope
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (i : Fin 2) (t : Real) (z : Weight d) : Weight h :=
  meanFeatureVelocity O a (X.measure i t) (X.velocity i t) z

theorem SphericalCharacteristicSolution.velocity_measurable
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (i : Fin 2) (t : Real) (ht : t ∈ Icc 0 T) :
    Measurable (X.velocity i t) := by
  letI : IsProbabilityMeasure (X.measure 0 t) := (X.cap 0 t ht).probability
  letI : IsProbabilityMeasure (X.measure 1 t) := (X.cap 1 t ht).probability
  exact (sphericalObjectiveGradient_measurable O a pole lambda p
    (X.measure 0 t) (X.measure 1 t) teacher teacher i).neg

theorem SphericalCharacteristicSolution.velocity_tangent
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (i : Fin 2) (t : Real) (ht : t ∈ Icc 0 T)
    (w : UnitSphere d) : inner Real w.val (X.velocity i t w) = 0 := by
  letI : IsProbabilityMeasure (X.measure 0 t) := (X.cap 0 t ht).probability
  letI : IsProbabilityMeasure (X.measure 1 t) := (X.cap 1 t ht).probability
  simp only [SphericalCharacteristicSolution.velocity,inner_neg_right,
    sphericalObjectiveGradient_tangent,neg_zero]

theorem SphericalCharacteristicSolution.velocity_norm_bound
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p)
    (i : Fin 2) (t : Real) (ht : t ∈ Icc 0 T) :
    ∀ᵐ w ∂X.measure i t, norm (X.velocity i t w) ≤ characteristicSpeedBound d O a radius lambda p := by
  filter_upwards [Measure.support_mem_ae (μ := X.measure i t)] with w hw
  simpa only [SphericalCharacteristicSolution.velocity,norm_neg] using
    X.gradient_norm_le_speedBound hp i t ht w hw

theorem SphericalCharacteristicSolution.velocity_norm_integrable
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p)
    (i : Fin 2) (t : Real) (ht : t ∈ Icc 0 T) :
    Integrable (fun w => norm (X.velocity i t w)) (X.measure i t) := by
  letI : IsProbabilityMeasure (X.measure i t) := (X.cap i t ht).probability
  exact Integrable.of_bound (X.velocity_measurable i t ht).norm.aestronglyMeasurable
    (characteristicSpeedBound d O a radius lambda p)
    (by simpa only [norm_norm] using X.velocity_norm_bound hp i t ht)

theorem SphericalCharacteristicSolution.featureSlope_stronglyMeasurable
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (i : Fin 2) (t : Real) (ht : t ∈ Icc 0 T) :
    StronglyMeasurable (X.featureSlope i t) := by
  letI : IsProbabilityMeasure (X.measure i t) := (X.cap i t ht).probability
  exact meanFeatureVelocity_stronglyMeasurable O a _ _ (X.velocity_measurable i t ht)

theorem SphericalCharacteristicSolution.featureSlope_norm_le
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p)
    (i : Fin 2) (t : Real) (ht : t ∈ Icc 0 T) (z : Weight d) :
    norm (X.featureSlope i t z) ≤ fittingFeatureEnvelope O a z * characteristicSpeedBound d O a radius lambda p := by
  letI : IsProbabilityMeasure (X.measure i t) := (X.cap i t ht).probability
  exact meanFeatureVelocity_norm_le O a _ _ (X.velocity_measurable i t ht) _
    (X.velocity_norm_bound hp i t ht) z

/-- The chain rule for each original supported particle. -/
theorem SphericalCharacteristicSolution.particleFeature_hasDerivAt
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (initial i).support)
    (z : Weight d) (t : Real) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => finiteHermiteActivation O a (inner Real (X.characteristic i s w).val z))
      (featureVelocity O a (X.velocity i t) (X.characteristic i t w) z) t := by
  have hinner : HasDerivAt (fun s => inner Real (X.characteristic i s w).val z)
      (inner Real (X.velocity i t (X.characteristic i t w)) z) t := by
    simpa only [SphericalCharacteristicSolution.velocity,inner_zero_right,add_zero,zero_add] using
      (X.ode i w hw t ht).inner Real (hasDerivAt_const t z)
  simpa only [Function.comp_def, Nat.zero_add, finiteHermiteActivationJet_zero,featureVelocity] using
    (finiteHermiteActivationJet_hasDerivAt 0 O a _).scomp t hinner

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Genuine first derivative of the current-law mean feature. -/
theorem SphericalCharacteristicSolution.feature_hasDerivAt
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p)
    (i : Fin 2) (z : Weight d) (t : Real) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => X.feature i s z) (X.featureSlope i t z) t := by
  letI : IsProbabilityMeasure (initial i) := X.initial_probability i
  have htc : t ∈ Icc (0 : Real) T := ⟨ht.1.le,ht.2.le⟩
  letI : IsProbabilityMeasure (X.measure i t) := (X.cap i t htc).probability
  let F := fun (s : Real) (w : UnitSphere d) => finiteHermiteActivation O a (inner Real (X.characteristic i s w).val z)
  let D := fun (s : Real) (w : UnitSphere d) => featureVelocity O a (X.velocity i s) (X.characteristic i s w) z
  let M := characteristicSpeedBound d O a radius lambda p
  let B := fittingFeatureEnvelope O a z
  have hnear : ∀ᶠ s in 𝓝 t, s ∈ Ioo (0 : Real) T := isOpen_Ioo.mem_nhds ht
  have hcfeature : Continuous (fun w : UnitSphere d =>
      finiteHermiteActivation O a (inner Real w.val z)) :=
    (finiteHermiteActivation_continuous O a).comp (continuous_subtype_val.inner continuous_const)
  have hFm (s : Real) (hs : s ∈ Icc (0 : Real) T) : Measurable (F s) :=
    hcfeature.measurable.comp (X.measurable_space i s hs)
  have hFi : Integrable (F t) (initial i) := by
    apply Integrable.of_bound (hFm t htc).aestronglyMeasurable B
    filter_upwards with w
    have hb : norm (F t w) ≤ featureEnvelope 0 O a z := by
      simpa only [F, finiteHermiteActivationJet_zero] using
        finiteHermiteActivationJet_sphere_bound 0 O a (X.characteristic i t w) z
    exact hb.trans (fittingFeatureEnvelope_bounds O a z).1
  have hDm : Measurable (D t) := by
    change Measurable (fun w : UnitSphere d =>
      featureVelocity O a (X.velocity i t) (X.characteristic i t w) z)
    have hm : Measurable (fun zw : Weight d × UnitSphere d =>
        featureVelocity O a (X.velocity i t) zw.2 zw.1) :=
      (featureVelocity_stronglyMeasurable O a (X.velocity i t)
        (X.velocity_measurable i t htc)).measurable
    have hp : Measurable (fun w : UnitSphere d => (z, X.characteristic i t w)) :=
      (measurable_const : Measurable (fun _ : UnitSphere d => z)).prodMk
        (X.measurable_space i t htc)
    exact hm.comp (f := fun w : UnitSphere d => (z, X.characteristic i t w)) hp
  have hDb : ∀ᵐ w ∂initial i, ∀ s ∈ Ioo (0 : Real) T, norm (D s w) ≤ B*M := by
    filter_upwards [Measure.support_mem_ae (μ := initial i)] with w hw
    intro s hs
    have hsc : s ∈ Icc (0 : Real) T := ⟨hs.1.le,hs.2.le⟩
    have hg := X.gradient_norm_le_speedBound hp i s hsc _ (X.characteristic_mem_support i s hsc w hw)
    have hv : norm (X.velocity i s (X.characteristic i s w)) ≤ M := by
      simpa only [SphericalCharacteristicSolution.velocity,norm_neg] using hg
    exact (featureVelocity_norm_le O a _ _ z).trans
      (mul_le_mul_of_nonneg_left hv (fittingFeatureEnvelope_nonneg O a z))
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := D) (bound := fun _ => B*M) (s := Ioo (0 : Real) T) (x₀ := t)
    hnear (hnear.mono (fun s hs => (hFm s ⟨hs.1.le,hs.2.le⟩).aestronglyMeasurable))
    hFi hDm.aestronglyMeasurable hDb (integrable_const _) (by
      filter_upwards [Measure.support_mem_ae (μ := initial i)] with w hw
      intro s hs
      exact X.particleFeature_hasDerivAt i w hw z s hs)
  have he : (fun s => X.feature i s z) =ᶠ[𝓝 t] (fun s => ∫ w, F s w ∂initial i) := by
    filter_upwards [hnear] with s hs
    rw [SphericalCharacteristicSolution.feature,meanFeature,X.map_law i s ⟨hs.1.le,hs.2.le⟩,
      integral_map (X.measurable_space i s ⟨hs.1.le,hs.2.le⟩).aemeasurable
        hcfeature.aestronglyMeasurable]
  have hde : (∫ w, D t w ∂initial i) = X.featureSlope i t z := by
    have hj : StronglyMeasurable (fun zw : Weight d × UnitSphere d =>
        featureVelocity O a (X.velocity i t) zw.2 zw.1) :=
      featureVelocity_stronglyMeasurable O a _ (X.velocity_measurable i t htc)
    have hm : AEStronglyMeasurable (fun w : UnitSphere d =>
        featureVelocity O a (X.velocity i t) w z)
        ((initial i).map (X.characteristic i t)) :=
      (hj.comp_measurable
        ((measurable_const : Measurable (fun _ : UnitSphere d => z)).prodMk
          measurable_id)).aestronglyMeasurable
    rw [SphericalCharacteristicSolution.featureSlope,meanFeatureVelocity,X.map_law i t htc,
      integral_map (X.measurable_space i t htc).aemeasurable hm]

  exact (hd.2.congr_of_eventuallyEq he).congr_deriv hde

end PaperFormalization.MatrixFactorization
