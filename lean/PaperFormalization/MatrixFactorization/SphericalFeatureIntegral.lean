import PaperFormalization.MatrixFactorization.SphericalFeatureBounds

/-! # MF04: feature differentiation under the original sphere measure

The mean feature is defined using the actual EXP-pushed measure. The map identity
then expresses it under the original measure. Continuous tangent fields on the
compact sphere supply the integrable speed and squared-speed bounds, so both
exchanges of derivative and integral are proved, rather than assumed.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Joint continuity also supplies measurability in the Gaussian input later. -/
theorem sphericalFeatureJet_continuous {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (v : UnitSphere d → Weight d)
    (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) :
    Continuous (fun p : (Real × Weight d) × UnitSphere d =>
      sphericalFeatureJet k O a p.2 (v p.2) (hv p.2) p.1.2 p.1.1) := by
  have hg : Continuous (fun p : (Real × Weight d) × UnitSphere d =>
      sphereExpVector p.2 (p.1.1 • v p.2)) := by
    unfold sphereExpVector
    fun_prop
  exact (finiteHermiteActivationJet_continuous k O a).comp
    (hg.inner (continuous_snd.comp continuous_fst))

theorem sphericalFeatureFirst_continuous {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (v : UnitSphere d → Weight d)
    (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) :
    Continuous (fun p : (Real × Weight d) × UnitSphere d =>
      sphericalFeatureFirst k O a p.2 (v p.2) (hv p.2) p.1.2 p.1.1) := by
  have hg : Continuous (fun p : (Real × Weight d) × UnitSphere d =>
      sphereExpVelocity p.2 (v p.2) p.1.1) := by
    unfold sphereExpVelocity
    fun_prop
  have hi : Continuous (fun p : (Real × Weight d) × UnitSphere d =>
      inner Real (sphereExpVelocity p.2 (v p.2) p.1.1) p.1.2) :=
    hg.inner (continuous_snd.comp continuous_fst)
  exact hi.smul
    (sphericalFeatureJet_continuous (k+1) O a v hv hc)

theorem sphericalFeatureSecond_continuous {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (v : UnitSphere d → Weight d)
    (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) :
    Continuous (fun p : (Real × Weight d) × UnitSphere d =>
      sphericalFeatureSecond k O a p.2 (v p.2) (hv p.2) p.1.2 p.1.1) := by
  have hvel : Continuous (fun p : (Real × Weight d) × UnitSphere d =>
      inner Real (sphereExpVelocity p.2 (v p.2) p.1.1) p.1.2) := by
    unfold sphereExpVelocity
    fun_prop
  have hpoint : Continuous (fun p : (Real × Weight d) × UnitSphere d =>
      (norm (v p.2))^2 * inner Real (geodesicPoint p.2 (v p.2) (hv p.2) p.1.1).val p.1.2) := by
    simp only [geodesicPoint_val]
    unfold sphereExpVector
    fun_prop
  exact ((hvel.pow 2).smul (sphericalFeatureJet_continuous (k+2) O a v hv hc)).sub
    (hpoint.smul (sphericalFeatureJet_continuous (k+1) O a v hv hc))

noncomputable def meanFeatureJetAlongExp {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (mu : Measure (UnitSphere d))
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (z : Weight d) (t : Real) : Weight h :=
  meanFeature (finiteHermiteActivationJet k O a) (mu.map (sphericalExpFamily v hv t)) z

noncomputable def meanFeatureJetAlongExpFirst {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (mu : Measure (UnitSphere d))
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (z : Weight d) (t : Real) : Weight h :=
  ∫ w, sphericalFeatureFirst k O a w (v w) (hv w) z t ∂mu

noncomputable def meanFeatureJetAlongExpSecond {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (mu : Measure (UnitSphere d))
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (z : Weight d) (t : Real) : Weight h :=
  ∫ w, sphericalFeatureSecond k O a w (v w) (hv w) z t ∂mu

@[simp] theorem meanFeatureJetAlongExp_zero_order {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (mu : Measure (UnitSphere d))
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (z : Weight d) (t : Real) :
    meanFeatureJetAlongExp 0 O a mu v hv z t =
      meanFeature (finiteHermiteActivation O a) (mu.map (sphericalExpFamily v hv t)) z := by
  have he : finiteHermiteActivationJet 0 O a = finiteHermiteActivation O a :=
    funext (finiteHermiteActivationJet_zero O a)
  rw [meanFeatureJetAlongExp, he]

theorem meanFeatureJetAlongExp_integral {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (mu : Measure (UnitSphere d))
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (z : Weight d) (t : Real) :
    meanFeatureJetAlongExp k O a mu v hv z t =
      ∫ w, sphericalFeatureJet k O a w (v w) (hv w) z t ∂mu := by
  have hambient : Continuous (fun w => sphereExpVector w (t • v w)) := by
    unfold sphereExpVector
    fun_prop
  have hphi : Continuous (sphericalExpFamily v hv t) :=
    hambient.subtype_mk (fun w => (sphericalExpFamily v hv t w).property)
  have hi : Continuous (fun w : UnitSphere d => finiteHermiteActivationJet k O a (inner Real w.val z)) :=
    (finiteHermiteActivationJet_continuous k O a).comp (by fun_prop)
  exact integral_map hphi.measurable.aemeasurable hi.aestronglyMeasurable

/-- All three integrands are genuinely Bochner integrable at every time. -/
theorem sphericalFeature_integrable {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu]
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (z : Weight d) (t : Real) :
    Integrable (fun w => sphericalFeatureJet k O a w (v w) (hv w) z t) mu ∧
    Integrable (fun w => sphericalFeatureFirst k O a w (v w) (hv w) z t) mu ∧
    Integrable (fun w => sphericalFeatureSecond k O a w (v w) (hv w) z t) mu := by
  have hm : Continuous (fun w : UnitSphere d => ((t,z),w)) :=
    continuous_const.prodMk continuous_id
  exact ⟨sphere_integrable mu _ ((sphericalFeatureJet_continuous k O a v hv hc).comp (f := fun w => ((t,z),w)) hm),
    sphere_integrable mu _ ((sphericalFeatureFirst_continuous k O a v hv hc).comp (f := fun w => ((t,z),w)) hm),
    sphere_integrable mu _ ((sphericalFeatureSecond_continuous k O a v hv hc).comp (f := fun w => ((t,z),w)) hm)⟩

theorem meanFeatureJetAlongExp_variations {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu]
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (z : Weight d) (t : Real) :
    HasDerivAt (meanFeatureJetAlongExp k O a mu v hv z)
      (meanFeatureJetAlongExpFirst k O a mu v hv z t) t ∧
    HasDerivAt (meanFeatureJetAlongExpFirst k O a mu v hv z)
      (meanFeatureJetAlongExpSecond k O a mu v hv z t) t := by
  have hnorm : Integrable (fun w => norm (v w)) mu := sphere_integrable mu _ hc.norm
  have hnorm2 : Integrable (fun w => (norm (v w))^2) mu := sphere_integrable mu _ (hc.norm.pow 2)
  have hm (s : Real) : Continuous (fun w : UnitSphere d => ((s,z),w)) :=
    continuous_const.prodMk continuous_id
  have hi := sphericalFeature_integrable k O a mu v hv hc z t
  have h1 := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s w => sphericalFeatureJet k O a w (v w) (hv w) z s)
    (F' := fun s w => sphericalFeatureFirst k O a w (v w) (hv w) z s)
    (bound := fun w => norm (v w)*featureFirstEnvelope k O a z)
    (s := Set.univ) (x₀ := t) (Filter.univ_mem)
    (Eventually.of_forall (fun s => ((sphericalFeatureJet_continuous k O a v hv hc).comp (f := fun w => ((s,z),w)) (hm s)).aestronglyMeasurable))
    hi.1 (((sphericalFeatureFirst_continuous k O a v hv hc).comp (f := fun w => ((t,z),w)) (hm t)).aestronglyMeasurable)
    (Eventually.of_forall (fun w s _ => sphericalFeatureFirst_bound k O a w (v w) (hv w) z s))
    (hnorm.mul_const _) (Eventually.of_forall (fun w s _ => sphericalFeatureJet_hasDerivAt k O a w (v w) (hv w) z s))
  have h2 := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s w => sphericalFeatureFirst k O a w (v w) (hv w) z s)
    (F' := fun s w => sphericalFeatureSecond k O a w (v w) (hv w) z s)
    (bound := fun w => (norm (v w))^2*featureSecondEnvelope k O a z)
    (s := Set.univ) (x₀ := t) (Filter.univ_mem)
    (Eventually.of_forall (fun s => ((sphericalFeatureFirst_continuous k O a v hv hc).comp (f := fun w => ((s,z),w)) (hm s)).aestronglyMeasurable))
    hi.2.1 (((sphericalFeatureSecond_continuous k O a v hv hc).comp (f := fun w => ((t,z),w)) (hm t)).aestronglyMeasurable)
    (Eventually.of_forall (fun w s _ => sphericalFeatureSecond_bound k O a w (v w) (hv w) z s))
    (hnorm2.mul_const _) (Eventually.of_forall (fun w s _ => sphericalFeatureFirst_hasDerivAt k O a w (v w) (hv w) z s))
  have he : meanFeatureJetAlongExp k O a mu v hv z =
      (fun s => ∫ w, sphericalFeatureJet k O a w (v w) (hv w) z s ∂mu) :=
    funext (meanFeatureJetAlongExp_integral k O a mu v hv hc z)
  exact ⟨he ▸ h1.2, h2.2⟩

theorem meanFeatureJetAlongExp_second_derivative {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu]
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (z : Weight d) (t : Real) :
    HasDerivAt (deriv (meanFeatureJetAlongExp k O a mu v hv z))
      (meanFeatureJetAlongExpSecond k O a mu v hv z t) t := by
  have he : deriv (meanFeatureJetAlongExp k O a mu v hv z) = meanFeatureJetAlongExpFirst k O a mu v hv z := by
    funext s
    exact (meanFeatureJetAlongExp_variations k O a mu v hv hc z s).1.deriv
  rw [he]
  exact (meanFeatureJetAlongExp_variations k O a mu v hv hc z t).2

end PaperFormalization.MatrixFactorization
