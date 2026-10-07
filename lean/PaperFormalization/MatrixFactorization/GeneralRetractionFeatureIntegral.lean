import PaperFormalization.MatrixFactorization.GeneralRetractionFeatures

/-! # MF10: normalized feature differentiation under the original sphere measure

The mean feature is defined using the actual normalized-retraction-pushed measure. The map identity
then expresses it under the original measure. Continuous tangent fields on the
compact sphere supply the integrable speed and squared-speed bounds, so both
exchanges of derivative and integral are proved, rather than assumed.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def meanFeatureJetAlongRetract {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (mu : Measure (UnitSphere d))
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (z : Weight d) (t : Real) : Weight h :=
  meanFeature (finiteHermiteActivationJet k O a) (mu.map (sphericalRetractFamily v hv t)) z

noncomputable def meanFeatureJetAlongRetractFirst {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (mu : Measure (UnitSphere d))
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (z : Weight d) (t : Real) : Weight h :=
  ∫ w, retractedFeatureFirst k O a w (v w) (hv w) z t ∂mu

noncomputable def meanFeatureJetAlongRetractSecond {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (mu : Measure (UnitSphere d))
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (z : Weight d) (t : Real) : Weight h :=
  ∫ w, retractedFeatureSecond k O a w (v w) (hv w) z t ∂mu

@[simp] theorem meanFeatureJetAlongRetract_zero_order {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (mu : Measure (UnitSphere d))
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (z : Weight d) (t : Real) :
    meanFeatureJetAlongRetract 0 O a mu v hv z t =
      meanFeature (finiteHermiteActivation O a) (mu.map (sphericalRetractFamily v hv t)) z := by
  have he : finiteHermiteActivationJet 0 O a = finiteHermiteActivation O a :=
    funext (finiteHermiteActivationJet_zero O a)
  rw [meanFeatureJetAlongRetract, he]

theorem meanFeatureJetAlongRetract_integral {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (mu : Measure (UnitSphere d))
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (z : Weight d) (t : Real) :
    meanFeatureJetAlongRetract k O a mu v hv z t =
      ∫ w, retractedFeatureJet k O a w (v w) (hv w) z t ∂mu := by
  have hphi : Continuous (sphericalRetractFamily v hv t) :=
    (sphericalRetractFamily_continuous v hv hc).comp
      (f := fun w : UnitSphere d => (t,w)) (by fun_prop)
  have hi : Continuous (fun w : UnitSphere d => finiteHermiteActivationJet k O a (inner Real w.val z)) :=
    (finiteHermiteActivationJet_continuous k O a).comp (by fun_prop)
  exact integral_map hphi.measurable.aemeasurable hi.aestronglyMeasurable

/-- All three integrands are genuinely Bochner integrable at every time. -/
theorem retractedFeature_integrable {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu]
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (z : Weight d) (t : Real) :
    Integrable (fun w => retractedFeatureJet k O a w (v w) (hv w) z t) mu ∧
    Integrable (fun w => retractedFeatureFirst k O a w (v w) (hv w) z t) mu ∧
    Integrable (fun w => retractedFeatureSecond k O a w (v w) (hv w) z t) mu := by
  have hm : Continuous (fun w : UnitSphere d => ((t,z),w)) :=
    continuous_const.prodMk continuous_id
  exact ⟨sphere_integrable mu _ ((retractedFeatureJet_continuous k O a v hv hc).comp (f := fun w => ((t,z),w)) hm),
    sphere_integrable mu _ ((retractedFeatureFirst_continuous k O a v hv hc).comp (f := fun w => ((t,z),w)) hm),
    sphere_integrable mu _ ((retractedFeatureSecond_continuous k O a v hv hc).comp (f := fun w => ((t,z),w)) hm)⟩

theorem meanFeatureJetAlongRetract_variations {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu]
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (z : Weight d) (t : Real) :
    HasDerivAt (meanFeatureJetAlongRetract k O a mu v hv z)
      (meanFeatureJetAlongRetractFirst k O a mu v hv z t) t ∧
    HasDerivAt (meanFeatureJetAlongRetractFirst k O a mu v hv z)
      (meanFeatureJetAlongRetractSecond k O a mu v hv z t) t := by
  have hnorm : Integrable (fun w => norm (v w)) mu := sphere_integrable mu _ hc.norm
  have hnorm2 : Integrable (fun w => (norm (v w))^2) mu := sphere_integrable mu _ (hc.norm.pow 2)
  have hm (s : Real) : Continuous (fun w : UnitSphere d => ((s,z),w)) :=
    continuous_const.prodMk continuous_id
  have hi := retractedFeature_integrable k O a mu v hv hc z t
  have h1 := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s w => retractedFeatureJet k O a w (v w) (hv w) z s)
    (F' := fun s w => retractedFeatureFirst k O a w (v w) (hv w) z s)
    (bound := fun w => 2*norm (v w)*featureFirstEnvelope k O a z)
    (s := Set.univ) (x₀ := t) (Filter.univ_mem)
    (Eventually.of_forall (fun s => ((retractedFeatureJet_continuous k O a v hv hc).comp (f := fun w => ((s,z),w)) (hm s)).aestronglyMeasurable))
    hi.1 (((retractedFeatureFirst_continuous k O a v hv hc).comp (f := fun w => ((t,z),w)) (hm t)).aestronglyMeasurable)
    (Eventually.of_forall (fun w s _ => retractedFeatureFirst_bound k O a w (v w) (hv w) z s))
    ((hnorm.const_mul 2).mul_const _) (Eventually.of_forall (fun w s _ => retractedFeatureJet_hasDerivAt k O a w (v w) (hv w) z s))
  have h2 := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s w => retractedFeatureFirst k O a w (v w) (hv w) z s)
    (F' := fun s w => retractedFeatureSecond k O a w (v w) (hv w) z s)
    (bound := fun w => 6*(norm (v w))^2*featureSecondEnvelope k O a z)
    (s := Set.univ) (x₀ := t) (Filter.univ_mem)
    (Eventually.of_forall (fun s => ((retractedFeatureFirst_continuous k O a v hv hc).comp (f := fun w => ((s,z),w)) (hm s)).aestronglyMeasurable))
    hi.2.1 (((retractedFeatureSecond_continuous k O a v hv hc).comp (f := fun w => ((t,z),w)) (hm t)).aestronglyMeasurable)
    (Eventually.of_forall (fun w s _ => retractedFeatureSecond_bound k O a w (v w) (hv w) z s))
    ((hnorm2.const_mul 6).mul_const _) (Eventually.of_forall (fun w s _ => retractedFeatureFirst_hasDerivAt k O a w (v w) (hv w) z s))
  have he : meanFeatureJetAlongRetract k O a mu v hv z =
      (fun s => ∫ w, retractedFeatureJet k O a w (v w) (hv w) z s ∂mu) :=
    funext (meanFeatureJetAlongRetract_integral k O a mu v hv hc z)
  exact ⟨he ▸ h1.2, h2.2⟩

theorem meanFeatureJetAlongRetract_second_derivative {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu]
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (z : Weight d) (t : Real) :
    HasDerivAt (deriv (meanFeatureJetAlongRetract k O a mu v hv z))
      (meanFeatureJetAlongRetractSecond k O a mu v hv z t) t := by
  have he : deriv (meanFeatureJetAlongRetract k O a mu v hv z) = meanFeatureJetAlongRetractFirst k O a mu v hv z := by
    funext s
    exact (meanFeatureJetAlongRetract_variations k O a mu v hv hc z s).1.deriv
  rw [he]
  exact (meanFeatureJetAlongRetract_variations k O a mu v hv hc z t).2

/-- The zeroth, first, and second original-measure jets agree exactly with
EXP at zero. These identities follow after both differentiation exchanges. -/
theorem meanFeatureJetAlongRetract_initial_jets {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (mu : Measure (UnitSphere d))
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (z : Weight d) :
    meanFeatureJetAlongRetract k O a mu v hv z 0 = meanFeatureJetAlongExp k O a mu v hv z 0 ∧
    meanFeatureJetAlongRetractFirst k O a mu v hv z 0 = meanFeatureJetAlongExpFirst k O a mu v hv z 0 ∧
    meanFeatureJetAlongRetractSecond k O a mu v hv z 0 = meanFeatureJetAlongExpSecond k O a mu v hv z 0 := by
  constructor
  · rw [meanFeatureJetAlongRetract_integral k O a mu v hv hc,
      meanFeatureJetAlongExp_integral k O a mu v hv hc]
    simp only [retractedFeatureJet_at_zero, sphericalFeatureJet_at_zero]
  constructor
  · simp only [meanFeatureJetAlongRetractFirst, meanFeatureJetAlongExpFirst,
      retractedFeatureFirst_at_zero, sphericalFeatureFirst_at_zero]
  · simp only [meanFeatureJetAlongRetractSecond, meanFeatureJetAlongExpSecond,
      retractedFeatureSecond_at_zero, sphericalFeatureSecond_at_zero]

end PaperFormalization.MatrixFactorization
