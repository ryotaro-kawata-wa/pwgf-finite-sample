import PaperFormalization.MatrixFactorization.RetractedTensorJets

/-! # MF35: differentiation of actual raw moments under the original law

Both exchanges of derivative and Bochner integral follow from continuous
spherical tangent fields and the uniform normalized-retraction jet bounds. The
moment curve is defined using the actual pushed measure, not a formal jet.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def rawMomentAlongRetract {d : Nat} (n : Nat) (mu : Measure (UnitSphere d))
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0) (t : Real) :
    MomentTensor d n := rawMoment (mu.map (sphericalRetractFamily v hv t)) n

noncomputable def rawMomentAlongRetractFirst {d : Nat} (n : Nat) (mu : Measure (UnitSphere d))
    (v : UnitSphere d → Weight d) (t : Real) : MomentTensor d n :=
  ∫ w, retractedTensorFirst n w (v w) t ∂mu

noncomputable def rawMomentAlongRetractSecond {d : Nat} (n : Nat) (mu : Measure (UnitSphere d))
    (v : UnitSphere d → Weight d) (t : Real) : MomentTensor d n :=
  ∫ w, retractedTensorSecond n w (v w) t ∂mu

/-- The original raw moment under the actual normalized retraction pushforward. -/
theorem rawMomentAlongRetract_integral {d n : Nat} (mu : Measure (UnitSphere d))
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (t : Real) :
    rawMomentAlongRetract n mu v hv t = ∫ w, tensorPower n (sphericalRetractVector w (v w) t) ∂mu := by
  have hp := (sphericalRetractFamily_continuous v hv hc).comp
    (f := fun w : UnitSphere d => (t, w)) (by fun_prop)
  exact integral_map hp.measurable.aemeasurable
    ((tensorPower_continuous d n).comp continuous_subtype_val).aestronglyMeasurable

/-- Every tensor jet is genuinely integrable before its integral is differentiated. -/
theorem rawMomentAlongRetract_integrable {d n : Nat} (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (t : Real) :
    Integrable (fun w => tensorPower n (sphericalRetractVector w (v w) t)) mu ∧
    Integrable (fun w => retractedTensorFirst n w (v w) t) mu ∧
    Integrable (fun w => retractedTensorSecond n w (v w) t) mu := by
  have hm : Continuous (fun w : UnitSphere d => (t, w)) := by fun_prop
  have hp := (sphericalRetractFamily_continuous v hv hc).comp hm
  have h0 := sphere_integrable mu _ ((tensorPower_continuous d n).comp hp.subtype_val)
  have h1 := sphere_integrable mu _ ((retractedTensorFirst_continuous n v hv hc).comp hm)
  have h2 := sphere_integrable mu _ ((retractedTensorSecond_continuous n v hv hc).comp hm)
  constructor
  · convert h0 using 1 <;> rfl
  constructor
  · convert h1 using 1 <;> rfl
  · convert h2 using 1 <;> rfl

/-- Both differentiation exchanges are proved at every signed parameter. -/
theorem rawMomentAlongRetract_variations {d n : Nat} (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (t : Real) :
    HasDerivAt (rawMomentAlongRetract n mu v hv) (rawMomentAlongRetractFirst n mu v t) t ∧
    HasDerivAt (rawMomentAlongRetractFirst n mu v) (rawMomentAlongRetractSecond n mu v t) t := by
  have hm (s : Real) : Continuous (fun w : UnitSphere d => (s, w)) := by fun_prop
  have hp (s : Real) := (sphericalRetractFamily_continuous v hv hc).comp (hm s)
  have hnorm := sphere_integrable mu (fun w => ‖v w‖) hc.norm
  have hnorm2 := sphere_integrable mu (fun w => ‖v w‖ ^ 2) (hc.norm.pow 2)
  have hi := rawMomentAlongRetract_integrable (n := n) mu v hv hc t
  have h1 := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s w => tensorPower n (sphericalRetractVector w (v w) s))
    (F' := fun s w => retractedTensorFirst n w (v w) s)
    (bound := fun w => (2 * (n : Real)) * ‖v w‖) (s := Set.univ) (x₀ := t) Filter.univ_mem
    (Eventually.of_forall (fun s => ((tensorPower_continuous d n).comp (hp s).subtype_val).aestronglyMeasurable))
    hi.1 (((retractedTensorFirst_continuous n v hv hc).comp (hm t)).aestronglyMeasurable)
    (Eventually.of_forall (fun w s _ => retractedTensorFirst_norm_le w (v w) (hv w) s))
    (hnorm.const_mul _) (Eventually.of_forall (fun w s _ => retractedTensor_hasDerivAt w (v w) (hv w) s))
  have h2 := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s w => retractedTensorFirst n w (v w) s)
    (F' := fun s w => retractedTensorSecond n w (v w) s)
    (bound := fun w => (6 * (n : Real) ^ 2) * ‖v w‖ ^ 2) (s := Set.univ) (x₀ := t) Filter.univ_mem
    (Eventually.of_forall (fun s => ((retractedTensorFirst_continuous n v hv hc).comp (hm s)).aestronglyMeasurable))
    hi.2.1 (((retractedTensorSecond_continuous n v hv hc).comp (hm t)).aestronglyMeasurable)
    (Eventually.of_forall (fun w s _ => retractedTensorSecond_norm_le w (v w) (hv w) s))
    (hnorm2.const_mul _) (Eventually.of_forall (fun w s _ => retractedTensorFirst_hasDerivAt w (v w) (hv w) s))
  have he : rawMomentAlongRetract n mu v hv =
      (fun s => ∫ w, tensorPower n (sphericalRetractVector w (v w) s) ∂mu) :=
    funext (rawMomentAlongRetract_integral mu v hv hc)
  exact ⟨he ▸ h1.2, h2.2⟩

/-- The actual second derivative, rather than only a proposed jet formula. -/
theorem rawMomentAlongRetract_second_derivative {d n : Nat} (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (t : Real) :
    HasDerivAt (deriv (rawMomentAlongRetract n mu v hv)) (rawMomentAlongRetractSecond n mu v t) t := by
  have he : deriv (rawMomentAlongRetract n mu v hv) = rawMomentAlongRetractFirst n mu v := by
    funext s
    exact (rawMomentAlongRetract_variations mu v hv hc s).1.deriv
  rw [he]
  exact (rawMomentAlongRetract_variations mu v hv hc t).2

end PaperFormalization.MatrixFactorization
