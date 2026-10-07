import PaperFormalization.MatrixFactorization.GeneralRetractionCost

/-! # Two original-measure derivative exchanges for normalized transport

The common open time neighborhood comes from the original closed support.
Uniform cost derivatives are dominated by continuous tangent-speed moments,
so neither integrability nor differentiation under the integral is assumed.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def marginalRetractedTransportSq {d : Nat} (a : UnitSphere d)
    (mu : Measure (UnitSphere d)) (v : UnitSphere d → Weight d)
    (hv : ∀ w, inner Real w.val (v w) = 0) (t : Real) : Real :=
  sphericalWassersteinSq (mu.map (sphericalRetractFamily v hv t)) (antipodalMeasure a)

@[simp] theorem marginalRetractedTransportSq_zero {d : Nat} (a : UnitSphere d)
    (mu : Measure (UnitSphere d)) (v : UnitSphere d → Weight d)
    (hv : ∀ w, inner Real w.val (v w) = 0) :
    marginalRetractedTransportSq a mu v hv 0 = sphericalWassersteinSq mu (antipodalMeasure a) := by
  have he : sphericalRetractFamily v hv 0 = id := funext (sphericalRetractFamily_zero v hv)
  simp only [marginalRetractedTransportSq, he, Measure.map_id]

theorem retractedFrozen_integral_jets {d : Nat} (a : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (h : TwoCapClass a r mu)
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) :
    ∃ U : Set Real, IsOpen U ∧ 0 ∈ U ∧ ∀ t ∈ U,
      Integrable (retractedFrozenCost a v hv t) mu ∧
      Integrable (retractedFrozenFirst a v hv t) mu ∧
      Integrable (retractedFrozenSecond a v hv t) mu ∧
      HasDerivAt (fun s => integral mu (retractedFrozenCost a v hv s))
        (integral mu (retractedFrozenFirst a v hv t)) t ∧
      HasDerivAt (fun s => integral mu (retractedFrozenFirst a v hv s))
        (integral mu (retractedFrozenSecond a v hv t)) t ∧
      marginalRetractedTransportSq a mu v hv t = 2*integral mu (retractedFrozenCost a v hv t) := by
  letI : IsProbabilityMeasure mu := h.probability
  have hp := h.eventually_preserves (sphericalRetractFamily v hv)
    (sphericalRetractFamily_continuous v hv hc) (sphericalRetractFamily_zero v hv)
  obtain ⟨e,he,hball⟩ := Metric.mem_nhds_iff.mp hp
  let U : Set Real := Metric.ball 0 e ∩ Ioo (-1) 1
  have hU : IsOpen U := Metric.isOpen_ball.inter isOpen_Ioo
  have h0 : (0 : Real) ∈ U := ⟨Metric.mem_ball_self he, by constructor <;> norm_num⟩
  have hdist (w : UnitSphere d) (hw : w ∈ mu.support) (t : Real) (ht : t ∈ U) :
      sphericalDistance (sphericalRetractFamily v hv t w) (assignedPole a w) < r :=
    (preservesCap_frozen_distance h (hball ht.1) hw).1
  have hpi (w : UnitSphere d) (hw : w ∈ mu.support) (t : Real) (ht : t ∈ U) :
      sphericalDistance (sphericalRetractFamily v hv t w) (assignedPole a w) < Real.pi := by
    have hh := hdist w hw t ht
    linarith [h.radius_lt,Real.pi_pos]
  have hnorm : Integrable (fun w : UnitSphere d => norm (v w)) mu := sphere_integrable mu _ hc.norm
  have hnorm2 : Integrable (fun w : UnitSphere d => norm (v w)^2+2*r*norm (v w)^3) mu :=
    sphere_integrable mu _ ((hc.norm.pow 2).add (continuous_const.mul (hc.norm.pow 3)))
  have hd1 : ∀ᵐ w ∂mu, ∀ t ∈ U,
      HasDerivAt (fun s => retractedFrozenCost a v hv s w) (retractedFrozenFirst a v hv t w) t := by
    filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
    intro t ht
    exact retractedFrozenCost_hasDerivAt a v hv t w (hpi w hw t ht)
  have hd2 : ∀ᵐ w ∂mu, ∀ t ∈ U,
      HasDerivAt (fun s => retractedFrozenFirst a v hv s w) (retractedFrozenSecond a v hv t w) t := by
    filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
    intro t ht
    exact retractedFrozenFirst_hasDerivAt a v hv t w (hpi w hw t ht)
  have hb1 : ∀ᵐ w ∂mu, ∀ t ∈ U, norm (retractedFrozenFirst a v hv t w) ≤ r*norm (v w) := by
    filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
    intro t ht
    exact (retractedFrozen_bounds a r h.radius_lt v hv t w (abs_lt.mpr ht.2).le (hdist w hw t ht)).1
  have hb2 : ∀ᵐ w ∂mu, ∀ t ∈ U,
      norm (retractedFrozenSecond a v hv t w) ≤ norm (v w)^2+2*r*norm (v w)^3 := by
    filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
    intro t ht
    exact (retractedFrozen_bounds a r h.radius_lt v hv t w (abs_lt.mpr ht.2).le (hdist w hw t ht)).2
  refine ⟨U,hU,h0,?_⟩
  intro t ht
  have hi := retractedFrozenCost_integrable a mu v hv hc t
  have hfirst := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := retractedFrozenCost a v hv) (F' := retractedFrozenFirst a v hv)
    (bound := fun w => r*norm (v w)) (hU.mem_nhds ht)
    (Filter.Eventually.of_forall (fun s => (retractedFrozen_measurable a v hv hc s).1.aestronglyMeasurable))
    hi ((retractedFrozen_measurable a v hv hc t).2.1.aestronglyMeasurable)
    hb1 (hnorm.const_mul r) hd1
  have hsecond := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := retractedFrozenFirst a v hv) (F' := retractedFrozenSecond a v hv)
    (bound := fun w => norm (v w)^2+2*r*norm (v w)^3) (hU.mem_nhds ht)
    (Filter.Eventually.of_forall (fun s => (retractedFrozen_measurable a v hv hc s).2.1.aestronglyMeasurable))
    hfirst.1 ((retractedFrozen_measurable a v hv hc t).2.2.aestronglyMeasurable)
    hb2 hnorm2 hd2
  refine ⟨hi,hfirst.1,hsecond.1,hfirst.2,hsecond.2,?_⟩
  have hphi : Continuous (sphericalRetractFamily v hv t) :=
    (sphericalRetractFamily_continuous v hv hc).comp
      (f := fun w : UnitSphere d => (t,w)) (continuous_const.prodMk continuous_id)
  have heq := (fixed_assignment_pushforward a r mu h _ hphi (hball ht.1)).2
  change sphericalWassersteinSq _ _ = _
  rw [heq]
  congr 1
  apply integral_congr_ae
  filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
  rw [retractedFrozenCost_source]
  simp only [poleCost, assignedCost, (preservesCap_frozen_distance h (hball ht.1) hw).2]

/-- Both ordinary derivatives of the true optimum retain the source factor 2. -/
theorem marginalRetractedTransport_variations {d : Nat} (a : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (h : TwoCapClass a r mu)
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) :
    HasDerivAt (marginalRetractedTransportSq a mu v hv) (2*marginalCostFirst a mu v) 0 ∧
    HasDerivAt (deriv (marginalRetractedTransportSq a mu v hv)) (2*marginalCostSecond a mu v) 0 ∧
    (∀ᶠ t in 𝓝 (0 : Real), DifferentiableAt Real (marginalRetractedTransportSq a mu v hv) t) := by
  obtain ⟨U,hU,h0,hdata⟩ := retractedFrozen_integral_jets a r mu h v hv hc
  have hder (t : Real) (ht : t ∈ U) :
      HasDerivAt (marginalRetractedTransportSq a mu v hv)
        (2*integral mu (retractedFrozenFirst a v hv t)) t := by
    obtain ⟨_,_,_,hd,_,_⟩ := hdata t ht
    apply (hd.const_mul 2).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds ht] with s hs
    exact (hdata s hs).2.2.2.2.2
  obtain ⟨_,_,_,_,hd2,_⟩ := hdata 0 h0
  have hsecond : HasDerivAt (deriv (marginalRetractedTransportSq a mu v hv))
      (2*integral mu (retractedFrozenSecond a v hv 0)) 0 := by
    apply (hd2.const_mul 2).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds h0] with t ht
    exact (hder t ht).deriv
  refine ⟨?_,?_,?_⟩
  · simpa only [retractedFrozenFirst_zero, marginalCostFirst] using hder 0 h0
  · simpa only [retractedFrozenSecond_zero, marginalCostSecond] using hsecond
  · filter_upwards [hU.mem_nhds h0] with t ht
    exact (hder t ht).differentiableAt

end PaperFormalization.MatrixFactorization
