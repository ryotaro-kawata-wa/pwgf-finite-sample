import PaperFormalization.MatrixFactorization.SphericalCostDifferential

/-! # MF03: dominated differentiation on the ORIGINAL compact-cap measures

MF03 checkpoint candidate; see MF03_VALIDATION.md for execution status.
The pole used inside the integrand is the original
assigned pole, frozen in time. MF02 proves that this frozen assignment agrees
with the true transport optimum on one common open time neighborhood.
Both derivative bounds and integrability are derived, not model premises.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def assignedGradient {d : Nat} (a w : UnitSphere d) : Weight d :=
  poleGradient (assignedPole a w) w

noncomputable def assignedHessian {d : Nat} (a w : UnitSphere d) (v : Weight d) : Real :=
  poleHessian (assignedPole a w) w v

noncomputable def frozenPoleCost {d : Nat} (a : UnitSphere d)
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (t : Real) (w : UnitSphere d) : Real :=
  poleCost (assignedPole a w) (sphericalExpFamily v hv t w)

noncomputable def frozenPoleFirst {d : Nat} (a : UnitSphere d)
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (t : Real) (w : UnitSphere d) : Real :=
  poleCostSlope (assignedPole a w) (sphericalExpFamily v hv t w) (sphereExpVelocity w (v w) t)

noncomputable def frozenPoleSecond {d : Nat} (a : UnitSphere d)
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (t : Real) (w : UnitSphere d) : Real :=
  poleHessian (assignedPole a w) (sphericalExpFamily v hv t w) (sphereExpVelocity w (v w) t)

/-- Original closed support, not a replacement with a weaker AE class. -/
theorem preservesCap_frozen_distance {d : Nat} {a : UnitSphere d} {r : Real}
    {mu : Measure (UnitSphere d)} (h : TwoCapClass a r mu)
    {f : UnitSphere d → UnitSphere d} (hf : PreservesCapAssignment a r mu f)
    {w : UnitSphere d} (hw : w ∈ mu.support) :
    sphericalDistance (f w) (assignedPole a w) < r ∧
      assignedPole a (f w) = assignedPole a w := by
  rcases h.support_subset hw with hp | hn
  · rw [assignedPole_positive a r h.radius_lt hp]
    exact ⟨(hf w hw).1 hp, assignedPole_positive a r h.radius_lt ((hf w hw).1 hp)⟩
  · rw [assignedPole_negative a r h.radius_lt hn]
    exact ⟨(hf w hw).2 hn, assignedPole_negative a r h.radius_lt ((hf w hw).2 hn)⟩

theorem frozenPole_measurable {d : Nat} (a : UnitSphere d)
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (t : Real) :
    Measurable (frozenPoleCost a v hv t) ∧
    Measurable (frozenPoleFirst a v hv t) ∧ Measurable (frozenPoleSecond a v hv t) := by
  have hambient : Continuous (fun w => sphereExpVector w (t • v w)) := by
    unfold sphereExpVector
    fun_prop
  have hphi : Measurable (fun w => sphericalExpFamily v hv t w) :=
    (hambient.subtype_mk (fun w => (sphericalExpFamily v hv t w).property)).measurable
  have hvel : Measurable (fun w : UnitSphere d => sphereExpVelocity w (v w) t) := by
    have h : Continuous (fun w : UnitSphere d => sphereExpVelocity w (v w) t) := by
      unfold sphereExpVelocity
      fun_prop
    exact h.measurable
  have hpair : Measurable (fun w =>
      ((assignedPole a w, sphericalExpFamily v hv t w), sphereExpVelocity w (v w) t)) :=
    ((assignedPole_measurable a).prodMk hphi).prodMk hvel
  refine ⟨?_, ?_, ?_⟩
  · change Measurable (fun w =>
      (sphericalDistance (sphericalExpFamily v hv t w) (assignedPole a w))^2/2)
    exact (((sphericalDistance_continuous d).measurable.comp
      (hphi.prodMk (assignedPole_measurable a))).pow_const 2).div_const 2
  · change Measurable (fun w => poleCostSlope (assignedPole a w)
      (sphericalExpFamily v hv t w) (sphereExpVelocity w (v w) t))
    exact (poleCostSlope_measurable d).comp
      (f := fun w => ((assignedPole a w, sphericalExpFamily v hv t w),
        sphereExpVelocity w (v w) t)) hpair
  · change Measurable (fun w => poleHessian (assignedPole a w)
      (sphericalExpFamily v hv t w) (sphereExpVelocity w (v w) t))
    exact (poleHessian_measurable d).comp
      (f := fun w => ((assignedPole a w, sphericalExpFamily v hv t w),
        sphereExpVelocity w (v w) t)) hpair

/-- The zeroth-order integral is genuinely finite at every time. -/
theorem frozenPoleCost_integrable {d : Nat} (a : UnitSphere d)
    (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu]
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (t : Real) : Integrable (frozenPoleCost a v hv t) mu := by
  apply Integrable.of_bound ((frozenPole_measurable a v hv hc t).1.aestronglyMeasurable)
    (Real.pi^2/2)
  filter_upwards with w
  have hn := sphericalDistance_nonneg (sphericalExpFamily v hv t w) (assignedPole a w)
  have hl := sphericalDistance_le_pi (sphericalExpFamily v hv t w) (assignedPole a w)
  change |(sphericalDistance (sphericalExpFamily v hv t w) (assignedPole a w))^2/2| ≤ _
  rw [abs_of_nonneg (by positivity)]
  nlinarith [Real.pi_pos]

noncomputable def marginalExpTransportSq {d : Nat} (a : UnitSphere d)
    (mu : Measure (UnitSphere d)) (v : UnitSphere d → Weight d)
    (hv : ∀ w, inner Real w.val (v w) = 0) (t : Real) : Real :=
  sphericalWassersteinSq (mu.map (sphericalExpFamily v hv t)) (antipodalMeasure a)

@[simp] theorem marginalExpTransportSq_zero {d : Nat} (a : UnitSphere d)
    (mu : Measure (UnitSphere d)) (v : UnitSphere d → Weight d)
    (hv : ∀ w, inner Real w.val (v w) = 0) :
    marginalExpTransportSq a mu v hv 0 = sphericalWassersteinSq mu (antipodalMeasure a) := by
  have he : sphericalExpFamily v hv 0 = id := funext (sphericalExpFamily_zero v hv)
  simp only [marginalExpTransportSq, he, Measure.map_id]

/-- One open neighborhood supplies the transport identity, both derivatives,
and all three genuine integrability statements under the same original mu. -/
theorem frozenPole_integral_jets {d : Nat} (a : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (h : TwoCapClass a r mu)
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) :
    ∃ U : Set Real, IsOpen U ∧ 0 ∈ U ∧ ∀ t ∈ U,
      Integrable (frozenPoleCost a v hv t) mu ∧
      Integrable (frozenPoleFirst a v hv t) mu ∧
      Integrable (frozenPoleSecond a v hv t) mu ∧
      HasDerivAt (fun s => integral mu (frozenPoleCost a v hv s))
        (integral mu (frozenPoleFirst a v hv t)) t ∧
      HasDerivAt (fun s => integral mu (frozenPoleFirst a v hv s))
        (integral mu (frozenPoleSecond a v hv t)) t ∧
      marginalExpTransportSq a mu v hv t = 2*integral mu (frozenPoleCost a v hv t) := by
  letI : IsProbabilityMeasure mu := h.probability
  have hp := h.eventually_preserves (sphericalExpFamily v hv)
    (sphericalExpFamily_continuous v hv hc) (sphericalExpFamily_zero v hv)
  obtain ⟨e,he,hball⟩ := Metric.mem_nhds_iff.mp hp
  let U : Set Real := Metric.ball 0 e
  have hU : IsOpen U := Metric.isOpen_ball
  have h0 : (0 : Real) ∈ U := Metric.mem_ball_self he
  have hdist (w : UnitSphere d) (hw : w ∈ mu.support) (t : Real) (ht : t ∈ U) :
      sphericalDistance (sphericalExpFamily v hv t w) (assignedPole a w) < r :=
    (preservesCap_frozen_distance h (hball ht) hw).1
  have hpi (w : UnitSphere d) (hw : w ∈ mu.support) (t : Real) (ht : t ∈ U) :
      sphericalDistance (sphericalExpFamily v hv t w) (assignedPole a w) < Real.pi := by
    have hh := hdist w hw t ht
    linarith [h.radius_lt,Real.pi_pos]
  have hnorm : Integrable (fun w : UnitSphere d => norm (v w)) mu := sphere_integrable mu _ hc.norm
  have hnorm2 : Integrable (fun w : UnitSphere d => (norm (v w))^2) mu :=
    sphere_integrable mu _ (hc.norm.pow 2)
  have hd1 : ∀ᵐ w ∂mu, ∀ t ∈ U,
      HasDerivAt (fun s => frozenPoleCost a v hv s w) (frozenPoleFirst a v hv t w) t := by
    filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
    intro t ht
    exact poleCost_hasDerivAt (assignedPole a w) w (v w) (hv w) t (hpi w hw t ht)
  have hd2 : ∀ᵐ w ∂mu, ∀ t ∈ U,
      HasDerivAt (fun s => frozenPoleFirst a v hv s w) (frozenPoleSecond a v hv t w) t := by
    filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
    intro t ht
    exact poleCostSlope_hasDerivAt (assignedPole a w) w (v w) (hv w) t (hpi w hw t ht)
  have hb1 : ∀ᵐ w ∂mu, ∀ t ∈ U, norm (frozenPoleFirst a v hv t w) ≤ r*norm (v w) := by
    filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
    intro t ht
    have hb := poleCostSlope_bound (assignedPole a w) (sphericalExpFamily v hv t w)
      (sphereExpVelocity w (v w) t) (hpi w hw t ht)
    rw [sphereExpVelocity_norm w (v w) (hv w) t] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (hdist w hw t ht).le (norm_nonneg _))
  have hb2 : ∀ᵐ w ∂mu, ∀ t ∈ U, norm (frozenPoleSecond a v hv t w) ≤ (norm (v w))^2 := by
    filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
    intro t ht
    have hb := poleHessian_abs_bound (assignedPole a w) (sphericalExpFamily v hv t w)
      (sphereExpVelocity w (v w) t) ((hdist w hw t ht).trans h.radius_lt)
    simpa only [frozenPoleSecond,Real.norm_eq_abs,sphereExpVelocity_norm w (v w) (hv w) t] using hb
  refine ⟨U,hU,h0,?_⟩
  intro t ht
  have hi := frozenPoleCost_integrable a mu v hv hc t
  have hfirst := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := frozenPoleCost a v hv) (F' := frozenPoleFirst a v hv)
    (bound := fun w => r*norm (v w)) (hU.mem_nhds ht)
    (Filter.Eventually.of_forall (fun s => (frozenPole_measurable a v hv hc s).1.aestronglyMeasurable))
    hi ((frozenPole_measurable a v hv hc t).2.1.aestronglyMeasurable)
    hb1 (hnorm.const_mul r) hd1
  have hsecond := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := frozenPoleFirst a v hv) (F' := frozenPoleSecond a v hv)
    (bound := fun w => (norm (v w))^2) (hU.mem_nhds ht)
    (Filter.Eventually.of_forall (fun s => (frozenPole_measurable a v hv hc s).2.1.aestronglyMeasurable))
    hfirst.1 ((frozenPole_measurable a v hv hc t).2.2.aestronglyMeasurable)
    hb2 hnorm2 hd2
  refine ⟨hi,hfirst.1,hsecond.1,hfirst.2,hsecond.2,?_⟩
  have hphi : Continuous (sphericalExpFamily v hv t) := by
    have hambient : Continuous (fun w => sphereExpVector w (t • v w)) := by
      unfold sphereExpVector
      fun_prop
    exact hambient.subtype_mk (fun w => (sphericalExpFamily v hv t w).property)
  have heq := (fixed_assignment_pushforward a r mu h _ hphi (hball ht)).2
  change sphericalWassersteinSq _ _ = _
  rw [heq]
  congr 1
  apply integral_congr_ae
  filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
  simp only [frozenPoleCost,poleCost,assignedCost,
    (preservesCap_frozen_distance h (hball ht) hw).2]

noncomputable def marginalCostFirst {d : Nat} (a : UnitSphere d)
    (mu : Measure (UnitSphere d)) (v : UnitSphere d → Weight d) : Real :=
  integral mu (fun w => inner Real (assignedGradient a w) (v w))

noncomputable def marginalCostSecond {d : Nat} (a : UnitSphere d)
    (mu : Measure (UnitSphere d)) (v : UnitSphere d → Weight d) : Real :=
  integral mu (fun w => assignedHessian a w (v w))

/-- Literal first and iterated second derivatives of the optimal transport cost.
The original factor 2 from Z=2D is retained in BOTH derivatives. -/
theorem marginalTransport_variations {d : Nat} (a : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (h : TwoCapClass a r mu)
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) :
    Integrable (fun w => inner Real (assignedGradient a w) (v w)) mu ∧
    Integrable (fun w => assignedHessian a w (v w)) mu ∧
    HasDerivAt (marginalExpTransportSq a mu v hv) (2*marginalCostFirst a mu v) 0 ∧
    HasDerivAt (deriv (marginalExpTransportSq a mu v hv)) (2*marginalCostSecond a mu v) 0 ∧
    (∀ᶠ t in 𝓝 (0 : Real), DifferentiableAt Real (marginalExpTransportSq a mu v hv) t) := by
  obtain ⟨U,hU,h0,hdata⟩ := frozenPole_integral_jets a r mu h v hv hc
  have hder (t : Real) (ht : t ∈ U) :
      HasDerivAt (marginalExpTransportSq a mu v hv)
        (2*integral mu (frozenPoleFirst a v hv t)) t := by
    obtain ⟨_,_,_,hd,_,_⟩ := hdata t ht
    apply (hd.const_mul 2).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds ht] with s hs
    exact (hdata s hs).2.2.2.2.2
  obtain ⟨_,hi1,hi2,_,hd2,_⟩ := hdata 0 h0
  have hsecond : HasDerivAt (deriv (marginalExpTransportSq a mu v hv))
      (2*integral mu (frozenPoleSecond a v hv 0)) 0 := by
    apply (hd2.const_mul 2).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds h0] with t ht
    exact (hder t ht).deriv
  have hevent : ∀ᶠ t in 𝓝 (0 : Real), DifferentiableAt Real (marginalExpTransportSq a mu v hv) t := by
    filter_upwards [hU.mem_nhds h0] with t ht
    exact (hder t ht).differentiableAt
  have hf0 : frozenPoleFirst a v hv 0 =
      (fun w => inner Real (assignedGradient a w) (v w)) := by
    funext w
    simp only [frozenPoleFirst, sphericalExpFamily_zero, sphereExpVelocity_at_zero,
      poleCostSlope, assignedGradient]
  have hs0 : frozenPoleSecond a v hv 0 = (fun w => assignedHessian a w (v w)) := by
    funext w
    simp only [frozenPoleSecond, sphericalExpFamily_zero, sphereExpVelocity_at_zero,
      assignedHessian]
  refine ⟨?_,?_,?_,?_,hevent⟩
  · simpa only [hf0] using hi1
  · simpa only [hs0] using hi2
  · simpa only [hf0, marginalCostFirst] using hder 0 h0
  · simpa only [hs0, marginalCostSecond] using hsecond

end PaperFormalization.MatrixFactorization
