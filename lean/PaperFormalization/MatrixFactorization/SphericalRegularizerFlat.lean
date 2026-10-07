import PaperFormalization.MatrixFactorization.SphericalRegularizer

/-! # MF03: actual zero-target law and regularizer Hessian-flatness

MF03 checkpoint candidate; see MF03_VALIDATION.md for execution status.
Zero optimal transport is shown to imply the original
antipodal law, not assumed to do so. The original EXP transport at that law is
exactly t^2 times tangent energy on a common neighborhood. Thus the regularizer
is a multiple of |t|^p, and its first AND ordinary second derivatives vanish
for every real p>2. No positive-distance quotient is evaluated at zero.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The zero cost law is obtained from genuine nonnegative integrability. -/
theorem zeroTransport_ae_assigned {d : Nat} (a : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (h : TwoCapClass a r mu)
    (hz : sphericalWassersteinSq mu (antipodalMeasure a) = 0) :
    ∀ᵐ w ∂mu, w = assignedPole a w := by
  letI : IsProbabilityMeasure mu := h.probability
  have hform := sphericalWassersteinSq_antipodal a r mu h
  have hint : (∫ w, assignedCost a w ∂mu) = 0 := by linarith
  have hae := (integral_eq_zero_iff_of_nonneg (assignedCost_nonneg a)
    (assignedCost_integrable a mu)).mp hint
  filter_upwards [hae] with w hw
  have hdist : sphericalDistance w (assignedPole a w) = 0 := by
    change (sphericalDistance w (assignedPole a w))^2/2 = 0 at hw
    nlinarith [sphericalDistance_nonneg w (assignedPole a w)]
  exact (sphericalDistance_eq_zero_iff w (assignedPole a w)).mp hdist

theorem zeroTransport_eq_antipodal {d : Nat} (a : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (h : TwoCapClass a r mu)
    (hz : sphericalWassersteinSq mu (antipodalMeasure a) = 0) :
    mu = antipodalMeasure a := by
  have hae := zeroTransport_ae_assigned a r mu h hz
  calc
    mu = mu.map (fun w => w) := (Measure.map_id').symm
    _ = mu.map (assignedPole a) := Measure.map_congr hae
    _ = antipodalMeasure a := assignedPole_pushforward a r mu h

/-- A common short-arc interval for all initial points, including v(w)=0. -/
theorem eventually_uniform_short_tangent {d : Nat} (v : UnitSphere d → Weight d)
    (hc : Continuous v) :
    ∀ᶠ t in 𝓝 (0 : Real), ∀ w, norm (t • v w) < Real.pi := by
  have h : ∀ᶠ t in 𝓝 (0 : Real), ∀ w ∈ (Set.univ : Set (UnitSphere d)),
      norm (t • v w) < Real.pi := by
    apply isCompact_univ.eventually_forall_of_forall_eventually
    intro w hw
    have hn : Continuous (fun z : Real × UnitSphere d => norm (z.1 • v z.2)) := by fun_prop
    exact hn.continuousAt.eventually (gt_mem_nhds (by simpa using Real.pi_pos))
  exact h.mono (fun t ht w => ht w (Set.mem_univ w))

/-- Source Z(t)=t^2*energy for a zero-cost marginal, not just an asymptotic. -/
theorem marginalTransport_zero_quadratic {d : Nat} (a : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (h : TwoCapClass a r mu)
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (hz : sphericalWassersteinSq mu (antipodalMeasure a) = 0) :
    ∀ᶠ t in 𝓝 (0 : Real), marginalExpTransportSq a mu v hv t =
      t^2*(∫ w, (norm (v w))^2 ∂mu) := by
  letI : IsProbabilityMeasure mu := h.probability
  have hi : Integrable (fun w => (norm (v w))^2) mu := sphere_integrable mu _ (hc.norm.pow 2)
  have hae := zeroTransport_ae_assigned a r mu h hz
  obtain ⟨U,hU,h0,hdata⟩ := frozenPole_integral_jets a r mu h v hv hc
  filter_upwards [hU.mem_nhds h0, eventually_uniform_short_tangent v hc] with t ht hshort
  rw [(hdata t ht).2.2.2.2.2]
  have hint : integral mu (frozenPoleCost a v hv t) =
      ∫ w, t^2*(norm (v w))^2/2 ∂mu := by
    apply integral_congr_ae
    filter_upwards [hae] with w hw
    change poleCost (assignedPole a w) (geodesicPoint w (v w) (hv w) t) = _
    rw [← hw]
    exact poleCost_along_pole w (v w) (hv w) (hshort w)
  rw [hint,integral_div,integral_const_mul]
  ring

theorem variationTransport_initial_nonneg {d : Nat} (P : SphericalVariation d) :
    0 ≤ variationTransport P 0 := by
  letI : IsProbabilityMeasure (P.measure 0) := (P.cap 0).probability
  letI : IsProbabilityMeasure (P.measure 1) := (P.cap 1).probability
  rw [variationTransport_zero,productAntipodalTransportSq]
  exact add_nonneg (sphericalWassersteinSq_nonneg _ _) (sphericalWassersteinSq_nonneg _ _)

/-- Neither factor can hide a positive transport cost through cancellation. -/
theorem zeroVariation_marginals {d : Nat} (P : SphericalVariation d)
    (hz : variationTransport P 0 = 0) :
    ∀ i : Fin 2, sphericalWassersteinSq (P.measure i) (antipodalMeasure P.pole) = 0 := by
  letI : IsProbabilityMeasure (P.measure 0) := (P.cap 0).probability
  letI : IsProbabilityMeasure (P.measure 1) := (P.cap 1).probability
  have h0 := sphericalWassersteinSq_nonneg (P.measure 0) (antipodalMeasure P.pole)
  have h1 := sphericalWassersteinSq_nonneg (P.measure 1) (antipodalMeasure P.pole)
  rw [variationTransport_zero,productAntipodalTransportSq] at hz
  intro i
  fin_cases i
  · change sphericalWassersteinSq (P.measure 0) (antipodalMeasure P.pole) = 0
    linarith
  · change sphericalWassersteinSq (P.measure 1) (antipodalMeasure P.pole) = 0
    linarith

theorem zeroVariation_original_laws {d : Nat} (P : SphericalVariation d)
    (hz : variationTransport P 0 = 0) : ∀ i, P.measure i = antipodalMeasure P.pole := by
  intro i
  exact zeroTransport_eq_antipodal P.pole P.radius (P.measure i) (P.cap i)
    (zeroVariation_marginals P hz i)

theorem variationTransport_zero_quadratic {d : Nat} (P : SphericalVariation d)
    (hz : variationTransport P 0 = 0) :
    ∀ᶠ t in 𝓝 (0 : Real), variationTransport P t = t^2*variationEnergy P := by
  have h0 := marginalTransport_zero_quadratic P.pole P.radius (P.measure 0) (P.cap 0)
    (P.velocity 0) (P.tangent 0) (P.continuous_velocity 0) (zeroVariation_marginals P hz 0)
  have h1 := marginalTransport_zero_quadratic P.pole P.radius (P.measure 1) (P.cap 1)
    (P.velocity 1) (P.tangent 1) (P.continuous_velocity 1) (zeroVariation_marginals P hz 1)
  filter_upwards [h0,h1] with t ht0 ht1
  rw [variationTransport_marginals,ht0,ht1,variationEnergy,Fin.sum_univ_two]
  ring

/-- Real powers retain arbitrary real p>2, and both signs of t. -/
theorem square_rpow_half (t p : Real) : (t^2)^(p/2) = |t|^p := by
  rw [← sq_abs t, ← Real.rpow_natCast_mul (abs_nonneg t)]
  congr 1
  norm_num
  ring

/-- Exact source central calculation, with the ORIGINAL product tangent energy. -/
theorem variationRegularizer_zero_formula {d : Nat} (P : SphericalVariation d)
    (lambda p : Real) (hz : variationTransport P 0 = 0) :
    variationRegularizer P lambda p =ᶠ[𝓝 (0 : Real)]
      (fun t => (lambda/p*(variationEnergy P)^(p/2))*|t|^p) := by
  filter_upwards [variationTransport_zero_quadratic P hz] with t ht
  rw [variationRegularizer,ht,Real.mul_rpow (sq_nonneg t) (variationEnergy_nonneg P),square_rpow_half]
  ring

/-- Elementary real analysis used at the target. It never differentiates
|t|^(p-2) at zero when 2<p<3; only its continuity is needed. -/
theorem absPower_second_zero (c p : Real) (hp : 2 < p) :
    HasDerivAt (fun t : Real => c*|t|^p) 0 0 ∧
    HasDerivAt (deriv (fun t : Real => c*|t|^p)) 0 0 := by
  have hp1 : 1 < p := by linarith
  have hp2 : 0 < p-2 := by linarith
  have hd (t : Real) := (hasDerivAt_abs_rpow t hp1).const_mul c
  have he : deriv (fun t : Real => c*|t|^p) =
      (fun t => c*p*|t|^(p-2)*t) := by
    funext t
    rw [(hd t).deriv]
    ring
  refine ⟨?_,?_⟩
  · simpa using hd 0
  · rw [he,hasDerivAt_iff_tendsto_slope_zero]
    have hc : ContinuousAt (fun t : Real => c*p*|t|^(p-2)) 0 :=
      continuousAt_const.mul (continuousAt_id.abs.rpow_const (Or.inr hp2.le))
    have hl : Tendsto (fun t : Real => c*p*|t|^(p-2)) (𝓝 (0 : Real)) (𝓝 0) := by
      simpa only [abs_zero,Real.zero_rpow hp2.ne',mul_zero] using hc.tendsto
    apply (hl.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htn : t ≠ 0 := by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using ht
    simp only [zero_add,abs_zero,mul_zero,sub_zero,smul_eq_mul]
    field_simp [htn]

/-- The actual regularizer, not merely its ray majorant, has zero first and
ordinary second EXP derivatives at zero target transport. -/
theorem metricRegularizer_zero_variations {d : Nat} (P : SphericalVariation d)
    (lambda p : Real) (hp : 2 < p) (hz : variationTransport P 0 = 0) :
    HasDerivAt (variationRegularizer P lambda p) 0 0 ∧
    HasDerivAt (deriv (variationRegularizer P lambda p)) 0 0 := by
  have he := variationRegularizer_zero_formula P lambda p hz
  have hd := absPower_second_zero (lambda/p*(variationEnergy P)^(p/2)) p hp
  exact ⟨hd.1.congr_of_eventuallyEq he,
    hd.2.congr_of_eventuallyEq he.deriv⟩

/-- Complete case distinction for the actual model; no pole/zero case is lost. -/
theorem metricRegularizer_all_cases {d : Nat} (P : SphericalVariation d)
    (lambda p : Real) (hlambda : 0 < lambda) (hp : 2 < p) :
    (variationTransport P 0 = 0 →
      HasDerivAt (variationRegularizer P lambda p) 0 0 ∧
      HasDerivAt (deriv (variationRegularizer P lambda p)) 0 0) ∧
    (0 < variationTransport P 0 →
      HasDerivAt (variationRegularizer P lambda p)
        (lambda*(variationTransport P 0)^(p/2-1)*variationFirst P) 0 ∧
      HasDerivAt (deriv (variationRegularizer P lambda p))
        (lambda*(variationTransport P 0)^(p/2-1)*variationSecond P +
          lambda*(p-2)*(variationTransport P 0)^(p/2-2)*(variationFirst P)^2) 0) ∧
    0 ≤ variationTransport P 0 := by
  exact ⟨metricRegularizer_zero_variations P lambda p hp,
    metricRegularizer_positive_variations P lambda p hlambda hp,
    variationTransport_initial_nonneg P⟩

end PaperFormalization.MatrixFactorization
