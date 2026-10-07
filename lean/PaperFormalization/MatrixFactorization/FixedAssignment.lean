import PaperFormalization.MatrixFactorization.CapAssignment
import PaperFormalization.MatrixFactorization.SphericalTransport

/-! # MF02d: source lemma-fixed-assignment

The proof proceeds from the full marginal-constrained transport problem:
1. the assigned map has the correct target law;
2. every feasible plan is carried by the two target poles;
3. pointwise nearest-pole comparison gives a lower bound for every plan;
4. the graph plan attains it, identifying the real infimum.

The half-cost c_star, squared Wasserstein cost and two-marginal sum keep their
source normalization. No conditional independence or density assumption occurs.
-/
open MeasureTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def assignedPoleCoupling {d : Nat} (a : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (h : TwoCapClass a r mu) :
    SphericalCoupling mu (antipodalMeasure a) where
  measure := mu.map (fun w => (w, assignedPole a w))
  first_marginal := (graphSphericalCoupling mu (assignedPole a) (assignedPole_measurable a)).first_marginal
  second_marginal :=
    (graphSphericalCoupling mu (assignedPole a) (assignedPole_measurable a)).second_marginal.trans
      (assignedPole_pushforward a r mu h)

theorem assignedPoleCoupling_cost {d : Nat} (a : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (h : TwoCapClass a r mu) :
    sphericalTransportCost (assignedPoleCoupling a r mu h) = 2 * ∫ w, assignedCost a w ∂mu := by
  letI : IsProbabilityMeasure mu := h.probability
  change sphericalTransportCost
    (graphSphericalCoupling mu (assignedPole a) (assignedPole_measurable a)) = _
  rw [sphericalTransportCost_graph]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun w => by dsimp [assignedCost]; ring)

/-- Any feasible plan has its second coordinate at one of the two target poles. -/
theorem sphericalCoupling_ae_target_poles {d : Nat} {mu : Measure (UnitSphere d)}
    (a : UnitSphere d) (gamma : SphericalCoupling mu (antipodalMeasure a)) :
    ∀ᵐ z ∂gamma.measure, z.2 = a ∨ z.2 = reflect a := by
  have hp : MeasurePreserving Prod.snd gamma.measure (antipodalMeasure a) :=
    ⟨measurable_snd, gamma.second_marginal⟩
  exact hp.quasiMeasurePreserving.ae (antipodalMeasure_ae_poles a)

/-- Universal lower bound. Plans need not be induced by maps, nor absolutely continuous. -/
theorem assignedPole_lower_bound {d : Nat} (a : UnitSphere d)
    (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    (gamma : SphericalCoupling mu (antipodalMeasure a)) :
    2 * ∫ w, assignedCost a w ∂mu ≤ sphericalTransportCost gamma := by
  have hhalf := assignedCost_integrable a mu
  have hleft : Integrable (fun z : UnitSphere d × UnitSphere d => 2 * assignedCost a z.1)
      gamma.measure :=
    spherePair_integrable gamma.measure _
      (continuous_const.mul ((assignedCost_continuous a).comp continuous_fst))
  have hright := sphericalTransportCost_integrable gamma
  calc
    2 * ∫ w, assignedCost a w ∂mu =
        ∫ w, 2 * assignedCost a w ∂gamma.measure.map Prod.fst := by
      rw [gamma.first_marginal, integral_const_mul]
    _ = ∫ z : UnitSphere d × UnitSphere d, 2 * assignedCost a z.1 ∂gamma.measure :=
      integral_map measurable_fst.aemeasurable
        (continuous_const.mul (assignedCost_continuous a)).aestronglyMeasurable
    _ ≤ sphericalTransportCost gamma := by
      apply integral_mono_ae hleft hright
      filter_upwards [sphericalCoupling_ae_target_poles a gamma] with z hz
      exact assignedCost_le_pole_cost a z.1 z.2 hz

/-- The actual graph plan minimizes the full transport objective. -/
theorem assignedPoleCoupling_optimal {d : Nat} (a : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (h : TwoCapClass a r mu)
    (gamma : SphericalCoupling mu (antipodalMeasure a)) :
    sphericalTransportCost (assignedPoleCoupling a r mu h) ≤ sphericalTransportCost gamma := by
  letI : IsProbabilityMeasure mu := h.probability
  rw [assignedPoleCoupling_cost]
  exact assignedPole_lower_bound a mu gamma

theorem sphericalWassersteinSq_antipodal {d : Nat} (a : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (h : TwoCapClass a r mu) :
    sphericalWassersteinSq mu (antipodalMeasure a) = 2 * ∫ w, assignedCost a w ∂mu := by
  letI : IsProbabilityMeasure mu := h.probability
  exact sphericalWassersteinSq_eq_of_attains (assignedPoleCoupling a r mu h)
    (2 * ∫ w, assignedCost a w ∂mu) (assignedPoleCoupling_cost a r mu h)
    (assignedPole_lower_bound a mu)

/-- The two displayed equalities of lemma-fixed-assignment, with genuine integrability. -/
theorem fixed_assignment_formula {d : Nat} (a : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (h : TwoCapClass a r mu) :
    Integrable (fun w => (sphericalDistance w (assignedPole a w))^2) mu ∧
    sphericalWassersteinSq mu (antipodalMeasure a) =
      (∫ w, (sphericalDistance w (assignedPole a w))^2 ∂mu) ∧
    (∫ w, (sphericalDistance w (assignedPole a w))^2 ∂mu) =
      2 * ∫ w, assignedCost a w ∂mu := by
  letI : IsProbabilityMeasure mu := h.probability
  have he : (fun w => (sphericalDistance w (assignedPole a w))^2) =
      (fun w => 2 * assignedCost a w) := by
    funext w
    dsimp [assignedCost]
    ring
  have hi : Integrable (fun w => (sphericalDistance w (assignedPole a w))^2) mu := by
    rw [he]
    exact (assignedCost_integrable a mu).const_mul 2
  have hint : (∫ w, (sphericalDistance w (assignedPole a w))^2 ∂mu) =
      2 * ∫ w, assignedCost a w ∂mu := by
    rw [he, integral_const_mul]
  exact ⟨hi, (sphericalWassersteinSq_antipodal a r mu h).trans hint.symm, hint⟩

theorem sphericalWassersteinSq_cap_bound {d : Nat} (a : UnitSphere d) (r : Real)
    (mu : Measure (UnitSphere d)) (h : TwoCapClass a r mu) :
    0 ≤ sphericalWassersteinSq mu (antipodalMeasure a) ∧
    sphericalWassersteinSq mu (antipodalMeasure a) ≤ r^2 := by
  letI : IsProbabilityMeasure mu := h.probability
  refine ⟨sphericalWassersteinSq_nonneg _ _, ?_⟩
  rw [sphericalWassersteinSq_antipodal a r mu h, ← integral_const_mul]
  calc
    _ ≤ ∫ _w : UnitSphere d, r^2 ∂mu :=
      integral_mono_ae ((assignedCost_integrable a mu).const_mul 2)
        (integrable_const _) h.assignedCost_bound
    _ = _ := by simp

/-- The center/diagonal boundary does not use a limiting positive-radius argument. -/
theorem sphericalWassersteinSq_self {d : Nat} (mu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] : sphericalWassersteinSq mu mu = 0 := by
  have hg : Measurable (fun w : UnitSphere d => (w, w)) :=
    measurable_id.prodMk measurable_id
  have hc : Continuous (fun z : UnitSphere d × UnitSphere d =>
      (sphericalDistance z.1 z.2)^2) := (sphericalDistance_continuous d).pow 2
  let gamma : SphericalCoupling mu mu := {
    measure := mu.map (fun w => (w, w))
    first_marginal := by
      rw [Measure.map_map measurable_fst hg]
      simp only [Function.comp_def, Measure.map_id']
    second_marginal := by
      rw [Measure.map_map measurable_snd hg]
      simp only [Function.comp_def, Measure.map_id'] }
  have hint := sphericalTransportCost_integrable gamma
  apply sphericalWassersteinSq_eq_of_attains gamma 0
  · change (∫ z : UnitSphere d × UnitSphere d, (sphericalDistance z.1 z.2)^2
      ∂mu.map (fun w => (w, w))) = 0
    rw [integral_map hg.aemeasurable hc.aestronglyMeasurable]
    simp
  · exact sphericalTransportCost_nonneg

/-- Source Z_pm is the SUM of the two squared marginal transport costs. -/
noncomputable def productAntipodalTransportSq {d : Nat} (a : UnitSphere d)
    (mu1 mu2 : Measure (UnitSphere d)) : Real :=
  sphericalWassersteinSq mu1 (antipodalMeasure a) +
    sphericalWassersteinSq mu2 (antipodalMeasure a)

theorem productAntipodalTransportSq_formula {d : Nat} (a : UnitSphere d) (r : Real)
    (mu1 mu2 : Measure (UnitSphere d)) (h1 : TwoCapClass a r mu1) (h2 : TwoCapClass a r mu2) :
    productAntipodalTransportSq a mu1 mu2 =
      2 * ((∫ w, assignedCost a w ∂mu1) + ∫ w, assignedCost a w ∂mu2) := by
  rw [productAntipodalTransportSq, sphericalWassersteinSq_antipodal a r mu1 h1,
    sphericalWassersteinSq_antipodal a r mu2 h2]
  ring

end PaperFormalization.MatrixFactorization
