import PaperFormalization.MatrixFactorization.SphericalDistance

/-! # MF02c: genuine spherical transport plans and their cost infimum

A plan is ANY measure with the prescribed two marginals, not necessarily a
map-induced plan. Probability of the plan is derived from its first marginal.
The squared Wasserstein cost is the real infimum of ALL such costs. Before
using that infimum for probability marginals we prove its nonempty, bounded
cost range. Bounded continuous angular cost supplies genuine integrability.
This does not install a new metric on the existing UnitSphere type.
-/
open MeasureTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

structure SphericalCoupling {d : Nat} (mu nu : Measure (UnitSphere d)) where
  measure : Measure (UnitSphere d × UnitSphere d)
  first_marginal : measure.map Prod.fst = mu
  second_marginal : measure.map Prod.snd = nu

instance sphericalCoupling_probability {d : Nat} {mu nu : Measure (UnitSphere d)}
    [IsProbabilityMeasure mu] (gamma : SphericalCoupling mu nu) :
    IsProbabilityMeasure gamma.measure where
  measure_univ := by
    have h := congrArg (fun m : Measure (UnitSphere d) => m Set.univ) gamma.first_marginal
    rw [Measure.map_apply measurable_fst MeasurableSet.univ] at h
    simpa using h

noncomputable def productSphericalCoupling {d : Nat}
    (mu nu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    SphericalCoupling mu nu where
  measure := mu.prod nu
  first_marginal := (measurePreserving_fst : MeasurePreserving Prod.fst (mu.prod nu) mu).map_eq
  second_marginal := (measurePreserving_snd : MeasurePreserving Prod.snd (mu.prod nu) nu).map_eq

/-- The usual graph construction; both marginal identities are proved. -/
noncomputable def graphSphericalCoupling {d : Nat} (mu : Measure (UnitSphere d))
    (f : UnitSphere d → UnitSphere d) (hf : Measurable f) : SphericalCoupling mu (mu.map f) where
  measure := mu.map (fun w => (w, f w))
  first_marginal := by
    have hg : Measurable (fun w : UnitSphere d => (w, f w)) := measurable_id.prodMk hf
    rw [Measure.map_map measurable_fst hg]
    simp only [Function.comp_def, Measure.map_id']
  second_marginal := by
    have hg : Measurable (fun w : UnitSphere d => (w, f w)) := measurable_id.prodMk hf
    rw [Measure.map_map measurable_snd hg]
    rfl

theorem spherePair_integrable {d : Nat} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    (mu : Measure (UnitSphere d × UnitSphere d)) [IsFiniteMeasure mu]
    (f : UnitSphere d × UnitSphere d → E) (hf : Continuous f) : Integrable f mu := by
  obtain ⟨C, hC⟩ := (isCompact_univ : IsCompact (Set.univ : Set (UnitSphere d × UnitSphere d))).exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun w => hC w (Set.mem_univ w)))

noncomputable def sphericalTransportCost {d : Nat} {mu nu : Measure (UnitSphere d)}
    (gamma : SphericalCoupling mu nu) : Real :=
  ∫ z, (sphericalDistance z.1 z.2)^2 ∂gamma.measure

theorem sphericalTransportCost_integrable {d : Nat} {mu nu : Measure (UnitSphere d)}
    [IsProbabilityMeasure mu] (gamma : SphericalCoupling mu nu) :
    Integrable (fun z : UnitSphere d × UnitSphere d => (sphericalDistance z.1 z.2)^2) gamma.measure :=
  spherePair_integrable gamma.measure _ ((sphericalDistance_continuous d).pow 2)

theorem sphericalTransportCost_nonneg {d : Nat} {mu nu : Measure (UnitSphere d)}
    [IsProbabilityMeasure mu] (gamma : SphericalCoupling mu nu) :
    0 ≤ sphericalTransportCost gamma := by
  have hint := sphericalTransportCost_integrable gamma
  exact integral_nonneg (fun z => sq_nonneg _)

theorem sphericalTransportCost_le_pi_sq {d : Nat} {mu nu : Measure (UnitSphere d)}
    [IsProbabilityMeasure mu] (gamma : SphericalCoupling mu nu) :
    sphericalTransportCost gamma ≤ Real.pi^2 := by
  calc
    _ ≤ ∫ _z : UnitSphere d × UnitSphere d, Real.pi^2 ∂gamma.measure := by
      apply integral_mono (sphericalTransportCost_integrable gamma) (integrable_const _)
      intro z
      exact pow_le_pow_left₀ (sphericalDistance_nonneg z.1 z.2)
        (sphericalDistance_le_pi z.1 z.2) 2
    _ = _ := by simp

/-- The graph formula is a pushforward integral identity, not the definition of cost. -/
theorem sphericalTransportCost_graph {d : Nat} (mu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] (f : UnitSphere d → UnitSphere d) (hf : Measurable f) :
    sphericalTransportCost (graphSphericalCoupling mu f hf) =
      ∫ w, (sphericalDistance w (f w))^2 ∂mu := by
  have hint := sphericalTransportCost_integrable (graphSphericalCoupling mu f hf)
  exact integral_map (measurable_id.prodMk hf).aemeasurable
    ((sphericalDistance_continuous d).pow 2).aestronglyMeasurable

noncomputable def sphericalTransportValues {d : Nat} (mu nu : Measure (UnitSphere d)) : Set Real :=
  Set.range (fun gamma : SphericalCoupling mu nu => sphericalTransportCost gamma)

theorem sphericalTransportValues_nonempty {d : Nat} (mu nu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    (sphericalTransportValues mu nu).Nonempty :=
  ⟨sphericalTransportCost (productSphericalCoupling mu nu), productSphericalCoupling mu nu, rfl⟩

theorem sphericalTransportValues_bddBelow {d : Nat} (mu nu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] : BddBelow (sphericalTransportValues mu nu) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨gamma, rfl⟩
  exact sphericalTransportCost_nonneg gamma

theorem sphericalTransportValues_bddAbove {d : Nat} (mu nu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] : BddAbove (sphericalTransportValues mu nu) := by
  refine ⟨Real.pi^2, ?_⟩
  rintro _ ⟨gamma, rfl⟩
  exact sphericalTransportCost_le_pi_sq gamma

/-- Source W_{2,S} squared: infimum over the full set of marginal-constrained plans.
Only probability-marginal uses below are certified to have nonempty finite costs. -/
noncomputable def sphericalWassersteinSq {d : Nat} (mu nu : Measure (UnitSphere d)) : Real :=
  sInf (sphericalTransportValues mu nu)

theorem sphericalWassersteinSq_nonneg {d : Nat} (mu nu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    0 ≤ sphericalWassersteinSq mu nu := by
  apply le_csInf (sphericalTransportValues_nonempty mu nu)
  rintro _ ⟨gamma, rfl⟩
  exact sphericalTransportCost_nonneg gamma

theorem sphericalWassersteinSq_le_cost {d : Nat} {mu nu : Measure (UnitSphere d)}
    [IsProbabilityMeasure mu] (gamma : SphericalCoupling mu nu) :
    sphericalWassersteinSq mu nu ≤ sphericalTransportCost gamma :=
  csInf_le (sphericalTransportValues_bddBelow mu nu) ⟨gamma, rfl⟩

/-- A lower bound for every feasible plan and one attaining plan identify the infimum. -/
theorem sphericalWassersteinSq_eq_of_attains {d : Nat} {mu nu : Measure (UnitSphere d)}
    [IsProbabilityMeasure mu] (gamma : SphericalCoupling mu nu) (v : Real)
    (hcost : sphericalTransportCost gamma = v)
    (hlower : ∀ plan : SphericalCoupling mu nu, v ≤ sphericalTransportCost plan) :
    sphericalWassersteinSq mu nu = v := by
  apply le_antisymm
  · exact (sphericalWassersteinSq_le_cost gamma).trans_eq hcost
  · apply le_csInf (show (sphericalTransportValues mu nu).Nonempty from
      ⟨sphericalTransportCost gamma, gamma, rfl⟩)
    rintro _ ⟨plan, rfl⟩
    exact hlower plan

end PaperFormalization.MatrixFactorization
