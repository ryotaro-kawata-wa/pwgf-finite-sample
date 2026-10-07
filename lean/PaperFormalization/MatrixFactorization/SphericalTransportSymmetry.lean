import PaperFormalization.MatrixFactorization.SphericalContraction

/-! # Reflection of every spherical transport plan and the assigned gradient

The isometry statement is derived by pushing forward arbitrary admissible
couplings and applying the involution twice. Gradient reflection is restricted
to the separated caps, where the assigned pole genuinely commutes with reflection.
-/
open MeasureTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def reflectedSphericalCoupling {d : Nat} {mu nu : Measure (UnitSphere d)}
    (gamma : SphericalCoupling mu nu) :
    SphericalCoupling (reflectedMeasure mu) (reflectedMeasure nu) where
  measure := gamma.measure.map (fun z : UnitSphere d × UnitSphere d => (reflect z.1,reflect z.2))
  first_marginal := by
    have hm : Measurable (fun z : UnitSphere d × UnitSphere d => (reflect z.1,reflect z.2)) :=
      ((reflect_measurable d).comp measurable_fst).prodMk ((reflect_measurable d).comp measurable_snd)
    rw [Measure.map_map measurable_fst hm]
    change gamma.measure.map (reflect ∘ Prod.fst) = _
    rw [← Measure.map_map (reflect_measurable d) measurable_fst, gamma.first_marginal]
    rfl
  second_marginal := by
    have hm : Measurable (fun z : UnitSphere d × UnitSphere d => (reflect z.1,reflect z.2)) :=
      ((reflect_measurable d).comp measurable_fst).prodMk ((reflect_measurable d).comp measurable_snd)
    rw [Measure.map_map measurable_snd hm]
    change gamma.measure.map (reflect ∘ Prod.snd) = _
    rw [← Measure.map_map (reflect_measurable d) measurable_snd, gamma.second_marginal]
    rfl

theorem sphericalTransportCost_reflected {d : Nat} {mu nu : Measure (UnitSphere d)}
    (gamma : SphericalCoupling mu nu) :
    sphericalTransportCost (reflectedSphericalCoupling gamma) = sphericalTransportCost gamma := by
  have hm : Measurable (fun z : UnitSphere d × UnitSphere d => (reflect z.1,reflect z.2)) :=
    ((reflect_measurable d).comp measurable_fst).prodMk ((reflect_measurable d).comp measurable_snd)
  have hc : Continuous (fun z : UnitSphere d × UnitSphere d => sphericalDistance z.1 z.2 ^ 2) :=
    (sphericalDistance_continuous d).pow 2
  change (∫ z : UnitSphere d × UnitSphere d, sphericalDistance z.1 z.2 ^ 2
    ∂gamma.measure.map (fun z => (reflect z.1,reflect z.2))) = _
  rw [integral_map hm.aemeasurable hc.aestronglyMeasurable]
  simp only [sphericalDistance_reflect_reflect, sphericalTransportCost]

/-- Reflection cannot increase the infimum over all feasible plans. -/
theorem sphericalWassersteinSq_reflected_le {d : Nat} (mu nu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    sphericalWassersteinSq (reflectedMeasure mu) (reflectedMeasure nu) ≤
      sphericalWassersteinSq mu nu := by
  apply le_csInf (sphericalTransportValues_nonempty mu nu)
  rintro _ ⟨gamma,rfl⟩
  exact (sphericalWassersteinSq_le_cost (reflectedSphericalCoupling gamma)).trans_eq
    (sphericalTransportCost_reflected gamma)

/-- The reverse bound uses the actual measure involution, so equality is exact. -/
theorem sphericalWassersteinSq_reflected {d : Nat} (mu nu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    sphericalWassersteinSq (reflectedMeasure mu) (reflectedMeasure nu) =
      sphericalWassersteinSq mu nu := by
  apply le_antisymm (sphericalWassersteinSq_reflected_le mu nu)
  simpa only [reflectedMeasure_involutive] using
    sphericalWassersteinSq_reflected_le (reflectedMeasure mu) (reflectedMeasure nu)

theorem sphericalWassersteinSq_reflected_antipodal {d : Nat} (pole : UnitSphere d)
    (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] :
    sphericalWassersteinSq (reflectedMeasure mu) (antipodalMeasure pole) =
      sphericalWassersteinSq mu (antipodalMeasure pole) := by
  simpa only [reflectedMeasure_antipodal] using sphericalWassersteinSq_reflected mu (antipodalMeasure pole)

/-- Reflection followed by exchange leaves the true product target cost unchanged. -/
theorem productAntipodalTransportSq_reflection_exchange {d : Nat} (pole : UnitSphere d)
    (mu1 mu2 : Measure (UnitSphere d)) [IsProbabilityMeasure mu1] [IsProbabilityMeasure mu2] :
    productAntipodalTransportSq pole (reflectedMeasure mu2) (reflectedMeasure mu1) =
      productAntipodalTransportSq pole mu1 mu2 := by
  simp only [productAntipodalTransportSq, sphericalWassersteinSq_reflected_antipodal, add_comm]

/-- Both the source point and the cost pole are reflected. -/
theorem poleGradient_reflected {d : Nat} (y w : UnitSphere d) :
    poleGradient (reflect y) (reflect w) = -poleGradient y w := by
  simp only [poleGradient, sphericalDistance_reflect_reflect, reflect_val, smul_neg,
    sub_neg_eq_add, neg_sub, smul_add, smul_sub]
  module

/-- No false equivariance is asserted for the tie-breaking assignment at the equator. -/
theorem assignedGradient_reflected_on_caps {d : Nat} (pole : UnitSphere d) (r : Real)
    (hr : r < Real.pi/2) {w : UnitSphere d}
    (hw : w ∈ sphericalCap pole r ∪ sphericalCap (reflect pole) r) :
    assignedGradient pole (reflect w) = -assignedGradient pole w := by
  rw [assignedGradient, assignedPole_reflect_on_caps pole r hr hw, poleGradient_reflected]
  rfl

end PaperFormalization.MatrixFactorization
