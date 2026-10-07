import PaperFormalization.MatrixFactorization.TransverseCenterField

/-! # MF07: the actual transverse center variation and its energy

The original transport vanishes at the initial antipodal law. The product
energy is norm(s)^2/2, reflecting both atom masses and the field's one-half.
Consequently, the regularizer has the exact local source power law.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

theorem antipodal_target_transport_zero {d : Nat} (a : UnitSphere d) {r : Real}
    (hr : 0 < r) (hrpi : r < Real.pi/2) :
    sphericalWassersteinSq (antipodalMeasure a) (antipodalMeasure a) = 0 := by
  rw [sphericalWassersteinSq_antipodal a r _ (antipodalMeasure_twoCap a hr hrpi)]
  have hi : (∫ w, assignedCost a w ∂antipodalMeasure a) = 0 := by
    have he : (fun w => assignedCost a w) =ᵐ[antipodalMeasure a] (fun _ => (0 : Real)) := by
      filter_upwards [antipodalMeasure_ae_poles a] with w hw
      rcases hw with hw | hw
      · rw [hw]
        simp [assignedCost, assignedPole_positive a r hrpi (sphericalCap_pole_mem a r hr)]
      · rw [hw]
        simp only [assignedCost, assignedPole_negative a r hrpi (sphericalCap_pole_mem (reflect a) r hr),
          sphericalDistance_self, zero_pow (by norm_num : 2 ≠ 0), zero_div]
    rw [integral_congr_ae he, integral_zero]
  rw [hi, mul_zero]

theorem transverseCenterVariation_transport_zero {d : Nat} (a : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (s : Weight d) :
    variationTransport (transverseCenterVariation a r hr hrpi s) 0 = 0 := by
  rw [variationTransport_zero]
  change sphericalWassersteinSq (antipodalMeasure a) (antipodalMeasure a) +
    sphericalWassersteinSq (antipodalMeasure a) (antipodalMeasure a) = 0
  rw [antipodal_target_transport_zero a hr hrpi, add_zero]

theorem transverseCenterVariation_energy {d : Nat} (a : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (s : Weight d) (hs : inner Real a.val s = 0) :
    variationEnergy (transverseCenterVariation a r hr hrpi s) = norm s^2/2 := by
  have hc : Continuous (fun w : UnitSphere d => norm (transverseHalfField s w)^2) :=
    (transverseHalfField_continuous s).norm.pow 2
  have hi := integral_antipodalMeasure a _ hc
  have ha := transverseHalfField_at_pole a s hs
  simp only [ha.1, ha.2, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : Real) ≤ 1/2),
    smul_eq_mul] at hi
  simp only [variationEnergy, transverseCenterVariation, Fin.sum_univ_two, hi]
  ring

theorem transverseCenterVariation_same_density {d : Nat} (a : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (s : Weight d) (t : Real) :
    let P := transverseCenterVariation a r hr hrpi s
    (P.measure 1).map (sphericalExpFamily (P.velocity 1) (P.tangent 1) t) =
      (P.measure 0).map (sphericalExpFamily (P.velocity 0) (P.tangent 0) t) := rfl

/-- The constructed path retains the original closed-support and half-mass cap
conditions throughout one common neighborhood of zero. -/
theorem transverseCenterVariation_caps_near {d : Nat} (a : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (s : Weight d) :
    let P := transverseCenterVariation a r hr hrpi s
    ∀ᶠ t in 𝓝 (0 : Real), ∀ i : Fin 2,
      TwoCapClass a r ((P.measure i).map (sphericalExpFamily (P.velocity i) (P.tangent i) t)) := by
  have ht := fixed_assignment_sphericalExp a r (antipodalMeasure a) (antipodalMeasure_twoCap a hr hrpi)
    (transverseHalfField s) (transverseHalfField_tangent s) (transverseHalfField_continuous s)
  filter_upwards [ht] with t ht i
  exact ht.1

theorem transverseCenterVariation_transport_quadratic {d : Nat} (a : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (s : Weight d) (hs : inner Real a.val s = 0) :
    ∀ᶠ t in 𝓝 (0 : Real), variationTransport (transverseCenterVariation a r hr hrpi s) t =
      t^2*(norm s^2/2) := by
  have ht := variationTransport_zero_quadratic (transverseCenterVariation a r hr hrpi s)
    (transverseCenterVariation_transport_zero a r hr hrpi s)
  simpa only [transverseCenterVariation_energy a r hr hrpi s hs] using ht

theorem transverseCenterVariation_regularizer_formula {d : Nat} (a : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (s : Weight d) (hs : inner Real a.val s = 0)
    (lambda p : Real) :
    variationRegularizer (transverseCenterVariation a r hr hrpi s) lambda p =ᶠ[𝓝 (0 : Real)]
      (fun t => (lambda/p*(norm s^2/2)^(p/2))*|t|^p) := by
  have ht := variationRegularizer_zero_formula (transverseCenterVariation a r hr hrpi s) lambda p
    (transverseCenterVariation_transport_zero a r hr hrpi s)
  simpa only [transverseCenterVariation_energy a r hr hrpi s hs] using ht

end PaperFormalization.MatrixFactorization
