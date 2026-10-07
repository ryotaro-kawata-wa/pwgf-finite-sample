import PaperFormalization.MatrixFactorization.ActiveMomentRetractVariation
import PaperFormalization.MatrixFactorization.SphericalActiveMomentBounds

/-! # MF35: actual symmetric active derivatives agree at the retraction origin

The equality uses both differentiation exchanges for each original measure.
It therefore concerns actual Hilbert-valued derivatives, not assumed jets.
-/
open MeasureTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000

theorem rawActiveRetractFirst_zero_eq_exp {d : Nat} (O : Finset Nat)
    (mu : Measure (UnitSphere d)) (v : UnitSphere d → Weight d) :
    rawActiveRetractFirst O mu v 0 = rawActiveFirst O mu v 0 := by
  unfold rawActiveRetractFirst rawActiveFirst
  congr 1
  apply PiLp.ext
  intro n
  exact rawMomentRetract_first_jet_eq_exp mu v

theorem rawActiveRetractSecond_zero_eq_exp {d : Nat} (O : Finset Nat)
    (mu : Measure (UnitSphere d)) (v : UnitSphere d → Weight d) :
    rawActiveRetractSecond O mu v 0 = rawActiveSecond O mu v 0 := by
  unfold rawActiveRetractSecond rawActiveSecond
  congr 1
  apply PiLp.ext
  intro n
  exact rawMomentRetract_second_jet_eq_exp mu v

noncomputable def activeMomentMapAlongRetract {d : Nat} (O : Finset Nat)
    (mu : Fin 2 → Measure (UnitSphere d)) [∀ i, IsFiniteMeasure (mu i)]
    (v : Fin 2 → UnitSphere d → Weight d) (hv : ∀ i w, inner Real w.val (v i w) = 0)
    (t : Real) : ActiveMomentCoordinates d O :=
  activeCoordinates (rawActiveAlongRetract O (mu 0) (v 0) (hv 0) t)
    (rawActiveAlongRetract O (mu 1) (v 1) (hv 1) t)

noncomputable def activeMomentRetractFirst {d : Nat} (O : Finset Nat)
    (mu : Fin 2 → Measure (UnitSphere d)) (v : Fin 2 → UnitSphere d → Weight d)
    (t : Real) : ActiveMomentCoordinates d O :=
  activeCoordinates (rawActiveRetractFirst O (mu 0) (v 0) t) (rawActiveRetractFirst O (mu 1) (v 1) t)

noncomputable def activeMomentRetractSecond {d : Nat} (O : Finset Nat)
    (mu : Fin 2 → Measure (UnitSphere d)) (v : Fin 2 → UnitSphere d → Weight d)
    (t : Real) : ActiveMomentCoordinates d O :=
  activeCoordinates (rawActiveRetractSecond O (mu 0) (v 0) t) (rawActiveRetractSecond O (mu 1) (v 1) t)

/-- This is the original source finite moment map of the normalized pushed laws. -/
theorem activeMomentMapAlongRetract_eq {d : Nat} (O : Finset Nat)
    (mu : Fin 2 → Measure (UnitSphere d)) [∀ i, IsFiniteMeasure (mu i)]
    (v : Fin 2 → UnitSphere d → Weight d) (hv : ∀ i w, inner Real w.val (v i w) = 0)
    (t : Real) :
    activeMomentMapAlongRetract O mu v hv t = activeMomentMap O
      ((mu 0).map (sphericalRetractFamily (v 0) (hv 0) t))
      ((mu 1).map (sphericalRetractFamily (v 1) (hv 1) t)) := rfl

theorem activeMomentMapAlongRetract_variations {d : Nat} (O : Finset Nat)
    (mu : Fin 2 → Measure (UnitSphere d)) [∀ i, IsFiniteMeasure (mu i)]
    (v : Fin 2 → UnitSphere d → Weight d) (hv : ∀ i w, inner Real w.val (v i w) = 0)
    (hc : ∀ i, Continuous (v i)) (t : Real) :
    HasDerivAt (activeMomentMapAlongRetract O mu v hv) (activeMomentRetractFirst O mu v t) t ∧
    HasDerivAt (activeMomentRetractFirst O mu v) (activeMomentRetractSecond O mu v t) t := by
  constructor
  · exact activeCoordinates_hasDerivAt
      (rawActiveAlongRetract_hasDerivAt O (mu 0) (v 0) (hv 0) (hc 0) t)
      (rawActiveAlongRetract_hasDerivAt O (mu 1) (v 1) (hv 1) (hc 1) t)
  · exact activeCoordinates_hasDerivAt
      (rawActiveRetractFirst_hasDerivAt O (mu 0) (v 0) (hv 0) (hc 0) t)
      (rawActiveRetractFirst_hasDerivAt O (mu 1) (v 1) (hv 1) (hc 1) t)

theorem activeMomentMapAlongRetract_second_derivative {d : Nat} (O : Finset Nat)
    (mu : Fin 2 → Measure (UnitSphere d)) [∀ i, IsFiniteMeasure (mu i)]
    (v : Fin 2 → UnitSphere d → Weight d) (hv : ∀ i w, inner Real w.val (v i w) = 0)
    (hc : ∀ i, Continuous (v i)) (t : Real) :
    HasDerivAt (deriv (activeMomentMapAlongRetract O mu v hv)) (activeMomentRetractSecond O mu v t) t := by
  letI : NormedSpace Real (ActiveMomentCoordinates d O) := PiLp.normedSpace 2 Real _
  have he : deriv (activeMomentMapAlongRetract O mu v hv) = activeMomentRetractFirst O mu v :=
    funext (fun s => (activeMomentMapAlongRetract_variations O mu v hv hc s).1.deriv)
  rw [he]
  exact (activeMomentMapAlongRetract_variations O mu v hv hc t).2

/-- Both actual active Hilbert derivatives agree at zero. -/
theorem activeMomentRetract_exp_initial_derivatives {d : Nat} (O : Finset Nat)
    (mu : Fin 2 → Measure (UnitSphere d)) [∀ i, IsFiniteMeasure (mu i)]
    (v : Fin 2 → UnitSphere d → Weight d) (hv : ∀ i w, inner Real w.val (v i w) = 0)
    (hc : ∀ i, Continuous (v i)) :
    deriv (activeMomentMapAlongRetract O mu v hv) 0 = deriv (activeMomentMapAlongExp O mu v hv) 0 ∧
    deriv (deriv (activeMomentMapAlongRetract O mu v hv)) 0 = deriv (deriv (activeMomentMapAlongExp O mu v hv)) 0 := by
  letI : NormedSpace Real (ActiveMomentCoordinates d O) := PiLp.normedSpace 2 Real _
  constructor
  · rw [(activeMomentMapAlongRetract_variations O mu v hv hc 0).1.deriv,
      (activeMomentMapAlongExp_variations O mu v hv hc 0).1.deriv]
    simp only [activeMomentRetractFirst, activeMomentMapFirst, rawActiveRetractFirst_zero_eq_exp]
  · rw [(activeMomentMapAlongRetract_second_derivative O mu v hv hc 0).deriv,
      (activeMomentMapAlongExp_second_derivative O mu v hv hc 0).deriv]
    simp only [activeMomentRetractSecond, activeMomentMapSecond, rawActiveRetractSecond_zero_eq_exp]

/-- The two printed source moment bounds now hold on the actual normalized retraction. -/
theorem spherical_active_retraction_moment_bounds {d : Nat} (O : Finset Nat)
    (P : SphericalVariation d) :
    ‖deriv (activeMomentMapAlongRetract O P.measure P.velocity P.tangent) 0‖ ≤
      Real.sqrt (∑ n ∈ O, (n : Real) ^ 2) * Real.sqrt (variationEnergy P) ∧
    ‖deriv (deriv (activeMomentMapAlongRetract O P.measure P.velocity P.tangent)) 0‖ ≤
      Real.sqrt (∑ n ∈ O, (n : Real) ^ 4) * variationEnergy P := by
  rw [(activeMomentRetract_exp_initial_derivatives O P.measure P.velocity P.tangent P.continuous_velocity).1,
    (activeMomentRetract_exp_initial_derivatives O P.measure P.velocity P.tangent P.continuous_velocity).2]
  exact spherical_active_moment_derivative_bounds O P 0

end PaperFormalization.MatrixFactorization
