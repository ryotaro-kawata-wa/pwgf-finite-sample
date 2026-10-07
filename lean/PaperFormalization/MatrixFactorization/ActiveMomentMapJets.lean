import PaperFormalization.MatrixFactorization.ActiveMomentJetBounds

/-! # MF34: the actual active moment map along product EXP perturbations

Both laws are the original EXP pushforwards. The symmetric and antisymmetric
coordinates vary together, so ambient perturbations may leave the branch.
-/
open MeasureTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000

noncomputable def activeMomentMapAlongExp {d : Nat} (O : Finset Nat)
    (mu : Fin 2 → Measure (UnitSphere d)) [∀ i, IsFiniteMeasure (mu i)]
    (v : Fin 2 → UnitSphere d → Weight d) (hv : ∀ i w, inner Real w.val (v i w) = 0)
    (t : Real) : ActiveMomentCoordinates d O :=
  activeCoordinates (rawActiveAlongExp O (mu 0) (v 0) (hv 0) t)
    (rawActiveAlongExp O (mu 1) (v 1) (hv 1) t)

noncomputable def activeMomentMapFirst {d : Nat} (O : Finset Nat)
    (mu : Fin 2 → Measure (UnitSphere d)) (v : Fin 2 → UnitSphere d → Weight d)
    (t : Real) : ActiveMomentCoordinates d O :=
  activeCoordinates (rawActiveFirst O (mu 0) (v 0) t) (rawActiveFirst O (mu 1) (v 1) t)

noncomputable def activeMomentMapSecond {d : Nat} (O : Finset Nat)
    (mu : Fin 2 → Measure (UnitSphere d)) (v : Fin 2 → UnitSphere d → Weight d)
    (t : Real) : ActiveMomentCoordinates d O :=
  activeCoordinates (rawActiveSecond O (mu 0) (v 0) t) (rawActiveSecond O (mu 1) (v 1) t)

/-- The curve is the previously defined source moment map of the actual laws. -/
theorem activeMomentMapAlongExp_eq {d : Nat} (O : Finset Nat)
    (mu : Fin 2 → Measure (UnitSphere d)) [∀ i, IsFiniteMeasure (mu i)]
    (v : Fin 2 → UnitSphere d → Weight d) (hv : ∀ i w, inner Real w.val (v i w) = 0)
    (t : Real) :
    activeMomentMapAlongExp O mu v hv t = activeMomentMap O
      ((mu 0).map (sphericalExpFamily (v 0) (hv 0) t))
      ((mu 1).map (sphericalExpFamily (v 1) (hv 1) t)) := rfl

theorem activeMomentMapAlongExp_variations {d : Nat} (O : Finset Nat)
    (mu : Fin 2 → Measure (UnitSphere d)) [∀ i, IsFiniteMeasure (mu i)]
    (v : Fin 2 → UnitSphere d → Weight d) (hv : ∀ i w, inner Real w.val (v i w) = 0)
    (hc : ∀ i, Continuous (v i)) (t : Real) :
    HasDerivAt (activeMomentMapAlongExp O mu v hv) (activeMomentMapFirst O mu v t) t ∧
    HasDerivAt (activeMomentMapFirst O mu v) (activeMomentMapSecond O mu v t) t := by
  constructor
  · exact activeCoordinates_hasDerivAt
      (rawActiveAlongExp_hasDerivAt O (mu 0) (v 0) (hv 0) (hc 0) t)
      (rawActiveAlongExp_hasDerivAt O (mu 1) (v 1) (hv 1) (hc 1) t)
  · exact activeCoordinates_hasDerivAt
      (rawActiveFirst_hasDerivAt O (mu 0) (v 0) (hv 0) (hc 0) t)
      (rawActiveFirst_hasDerivAt O (mu 1) (v 1) (hv 1) (hc 1) t)

theorem activeMomentMapAlongExp_second_derivative {d : Nat} (O : Finset Nat)
    (mu : Fin 2 → Measure (UnitSphere d)) [∀ i, IsFiniteMeasure (mu i)]
    (v : Fin 2 → UnitSphere d → Weight d) (hv : ∀ i w, inner Real w.val (v i w) = 0)
    (hc : ∀ i, Continuous (v i)) (t : Real) :
    HasDerivAt (deriv (activeMomentMapAlongExp O mu v hv)) (activeMomentMapSecond O mu v t) t := by
  letI : NormedSpace Real (ActiveMomentCoordinates d O) := PiLp.normedSpace 2 Real _
  have he : deriv (activeMomentMapAlongExp O mu v hv) = activeMomentMapFirst O mu v :=
    funext (fun s => (activeMomentMapAlongExp_variations O mu v hv hc s).1.deriv)
  rw [he]
  exact (activeMomentMapAlongExp_variations O mu v hv hc t).2

/-- The first source parallelogram formula for the original tensor integrals. -/
theorem activeMomentMapFirst_norm_sq {d : Nat} (O : Finset Nat)
    (mu : Fin 2 → Measure (UnitSphere d)) [∀ i, IsFiniteMeasure (mu i)]
    (v : Fin 2 → UnitSphere d → Weight d) (hv : ∀ i w, inner Real w.val (v i w) = 0)
    (hc : ∀ i, Continuous (v i)) (t : Real) :
    ‖activeMomentMapFirst O mu v t‖ ^ 2 = (1 / 2 : Real) * ∑ n : O,
      (‖rawMomentAlongExpFirst n.val (mu 0) (v 0) t‖ ^ 2 +
       ‖rawMomentAlongExpFirst n.val (mu 1) (v 1) t‖ ^ 2) := by
  rw [activeMomentMapFirst, activeCoordinates_block_norm_sq,
    rawActiveFirst_val O (mu 0) (v 0) (hv 0) (hc 0),
    rawActiveFirst_val O (mu 1) (v 1) (hv 1) (hc 1)]
  rfl

/-- The same exact formula retains the full tensor accelerations. -/
theorem activeMomentMapSecond_norm_sq {d : Nat} (O : Finset Nat)
    (mu : Fin 2 → Measure (UnitSphere d)) [∀ i, IsFiniteMeasure (mu i)]
    (v : Fin 2 → UnitSphere d → Weight d) (hv : ∀ i w, inner Real w.val (v i w) = 0)
    (hc : ∀ i, Continuous (v i)) (t : Real) :
    ‖activeMomentMapSecond O mu v t‖ ^ 2 = (1 / 2 : Real) * ∑ n : O,
      (‖rawMomentAlongExpSecond n.val (mu 0) (v 0) t‖ ^ 2 +
       ‖rawMomentAlongExpSecond n.val (mu 1) (v 1) t‖ ^ 2) := by
  rw [activeMomentMapSecond, activeCoordinates_block_norm_sq,
    rawActiveSecond_val O (mu 0) (v 0) (hv 0) (hc 0),
    rawActiveSecond_val O (mu 1) (v 1) (hv 1) (hc 1)]
  rfl

end PaperFormalization.MatrixFactorization
