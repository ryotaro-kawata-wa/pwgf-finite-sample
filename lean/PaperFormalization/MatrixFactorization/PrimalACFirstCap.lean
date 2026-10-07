import PaperFormalization.MatrixFactorization.PrimalACCharacteristics
import PaperFormalization.MatrixFactorization.AntipodalPotentialGeometry
import PaperFormalization.MatrixFactorization.ExactSupportRadius
import PaperFormalization.MatrixFactorization.ContinuousCapAssignment

/-! # MF25: a common first cap interval from an AE characteristic ODE

Verification status and conditional scope: see `MF25_VALIDATION.md`. The statewise primal speed estimate is integrated before
lifting endpoint bounds to the original CLOSED support. Thus this first
interval does not use a speed bound which already assumes current cap laws.
The exact initial support maximum and exact half masses are retained.

The theorem concerns PrimalACCharacteristicData with its explicit AC/Borel/
first-variation inputs, not every distributional solution of a continuity
equation. It does not assert all-time confinement or finite uniqueness.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def primalInitialCapTime (d : Nat) {h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (r lambda p : Real)
    (initial : Fin 2 → Measure (UnitSphere d)) : Real :=
  (r - productSphericalSupportRadius pole initial) /
    (Real.pi * (primalObjectiveSpeedBound d O a lambda p + 1))

theorem primalInitialCapTime_pos {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (r lambda p : Real)
    (initial : Fin 2 → Measure (UnitSphere d)) (hl : 0 ≤ lambda)
    (hc : ∀ i, TwoCapClass pole r (initial i)) :
    0 < primalInitialCapTime d O a pole r lambda p initial := by
  have hR := productSphericalSupportRadius_cap_properties pole r initial hc
  have hM := primalObjectiveSpeedBound_nonneg d O a lambda p hl
  exact div_pos (sub_pos.mpr hR.2.1) (mul_pos Real.pi_pos (by linarith))

variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

/-- Angular displacement is derived from the ambient integral bound, not
by replacing the angular transport metric with the chordal distance. -/
theorem PrimalACCharacteristicData.angular_displacement_le
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (initial i).support)
    (t : Real) (ht : 0 ≤ t) :
    sphericalDistance (X.characteristic i t w) w ≤
      (Real.pi / 2) * primalObjectiveSpeedBound d O a lambda p * t := by
  have hM := primalObjectiveSpeedBound_nonneg d O a lambda p hl
  have hb := (X.supported_lipschitz hl hp i w hw).dist_le_mul t ht 0 (by simp)
  rw [X.initial_map i w hw] at hb
  change norm ((X.characteristic i t w).val - w.val) ≤
    |primalObjectiveSpeedBound d O a lambda p| * dist t 0 at hb
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ht, abs_of_nonneg hM] at hb
  exact (sphericalDistance_le_pi_half_chord (X.characteristic i t w) w).trans
    (by nlinarith [Real.pi_pos])

/-- A proved good prefix yields all current cap fields, including exact mass.
No current half-mass or optimal-transport formula is supplied as a premise. -/
theorem PrimalACCharacteristicData.cap_on_prefix
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r T : Real) (hT : 0 ≤ T) (hc : ∀ i, TwoCapClass pole r (initial i))
    (hin : ∀ i w, w ∈ (initial i).support → ∀ t ∈ Icc (0 : Real) T,
      X.characteristic i t w ∈ sphericalCap pole r ∪ sphericalCap (reflect pole) r)
    (i : Fin 2) (t : Real) (ht : t ∈ Icc (0 : Real) T) :
    TwoCapClass pole r (X.measure i t) :=
  (hc i).map_of_continuous_paths (X.characteristic i) T hT (X.initial_map i)
    (fun w hw => (X.supported_time_continuity hl hp i w hw).mono (fun _ hs => hs.1))
    (hin i) t ht (X.measurable_space i t) (X.continuous_space i t ht.1)

/-- All original supported particles remain in the caps on one explicitly
positive interval. Zero speed causes no division by zero. -/
theorem PrimalACCharacteristicData.first_cap_particles
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r : Real) (hc : ∀ i, TwoCapClass pole r (initial i)) :
    let tau := primalInitialCapTime d O a pole r lambda p initial
    0 < tau ∧
      ∀ i w, w ∈ (initial i).support → ∀ t ∈ Icc (0 : Real) tau,
        X.characteristic i t w ∈ sphericalCap pole r ∪ sphericalCap (reflect pole) r := by
  let R := productSphericalSupportRadius pole initial
  let M := primalObjectiveSpeedBound d O a lambda p
  have hR := productSphericalSupportRadius_cap_properties pole r initial hc
  have hM : 0 ≤ M := primalObjectiveSpeedBound_nonneg d O a lambda p hl
  refine ⟨primalInitialCapTime_pos O a pole r lambda p initial hl hc, ?_⟩
  intro i w hw t ht
  have ht' : t ≤ (r - R) / (Real.pi * (M + 1)) := ht.2
  have htime : t * (Real.pi * (M + 1)) ≤ r - R :=
    (le_div_iff₀ (mul_pos Real.pi_pos (by linarith))).mp ht'
  have hdisp := X.angular_displacement_le hl hp i w hw t ht.1
  have htri := assignedPole_distance_triangle pole (X.characteristic i t w) w
  have hlabel := hR.2.2.1 i w hw
  have hpt : 0 ≤ Real.pi * t := mul_nonneg Real.pi_pos.le ht.1
  have hrnow : sphericalDistance (X.characteristic i t w)
      (assignedPole pole (X.characteristic i t w)) < r := by
    change sphericalDistance w (assignedPole pole w) ≤ R at hlabel
    change sphericalDistance (X.characteristic i t w) w ≤ (Real.pi / 2) * M * t at hdisp
    have hRr : R < r := hR.2.1
    nlinarith
  rcases assignedPole_mem pole (X.characteristic i t w) with hplus | hminus
  · exact Or.inl (by simpa only [sphericalCap, Set.mem_setOf_eq, hplus] using hrnow)
  · exact Or.inr (by simpa only [sphericalCap, Set.mem_setOf_eq, hminus] using hrnow)

/-- First complete cap laws. This is an output on an explicit positive
interval, not a cap field assumed for an arbitrary time horizon. -/
theorem PrimalACCharacteristicData.first_cap_laws
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r : Real) (hc : ∀ i, TwoCapClass pole r (initial i)) :
    let tau := primalInitialCapTime d O a pole r lambda p initial
    0 < tau ∧ ∀ i t, t ∈ Icc (0 : Real) tau → TwoCapClass pole r (X.measure i t) := by
  have hfirst := X.first_cap_particles hl hp r hc
  exact ⟨hfirst.1, X.cap_on_prefix hl hp r _ hfirst.1.le hc hfirst.2⟩

/-- Current-law local gradient identification remains AE. The endpoint
regularity result is not used to overwrite arbitrary null-set field values. -/
theorem PrimalACCharacteristicData.first_cap_gradient_ae
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r : Real) (hc : ∀ i, TwoCapClass pole r (initial i)) :
    let tau := primalInitialCapTime d O a pole r lambda p initial
    ∀ᵐ t ∂volume.restrict (Icc (0 : Real) tau), ∀ i,
      X.gradient i t =ᵐ[X.measure i t]
        sphericalObjectiveGradient O a pole lambda p (X.measure 0 t) (X.measure 1 t)
          teacher teacher i := by
  let tau := primalInitialCapTime d O a pole r lambda p initial
  have hf := (ae_restrict_iff' measurableSet_Ici).mp X.first_variation
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  filter_upwards [hf] with t ht htime
  have H := ht htime.1
  exact (source_primal_gradient_statewise O a pole lambda p hl hp
    (fun i => X.measure i t) (fun i => X.measure_probability i t) teacher
    (fun i => X.gradient i t) H).2.2 r
      (fun i => (X.first_cap_laws hl hp r hc).2 i t htime)

end PaperFormalization.MatrixFactorization
