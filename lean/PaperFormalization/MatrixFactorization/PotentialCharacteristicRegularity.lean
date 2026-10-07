import PaperFormalization.MatrixFactorization.PotentialCharacteristicFlow
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! # MF23: supported time uniformity WITHOUT a previously known cap interval

Execution records: `MF23_VALIDATION.md`.

The global speed bound is derived from actual angular
transport potentials, not from the cap radius. Only separate continuity is
input in PotentialCharacteristicFlow; this module proves joint continuity.
The field representation remains an explicit source-interpretation obligation.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {d h : Nat} {O : Finset Nat} {a : Nat -> Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 -> Measure (UnitSphere d)}

/-- A common Lipschitz bound for every original supported trajectory on [0,infinity).
At t=0 continuity suffices; an endpoint ODE is not added. -/
theorem PotentialCharacteristicFlow.characteristic_val_lipschitzOnWith
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hp : 2 < p) (i : Fin 2)
    (w : UnitSphere d) (hw : w ∈ (initial i).support) :
    LipschitzOnWith (Real.nnabs (potentialSpeedBound d O a lambda p))
      (fun t => (X.characteristic i t w).val) (Ici (0 : Real)) := by
  have hL : LipschitzOnWith (Real.nnabs (potentialSpeedBound d O a lambda p))
      (fun t => (X.characteristic i t w).val) (Ioi (0 : Real)) := by
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun t ht => (X.ode i w hw t ht).differentiableAt) ?_ (convex_Ioi (0 : Real))
    intro t ht
    change 0 < t at ht
    change norm (deriv (fun s => (X.characteristic i s w).val) t) <=
      |potentialSpeedBound d O a lambda p|
    rw [(X.ode i w hw t ht).deriv]
    change norm (-X.field t ht i (X.characteristic i t w)) <= |potentialSpeedBound d O a lambda p|
    rw [norm_neg]
    exact (X.field_norm_le hp t ht i _
      (X.characteristic_mem_support i t ht.le w hw)).trans (le_abs_self _)
  have hc : ContinuousOn (fun t => (X.characteristic i t w).val) (closure (Ioi (0 : Real))) := by
    rw [closure_Ioi]
    exact continuous_subtype_val.comp_continuousOn (X.continuous_time i w hw)
  simpa only [closure_Ioi] using hL.closure hc

theorem PotentialCharacteristicFlow.characteristic_lipschitzOnWith
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hp : 2 < p) (i : Fin 2)
    (w : UnitSphere d) (hw : w ∈ (initial i).support) :
    LipschitzOnWith (Real.nnabs (potentialSpeedBound d O a lambda p))
      (fun t => X.characteristic i t w) (Ici (0 : Real)) := by
  intro s hs t ht
  exact X.characteristic_val_lipschitzOnWith hp i w hw hs ht

/-- The supported joint continuity needed by the MF22 compact maximum theorem.
It is a conclusion, not a field of the global representation. -/
theorem PotentialCharacteristicFlow.characteristic_joint_continuousOn
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hp : 2 < p) (i : Fin 2) :
    ContinuousOn (fun tw : Real × UnitSphere d => X.characteristic i tw.1 tw.2)
      ((Ici (0 : Real)) ×ˢ (initial i).support) := by
  intro tw htw
  rcases tw with ⟨ t,w ⟩
  rcases htw with ⟨ ht,hw ⟩
  rw [Metric.continuousWithinAt_iff]
  intro eps heps
  obtain ⟨ delta,hdelta,hspace ⟩ := Metric.continuousWithinAt_iff.mp
    (X.continuous_space i t ht w hw) (eps/2) (by positivity)
  let K := |potentialSpeedBound d O a lambda p|
  have hK : 0 <= K := abs_nonneg _
  refine ⟨ min delta (eps/(2*(K+1))), lt_min hdelta (by positivity), ?_ ⟩
  rintro ⟨ s,u ⟩ ⟨ hs,hu ⟩ hsu
  rw [Prod.dist_eq] at hsu
  have hst : dist s t < eps/(2*(K+1)) :=
    (le_max_left _ _).trans_lt (hsu.trans_le (min_le_right _ _))
  have huw : dist u w < delta :=
    (le_max_right _ _).trans_lt (hsu.trans_le (min_le_left _ _))
  have hsp := hspace hu huw
  have htime := (X.characteristic_lipschitzOnWith hp i u hu).dist_le_mul s hs t ht
  have htimelt : dist (X.characteristic i s u) (X.characteristic i t u) < eps/2 := by
    have hh := (lt_div_iff₀ (show 0 < 2*(K+1) by positivity)).mp hst
    change dist (X.characteristic i s u) (X.characteristic i t u) <= K*dist s t at htime
    have hdist : 0 <= dist s t := dist_nonneg
    nlinarith
  exact (dist_triangle (X.characteristic i s u) (X.characteristic i t u)
    (X.characteristic i t w)).trans_lt (by linarith)

/-- A uniform angular displacement estimate from the original label, at any time. -/
theorem PotentialCharacteristicFlow.angular_displacement_le
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hp : 2 < p) (i : Fin 2)
    (w : UnitSphere d) (hw : w ∈ (initial i).support) (t : Real) (ht : 0 <= t) :
    sphericalDistance (X.characteristic i t w) w <=
      (Real.pi/2)*potentialSpeedBound d O a lambda p*t := by
  have hM := potentialSpeedBound_nonneg d O a lambda p
  have hl := (X.characteristic_lipschitzOnWith hp i w hw).dist_le_mul t ht 0
    (by simp only [mem_Ici]; exact le_rfl)
  rw [X.initial_map i w hw] at hl
  change norm ((X.characteristic i t w).val-w.val) <=
    |potentialSpeedBound d O a lambda p| * dist t 0 at hl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ht, abs_of_nonneg hM] at hl
  exact (sphericalDistance_le_pi_half_chord (X.characteristic i t w) w).trans
    (by nlinarith [Real.pi_pos])

end PaperFormalization.MatrixFactorization
