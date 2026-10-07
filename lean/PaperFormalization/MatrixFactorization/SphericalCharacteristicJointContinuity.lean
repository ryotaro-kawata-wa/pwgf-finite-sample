import PaperFormalization.MatrixFactorization.SphericalCharacteristicFeatures
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! # Uniform time regularity on an already given cap interval

The original supported ODE and the derived cap speed bound imply a common
Lipschitz constant for all supported particle curves. The original spatial
continuity then gives joint continuity on the time/support product. This is
regularity on a given cap interval; it neither constructs a cap-free global
flow nor proves that such a flow initially stays in the cap class.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}

/-- Every original supported ambient characteristic has the same time
Lipschitz constant, including both endpoints and a zero-length interval. -/
theorem SphericalCharacteristicSolution.characteristic_val_lipschitzOnWith
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p) (i : Fin 2)
    (w : UnitSphere d) (hw : w ∈ (initial i).support) :
    LipschitzOnWith (Real.nnabs (characteristicSpeedBound d O a radius lambda p))
      (fun t => (X.characteristic i t w).val) (Icc (0 : Real) T) := by
  by_cases hT : T = 0
  · subst T
    intro s hs t ht
    have hs0 : s = 0 := le_antisymm hs.2 hs.1
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    simp [hs0,ht0]
  have hT : 0 < T := lt_of_le_of_ne X.time_nonneg (Ne.symm hT)
  have hL : LipschitzOnWith (Real.nnabs (characteristicSpeedBound d O a radius lambda p))
      (fun t => (X.characteristic i t w).val) (Ioo (0 : Real) T) := by
    apply (convex_Ioo (0 : Real) T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t ht => (X.ode i w hw t ht).hasDerivWithinAt)
    intro t ht
    change norm (-sphericalObjectiveGradient O a pole lambda p (X.measure 0 t)
      (X.measure 1 t) teacher teacher i (X.characteristic i t w)) ≤
        |characteristicSpeedBound d O a radius lambda p|
    rw [norm_neg]
    exact (X.gradient_norm_le_speedBound hp i t ⟨ht.1.le,ht.2.le⟩ _
      (X.characteristic_mem_support i t ⟨ht.1.le,ht.2.le⟩ w hw)).trans (le_abs_self _)
  have hc : ContinuousOn (fun t => (X.characteristic i t w).val) (closure (Ioo (0 : Real) T)) := by
    rw [closure_Ioo hT.ne]
    exact continuous_subtype_val.comp_continuousOn (X.continuous_time i w hw)
  simpa only [closure_Ioo hT.ne] using hL.closure hc

/-- The sphere's inherited metric is the chordal metric, so the same bound
passes through subtype coercion without changing the angular cost. -/
theorem SphericalCharacteristicSolution.characteristic_lipschitzOnWith
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p) (i : Fin 2)
    (w : UnitSphere d) (hw : w ∈ (initial i).support) :
    LipschitzOnWith (Real.nnabs (characteristicSpeedBound d O a radius lambda p))
      (fun t => X.characteristic i t w) (Icc (0 : Real) T) := by
  intro s hs t ht
  exact X.characteristic_val_lipschitzOnWith hp i w hw hs ht

/-- Joint time/label continuity is derived from a uniform time bound and
original support-only spatial continuity. No global label continuity is added. -/
theorem SphericalCharacteristicSolution.characteristic_joint_continuousOn
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p) (i : Fin 2) :
    ContinuousOn (fun tw : Real × UnitSphere d => X.characteristic i tw.1 tw.2)
      ((Icc (0 : Real) T) ×ˢ (initial i).support) := by
  intro tw htw
  rcases tw with ⟨t,w⟩
  rcases htw with ⟨ht,hw⟩
  rw [Metric.continuousWithinAt_iff]
  intro eps heps
  obtain ⟨delta,hdelta,hspace⟩ := Metric.continuousWithinAt_iff.mp
    (X.continuous_space i t ht w hw) (eps/2) (by positivity)
  let K : Real := |characteristicSpeedBound d O a radius lambda p|
  have hK : 0 ≤ K := abs_nonneg _
  refine ⟨min delta (eps/(2*(K+1))),lt_min hdelta (by positivity),?_⟩
  rintro ⟨s,u⟩ ⟨hs,hu⟩ hsu
  rw [Prod.dist_eq] at hsu
  have hst : dist s t < eps/(2*(K+1)) := by
    exact (le_max_left _ _).trans_lt (hsu.trans_le (min_le_right _ _))
  have huw : dist u w < delta :=
    (le_max_right _ _).trans_lt (hsu.trans_le (min_le_left _ _))
  have hsp := hspace hu huw
  have htime := (X.characteristic_lipschitzOnWith hp i u hu).dist_le_mul s hs t ht
  have htimelt : dist (X.characteristic i s u) (X.characteristic i t u) < eps/2 := by
    have hsmall : (K+1)*dist s t < eps/2 := by
      have hh := (lt_div_iff₀ (show 0 < 2*(K+1) by positivity)).mp hst
      nlinarith
    change dist (X.characteristic i s u) (X.characteristic i t u) ≤ K*dist s t at htime
    have hd : 0 ≤ dist s t := dist_nonneg
    linarith
  exact (dist_triangle (X.characteristic i s u) (X.characteristic i t u)
    (X.characteristic i t w)).trans_lt (by linarith)

end PaperFormalization.MatrixFactorization
