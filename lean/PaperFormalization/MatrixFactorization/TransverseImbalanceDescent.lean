import PaperFormalization.MatrixFactorization.GaussianTransversePairing
import PaperFormalization.MatrixFactorization.TransverseVisibility
import PaperFormalization.MatrixFactorization.TransverseRetractionObjective

/-! # A complete imbalance-to-descent chain for the linear active block

This file specializes the original model to the active set `{1}`. In that case
the actual Gaussian pairing has been identified with the weighted transverse
teacher moment. The original Borel-slice imbalance therefore discharges the
positive-signal premise of the normalized spherical descent theorem. No claim
of arbitrary-degree Hermite orthogonality is made by this specialization.
-/

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

theorem singleton_one_odd : ∀ n : Nat, n ∈ ({1} : Finset Nat) → Odd n := by
  intro n hn
  simpa only [Finset.mem_singleton.mp hn] using (show Odd (1 : Nat) by decide)

theorem linear_imbalance_signal_lower {d h : Nat} (a : Nat → Weight h)
    (pole : UnitSphere d) (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (e : Weight d) (rvis gamma : Real)
    (himb : TwoSidedTeacherImbalance pole teacher e rvis gamma) :
    (activeLatitudeMinimum {1} a rvis * gamma)^2 ≤
      transverseTeacherSignal {1} a pole e teacher := by
  have hb := weightedTransverseMoment_lower {1} a pole teacher e rvis gamma himb
  have hk : 0 ≤ activeLatitudeMinimum {1} a rvis := by
    rw [activeLatitudeMinimum_eq {1} a himb.radius_pos.le himb.radius_lt_one.le]
    exact activeLatitudeWeight_nonneg {1} a himb.radius_pos.le
  have hc : 0 ≤ activeLatitudeMinimum {1} a rvis * gamma := mul_nonneg hk himb.margin_pos.le
  have hj := transverseTeacherSignal_ge_mean_pairing_sq {1} a pole teacher e himb.tangent
  rw [gaussianTransverseMean_eq_weightedMoment_singleton_one] at hj
  exact (pow_le_pow_left₀ hc hb 2).trans hj

theorem linear_imbalance_signal_pos {d h : Nat} (a : Nat → Weight h) (ha : a 1 ≠ 0)
    (pole : UnitSphere d) (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (e : Weight d) (rvis gamma : Real)
    (himb : TwoSidedTeacherImbalance pole teacher e rvis gamma) :
    0 < transverseTeacherSignal {1} a pole e teacher := by
  have hk := activeLatitudeMinimum_pos {1} a singleton_one_odd
    ⟨1, Finset.mem_singleton_self 1, ha⟩ himb.radius_pos himb.radius_lt_one.le
  exact (sq_pos_of_pos (mul_pos hk himb.margin_pos)).trans_le
    (linear_imbalance_signal_lower a pole teacher e rvis gamma himb)

theorem linear_imbalance_gaussian_mean_ne_zero {d h : Nat} (a : Nat → Weight h)
    (ha : a 1 ≠ 0) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] (e : Weight d) (rvis gamma : Real)
    (himb : TwoSidedTeacherImbalance pole teacher e rvis gamma) :
    gaussianTransverseMean {1} a pole teacher ≠ 0 := by
  rw [gaussianTransverseMean_eq_weightedMoment_singleton_one]
  exact weightedTransverseMoment_ne_zero {1} a singleton_one_odd
    ⟨1, Finset.mem_singleton_self 1, ha⟩ pole teacher e rvis gamma himb

/-- The actual normalized objective has strictly negative second derivative
with the source's quantitative imbalance coefficient. -/
theorem linear_imbalance_retracted_negative_curvature {d h : Nat}
    (a : Nat → Weight h) (ha : a 1 ≠ 0) (pole : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] (e : Weight d) (rvis gamma : Real)
    (himb : TwoSidedTeacherImbalance pole teacher e rvis gamma)
    (lambda p : Real) (hp : 2 < p) :
    let P := transverseCenterVariation pole r hr hrpi e
    let F := variationRetractedObjective {1} a P lambda p teacher teacher
    HasDerivAt F 0 0 ∧
      deriv (deriv F) 0 ≤ -2 * (activeLatitudeMinimum {1} a rvis * gamma)^2 ∧
      deriv (deriv F) 0 < 0 := by
  dsimp only
  have hd := transverse_retracted_objective_variations {1} a singleton_one_odd
    pole r hr hrpi e himb.tangent himb.unit lambda p hp teacher
  refine ⟨hd.1, ?_, ?_⟩
  · rw [hd.2.deriv]
    have hb := linear_imbalance_signal_lower a pole teacher e rvis gamma himb
    linarith
  · rw [hd.2.deriv]
    have hp := linear_imbalance_signal_pos a ha pole teacher e rvis gamma himb
    linarith

/-- The coefficient in the full normalized objective's Peano expansion is
the actual positive Gaussian signal, now derived from source imbalance. -/
theorem linear_imbalance_retracted_expansion {d h : Nat} (a : Nat → Weight h)
    (ha : a 1 ≠ 0) (pole : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] (e : Weight d) (rvis gamma : Real)
    (himb : TwoSidedTeacherImbalance pole teacher e rvis gamma)
    (lambda p : Real) (hp : 2 < p) :
    let P := transverseCenterVariation pole r hr hrpi e
    let F := variationRetractedObjective {1} a P lambda p teacher teacher
    0 < transverseTeacherSignal {1} a pole e teacher ∧
      (fun t => F t-F 0+transverseTeacherSignal {1} a pole e teacher*t^2)
        =o[𝓝 (0 : Real)] (fun t => t^2) := by
  exact ⟨linear_imbalance_signal_pos a ha pole teacher e rvis gamma himb,
    transverse_retracted_objective_expansion {1} a singleton_one_odd pole r hr hrpi
      e himb.tangent himb.unit lambda p hp teacher⟩

/-- This is a theorem about the original normalized spherical pushforwards.
The positive-signal premise is discharged, not added to the manuscript. -/
theorem linear_imbalance_retracted_strict_decrease {d h : Nat}
    (a : Nat → Weight h) (ha : a 1 ≠ 0) (pole : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] (e : Weight d) (rvis gamma : Real)
    (himb : TwoSidedTeacherImbalance pole teacher e rvis gamma)
    (lambda p : Real) (hp : 2 < p) :
    let P := transverseCenterVariation pole r hr hrpi e
    let F := variationRetractedObjective {1} a P lambda p teacher teacher
    ∀ᶠ t in 𝓝 (0 : Real), t ≠ 0 →
      F t ≤ F 0-((activeLatitudeMinimum {1} a rvis * gamma)^2/2)*t^2 ∧
      F t < F 0 := by
  have hd := transverse_retracted_strict_decrease {1} a singleton_one_odd
    pole r hr hrpi e himb.tangent himb.unit lambda p hp teacher
    (linear_imbalance_signal_pos a ha pole teacher e rvis gamma himb)
  have hb := linear_imbalance_signal_lower a pole teacher e rvis gamma himb
  dsimp only at hd ⊢
  filter_upwards [hd] with t ht hne
  refine ⟨?_, (ht hne).2⟩
  exact (ht hne).1.trans (sub_le_sub_left
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hb (by norm_num))
      (sq_nonneg t)) _)

end PaperFormalization.MatrixFactorization
