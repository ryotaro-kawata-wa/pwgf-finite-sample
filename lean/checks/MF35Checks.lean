import PaperFormalization.MatrixFactorization.ActiveRetractionJetEquality

open MeasureTheory
open PaperFormalization.MatrixFactorization
set_option synthInstance.maxHeartbeats 80000

-- Both literal pathwise jets retain zero velocity and the radial acceleration.
example {d n : Nat} (w : UnitSphere d) (v : Weight d) :
    retractedTensorFirst n w v 0 = sphericalTensorFirst n w v 0 := retractedTensorFirst_zero_eq_exp w v
example {d n : Nat} (w : UnitSphere d) (v : Weight d) :
    retractedTensorSecond n w v 0 = sphericalTensorSecond n w v 0 := retractedTensorSecond_zero_eq_exp w v
example {d n : Nat} (w : UnitSphere d) (t : Real) : ‖retractedTensorFirst n w 0 t‖ ≤ 0 := by
  simpa only [norm_zero, mul_zero] using retractedTensorFirst_norm_le (n := n) w 0 (by simp) t
example {d n : Nat} (w : UnitSphere d) (t : Real) : ‖retractedTensorSecond n w 0 t‖ ≤ 0 := by
  simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] using
    retractedTensorSecond_norm_le (n := n) w 0 (by simp) t
example {d n : Nat} (w : UnitSphere d) (v : Weight d) (hv : inner Real w.val v = 0) :
    HasDerivAt (retractedTensorFirst n w v) (retractedTensorSecond n w v (-1)) (-1) :=
  retractedTensorFirst_hasDerivAt w v hv (-1)
example {d : Nat} (w : UnitSphere d) (v a : Weight d) (B : Real)
    (hv : ‖v‖ ^ 2 ≤ B) (ha : ‖a‖ ≤ B) : ‖tensorSecondJet 0 w.val v a‖ ≤ 0 := by
  simpa only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_mul] using
    tensorSecondJet_norm_le_of_bounds (n := 0) w v a B hv ha

-- Original-law integration precedes comparison of the actual derivatives.
example {d n : Nat} (a : UnitSphere d) (v : UnitSphere d → Weight d) :
    rawMomentAlongRetractFirst n (antipodalMeasure a) v 0 = rawMomentAlongExpFirst n (antipodalMeasure a) v 0 :=
  rawMomentRetract_first_jet_eq_exp _ v
example {d n : Nat} (a : UnitSphere d) (v : UnitSphere d → Weight d) :
    rawMomentAlongRetractSecond n (antipodalMeasure a) v 0 = rawMomentAlongExpSecond n (antipodalMeasure a) v 0 :=
  rawMomentRetract_second_jet_eq_exp _ v
example {d : Nat} (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) :
    ‖deriv (rawMomentAlongRetract 0 mu v hv) 0‖ ≤ 0 := by
  simpa only [Nat.cast_zero, zero_mul] using (rawMomentAlongRetract_derivative_bounds (n := 0) mu v hv hc).2.1
example {d : Nat} (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) :
    ‖deriv (deriv (rawMomentAlongRetract 0 mu v hv)) 0‖ ≤ 0 := by
  simpa only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_mul] using
    (rawMomentAlongRetract_derivative_bounds (n := 0) mu v hv hc).2.2

-- The active source map and its existing product energy have no rescaling.
example {d : Nat} (O : Finset Nat) (mu : Measure (UnitSphere d)) (v : UnitSphere d → Weight d) :
    rawActiveRetractFirst O mu v 0 = rawActiveFirst O mu v 0 := rawActiveRetractFirst_zero_eq_exp O mu v
example {d : Nat} (O : Finset Nat) (mu : Measure (UnitSphere d)) (v : UnitSphere d → Weight d) :
    rawActiveRetractSecond O mu v 0 = rawActiveSecond O mu v 0 := rawActiveRetractSecond_zero_eq_exp O mu v
example {d : Nat} (P : SphericalVariation d) :
    ‖deriv (activeMomentMapAlongRetract ∅ P.measure P.velocity P.tangent) 0‖ ≤ 0 := by
  simpa only [Finset.sum_empty, Real.sqrt_zero, zero_mul] using
    (spherical_active_retraction_moment_bounds ∅ P).1
example {d : Nat} (P : SphericalVariation d) :
    ‖deriv (deriv (activeMomentMapAlongRetract ∅ P.measure P.velocity P.tangent)) 0‖ ≤ 0 := by
  simpa only [Finset.sum_empty, Real.sqrt_zero, zero_mul] using
    (spherical_active_retraction_moment_bounds ∅ P).2
example {d : Nat} (O : Finset Nat) (P : SphericalVariation d) :
    deriv (activeMomentMapAlongRetract O P.measure P.velocity P.tangent) 0 =
      deriv (activeMomentMapAlongExp O P.measure P.velocity P.tangent) 0 :=
  (activeMomentRetract_exp_initial_derivatives O P.measure P.velocity P.tangent P.continuous_velocity).1
example {d : Nat} (O : Finset Nat) (P : SphericalVariation d) :
    deriv (deriv (activeMomentMapAlongRetract O P.measure P.velocity P.tangent)) 0 =
      deriv (deriv (activeMomentMapAlongExp O P.measure P.velocity P.tangent)) 0 :=
  (activeMomentRetract_exp_initial_derivatives O P.measure P.velocity P.tangent P.continuous_velocity).2
