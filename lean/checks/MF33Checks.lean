import PaperFormalization.MatrixFactorization.RawMomentJetNorms

open MeasureTheory
open PaperFormalization.MatrixFactorization

-- Empty tensors, zero velocity, and the radial second jet retain their true values.
example (d : Nat) (v : Fin 0 → Weight d) : ‖mixedTensorMap d 0 v‖ = 1 := by
  rw [mixedTensorMap_norm]; simp
example {d : Nat} (w : UnitSphere d) (v : Weight d) : ‖tensorFirstJet 0 w.val v‖ ≤ 0 := by
  simpa only [Nat.cast_zero, zero_mul] using tensorFirstJet_norm_le (n := 0) w v
example {d : Nat} (w : UnitSphere d) (v : Weight d) :
    ‖tensorSecondJet 0 w.val v (-(‖v‖ ^ 2) • w.val)‖ = 0 := by simp [tensorSecondJet]
example {d : Nat} (w : UnitSphere d) (v : Weight d) :
    sphericalTensorSecond 1 w v 0 = tensorSecondJet 1 w.val v (-(‖v‖ ^ 2) • w.val) :=
  sphericalTensorSecond_zero w v
example {d : Nat} (w : UnitSphere d) (n : Nat) (t : Real) :
    ‖sphericalTensorFirst n w 0 t‖ ≤ 0 := by
  simpa only [norm_zero, mul_zero] using sphericalTensorFirst_norm_le (n := n) w 0 (by simp) t
example {d : Nat} (w : UnitSphere d) (n : Nat) (t : Real) :
    ‖sphericalTensorSecond n w 0 t‖ ≤ 0 := by
  simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] using
    sphericalTensorSecond_norm_le (n := n) w 0 (by simp) t

-- Both derivatives are of the original signed-time spherical curve.
example {d n : Nat} (w : UnitSphere d) (v : Weight d) :
    HasDerivAt (fun s : Real => tensorPower n (sphereExpVector w (s • v)))
      (sphericalTensorFirst n w v (-1)) (-1) := sphericalTensor_hasDerivAt w v (-1)
example {d n : Nat} (w : UnitSphere d) (v : Weight d) :
    HasDerivAt (sphericalTensorFirst n w v) (sphericalTensorSecond n w v 0) 0 :=
  sphericalTensorFirst_hasDerivAt w v 0
example {d n : Nat} (w : UnitSphere d) (v : Weight d) (hv : inner Real w.val v = 0) :
    ‖sphericalTensorSecond n w v (-1)‖ ≤ (n : Real) ^ 2 * ‖v‖ ^ 2 :=
  sphericalTensorSecond_norm_le w v hv (-1)
example {d n : Nat} (w : UnitSphere d) (v : Weight d) :
    sphericalTensorFirst n w v 0 = tensorFirstJet n w.val v := sphericalTensorFirst_zero w v

-- Atomic laws are included and the actual Bochner differentiation exchanges are used.
example {d n : Nat} (a : UnitSphere d) (v : UnitSphere d → Weight d)
    (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) :
    HasDerivAt (rawMomentAlongExp n (antipodalMeasure a) v hv)
      (rawMomentAlongExpFirst n (antipodalMeasure a) v 0) 0 :=
  (rawMomentAlongExp_variations _ v hv hc 0).1
example {d n : Nat} (a : UnitSphere d) (v : UnitSphere d → Weight d)
    (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) :
    HasDerivAt (deriv (rawMomentAlongExp n (antipodalMeasure a) v hv))
      (rawMomentAlongExpSecond n (antipodalMeasure a) v 0) 0 :=
  rawMomentAlongExp_second_derivative _ v hv hc 0
example {d : Nat} (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) :
    ‖deriv (rawMomentAlongExp 0 mu v hv) 0‖ ≤ 0 := by
  simpa only [Nat.cast_zero, zero_mul] using (rawMomentAlongExp_derivative_bounds (n := 0) mu v hv hc 0).2.1
example {d : Nat} (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) :
    ‖deriv (deriv (rawMomentAlongExp 0 mu v hv)) 0‖ ≤ 0 := by
  simpa only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_mul] using
    (rawMomentAlongExp_derivative_bounds (n := 0) mu v hv hc 0).2.2
example {d n : Nat} (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) :
    ‖rawMomentAlongExpSecond n mu v (-1)‖ ≤ (n : Real) ^ 2 * (∫ w, ‖v w‖ ^ 2 ∂mu) :=
  rawMomentAlongExpSecond_norm_le mu v hv hc (-1)
example {d : Nat} (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    (v : UnitSphere d → Weight d) (hc : Continuous v) :
    (∫ w, ‖v w‖ ∂mu) ≤ Real.sqrt (∫ w, ‖v w‖ ^ 2 ∂mu) :=
  sphere_integral_norm_le_sqrt_energy mu v hc
