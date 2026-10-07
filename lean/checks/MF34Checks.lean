import PaperFormalization.MatrixFactorization.SphericalActiveMomentBounds

open MeasureTheory
open PaperFormalization.MatrixFactorization
set_option synthInstance.maxHeartbeats 80000

-- Projection is construction machinery; the original full tensor jets are unchanged.
example {d : Nat} (O : Finset Nat) (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu]
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) :
    (rawActiveFirst O mu v 0).val = rawActiveTensorFirst O mu v 0 := rawActiveFirst_val O mu v hv hc 0
example {d : Nat} (O : Finset Nat) (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu]
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) :
    (rawActiveSecond O mu v 0).val = rawActiveTensorSecond O mu v 0 := rawActiveSecond_val O mu v hv hc 0
example {d : Nat} (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) :
    ‖rawActiveFirst ∅ mu v 0‖ ^ 2 ≤ 0 := by
  simpa only [Finset.univ_eq_empty, Finset.sum_empty, zero_mul] using rawActiveFirst_norm_sq_le ∅ mu v hv hc 0
example {d : Nat} (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) :
    ‖rawActiveSecond ∅ mu v 0‖ ^ 2 ≤ 0 := by
  simpa only [Finset.univ_eq_empty, Finset.sum_empty, zero_mul] using rawActiveSecond_norm_sq_le ∅ mu v hv hc 0

-- The existing source variation energy is preserved with exactly two marginal terms.
example {d : Nat} (P : SphericalVariation d) :
    productTangentEnergy P.measure P.velocity = variationEnergy P := productTangentEnergy_eq_variationEnergy P
example {d : Nat} (P : SphericalVariation d) :
    0 ≤ productTangentEnergy P.measure P.velocity := productTangentEnergy_nonneg _ _
example {d : Nat} (P : SphericalVariation d) :
    ‖deriv (activeMomentMapAlongExp ∅ P.measure P.velocity P.tangent) 0‖ ≤ 0 := by
  simpa only [Finset.sum_empty, Real.sqrt_zero, zero_mul] using
    (spherical_active_moment_derivative_bounds ∅ P 0).1
example {d : Nat} (P : SphericalVariation d) :
    ‖deriv (deriv (activeMomentMapAlongExp ∅ P.measure P.velocity P.tangent)) 0‖ ≤ 0 := by
  simpa only [Finset.sum_empty, Real.sqrt_zero, zero_mul] using
    (spherical_active_moment_derivative_bounds ∅ P 0).2

-- Signed times and even active degrees are valid for the jet bound itself.
example {d : Nat} (O : Finset Nat) (P : SphericalVariation d) :
    ‖deriv (activeMomentMapAlongExp O P.measure P.velocity P.tangent) (-1)‖ ≤
      Real.sqrt (∑ n ∈ O, (n : Real) ^ 2) * Real.sqrt (variationEnergy P) :=
  (spherical_active_moment_derivative_bounds O P (-1)).1
example {d : Nat} (P : SphericalVariation d) :
    ‖deriv (deriv (activeMomentMapAlongExp {2} P.measure P.velocity P.tangent)) 0‖ ≤
      Real.sqrt (∑ n ∈ ({2} : Finset Nat), (n : Real) ^ 4) * variationEnergy P :=
  (spherical_active_moment_derivative_bounds {2} P 0).2
example {d : Nat} (P : SphericalVariation d) :
    ‖deriv (activeMomentMapAlongExp {0} P.measure P.velocity P.tangent) 0‖ ≤ 0 := by
  simpa only [Finset.sum_singleton, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), Real.sqrt_zero, zero_mul]
    using (spherical_active_moment_derivative_bounds {0} P 0).1
example {d : Nat} (mu : Fin 2 → Measure (UnitSphere d)) :
    productTangentEnergy mu (fun _ _ => 0) = 0 := by simp [productTangentEnergy]
