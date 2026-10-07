import PaperFormalization.MatrixFactorization.RawMomentRetractVariation
import PaperFormalization.MatrixFactorization.RawMomentJetNorms

/-! # MF35: equality of the actual raw-moment retraction and EXP jets

Both sides have already been differentiated under their original law. Equality
of their pointwise initial jets is then integrated, retaining the sharp source
bounds without importing the larger domination constants into the conclusion.
-/
open MeasureTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Original-measure integrals of the first pointwise jets agree at zero. -/
theorem rawMomentRetract_first_jet_eq_exp {d n : Nat} (mu : Measure (UnitSphere d))
    (v : UnitSphere d → Weight d) :
    rawMomentAlongRetractFirst n mu v 0 = rawMomentAlongExpFirst n mu v 0 := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun w => retractedTensorFirst_zero_eq_exp w (v w))

/-- The full second jet includes the equal radial accelerations before integration. -/
theorem rawMomentRetract_second_jet_eq_exp {d n : Nat} (mu : Measure (UnitSphere d))
    (v : UnitSphere d → Weight d) :
    rawMomentAlongRetractSecond n mu v 0 = rawMomentAlongExpSecond n mu v 0 := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun w => retractedTensorSecond_zero_eq_exp w (v w))

/-- The actual curves agree to second derivative at zero, not at all parameters. -/
theorem rawMomentRetract_exp_initial_derivatives {d n : Nat} (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) :
    rawMomentAlongRetract n mu v hv 0 = rawMomentAlongExp n mu v hv 0 ∧
    deriv (rawMomentAlongRetract n mu v hv) 0 = deriv (rawMomentAlongExp n mu v hv) 0 ∧
    deriv (deriv (rawMomentAlongRetract n mu v hv)) 0 = deriv (deriv (rawMomentAlongExp n mu v hv)) 0 := by
  constructor
  · rw [rawMomentAlongRetract_integral mu v hv hc, rawMomentAlongExp_integral mu v hv hc]
    simp only [sphericalRetractVector_zero, zero_smul, sphereExpVector_zero]
  constructor
  · rw [(rawMomentAlongRetract_variations mu v hv hc 0).1.deriv,
      (rawMomentAlongExp_variations mu v hv hc 0).1.deriv]
    exact rawMomentRetract_first_jet_eq_exp mu v
  · rw [(rawMomentAlongRetract_second_derivative mu v hv hc 0).deriv,
      (rawMomentAlongExp_second_derivative mu v hv hc 0).deriv]
    exact rawMomentRetract_second_jet_eq_exp mu v

/-- Literal source raw-moment retraction bounds with coefficients n and n-squared. -/
theorem rawMomentAlongRetract_derivative_bounds {d n : Nat} (mu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] (v : UnitSphere d → Weight d)
    (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) :
    Integrable (fun w => ‖v w‖ ^ 2) mu ∧
    ‖deriv (rawMomentAlongRetract n mu v hv) 0‖ ≤ (n : Real) * Real.sqrt (∫ w, ‖v w‖ ^ 2 ∂mu) ∧
    ‖deriv (deriv (rawMomentAlongRetract n mu v hv)) 0‖ ≤ (n : Real) ^ 2 * (∫ w, ‖v w‖ ^ 2 ∂mu) := by
  rw [(rawMomentRetract_exp_initial_derivatives (n := n) mu v hv hc).2.1,
    (rawMomentRetract_exp_initial_derivatives (n := n) mu v hv hc).2.2]
  exact rawMomentAlongExp_derivative_bounds mu v hv hc 0

end PaperFormalization.MatrixFactorization
