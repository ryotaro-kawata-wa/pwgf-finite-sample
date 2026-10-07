import PaperFormalization.MatrixFactorization.TransverseRetractionObjective

/-! MF08 diagnostics for the literal normalized retraction and degenerate data. -/
open MeasureTheory
open scoped Topology
open PaperFormalization.MatrixFactorization
set_option autoImplicit false

example (t : Real) : retractionScale 0 t = 1 := by simp [retractionScale]

example (t : Real) : retractionScaleFirst 0 t = 0 := by simp [retractionScaleFirst]

example {d : Nat} (w : UnitSphere d) (t : Real) : sphericalRetractVector w 0 t = w.val := by
  simp [sphericalRetractVector]

example {d : Nat} (w : UnitSphere d) (t : Real) : sphericalRetract w 0 (by simp) t = w := by
  apply Subtype.ext
  simp [sphericalRetract, sphericalRetractVector]

-- The normalized path has unit norm even at a large negative time.
example {d : Nat} (w : UnitSphere d) (v : Weight d) (hv : inner Real w.val v = 0) :
    norm (sphericalRetractVector w v (-7)) = 1 := sphericalRetractVector_norm w v hv (-7)

-- Unit-speed acceleration is -w, with no missing normalization or factor two.
example {d : Nat} (w : UnitSphere d) (v : Weight d) (hv : inner Real w.val v = 0)
    (hunit : norm v = 1) : HasDerivAt (deriv (sphericalRetractVector w v)) (-w.val) 0 := by
  have hd := (sphericalRetract_second_jet w v hv).2
  apply hd.congr_deriv
  simp [hunit]

-- Zero velocity is included in the ordinary second derivative statement.
example {d : Nat} (w : UnitSphere d) :
    HasDerivAt (deriv (sphericalRetractVector w 0)) 0 0 := by
  have hd := (sphericalRetract_second_jet w 0 (by simp)).2
  apply hd.congr_deriv
  simp

-- The comparison is second-order agreement, not equality of the two paths.
example {d : Nat} (w : UnitSphere d) (v : Weight d) (hv : inner Real w.val v = 0) :
    Asymptotics.IsLittleO (𝓝 (0 : Real))
      (fun t => (sphericalRetract w v hv t).val-(geodesicPoint w v hv t).val)
      (fun t => t^2) := sphericalRetract_exp_littleO w v hv


-- The time change preserves both signs of time and its normalization at zero.
example (t : Real) : halfSpeedTime (-t) = -halfSpeedTime t := by
  simp [halfSpeedTime, neg_div]

example : HasDerivAt halfSpeedTime 1 0 ∧ HasDerivAt (deriv halfSpeedTime) 0 0 :=
  ⟨halfSpeedTime_first_zero, halfSpeedTime_second_zero⟩

-- The exact measure identity also holds at a negative time, before taking jets.
example {d : Nat} (pole : UnitSphere d) (r : Real) (hr : 0 < r) (hrpi : r < Real.pi/2)
    (s : Weight d) (hs : inner Real pole.val s = 0) (hunit : norm s = 1) :
    let P := transverseCenterVariation pole r hr hrpi s
    (P.measure 0).map (sphericalRetractFamily (P.velocity 0) (P.tangent 0) (-2)) =
      (P.measure 0).map (sphericalExpFamily (P.velocity 0) (P.tangent 0) (halfSpeedTime (-2))) :=
  transverseCenter_retract_map_eq_exp pole r hr hrpi s hs hunit 0 (-2)

-- A noninteger power between two and three is included for the literal objective.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n)
    (pole : UnitSphere d) (r : Real) (hr : 0 < r) (hrpi : r < Real.pi/2)
    (s : Weight d) (hs : inner Real pole.val s = 0) (hunit : norm s = 1) (lambda : Real)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    let P := transverseCenterVariation pole r hr hrpi s
    let F := variationRetractedObjective O a P lambda (5/2) teacher teacher
    Asymptotics.IsLittleO (𝓝 (0 : Real))
      (fun t => F t-F 0+transverseTeacherSignal O a pole s teacher*t^2) (fun t => t^2) :=
  transverse_retracted_objective_expansion O a hO pole r hr hrpi s hs hunit lambda (5/2) (by norm_num) teacher

-- A symmetric antipodal teacher has zero quadratic signal, so no strict decrease is asserted.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n)
    (pole other : UnitSphere d) (r : Real) (hr : 0 < r) (hrpi : r < Real.pi/2)
    (s : Weight d) (hs : inner Real pole.val s = 0) (hunit : norm s = 1)
    (lambda p : Real) (hp : 2 < p) :
    let F := variationRetractedObjective O a (transverseCenterVariation pole r hr hrpi s) lambda p
      (antipodalMeasure other) (antipodalMeasure other)
    Asymptotics.IsLittleO (𝓝 (0 : Real)) (fun t => F t-F 0) (fun t => t^2) := by
  have he := transverse_retracted_objective_expansion O a hO pole r hr hrpi s hs hunit lambda p hp (antipodalMeasure other)
  simpa [transverseTeacherSignal, finiteHermite_mean_antipodal O a hO other] using he

-- The same noninteger power leaves the actual normalized metric term quadratically flat.
example {d : Nat} (pole : UnitSphere d) (r : Real) (hr : 0 < r) (hrpi : r < Real.pi/2)
    (s : Weight d) (hs : inner Real pole.val s = 0) (hunit : norm s = 1) (lambda : Real) :
    Asymptotics.IsLittleO (𝓝 (0 : Real))
      (variationRetractedRegularizer (transverseCenterVariation pole r hr hrpi s) lambda (5/2))
      (fun t => t^2) :=
  transverse_retracted_regularizer_littleO pole r hr hrpi s hs hunit lambda (5/2) (by norm_num)
