import PaperFormalization.MatrixFactorization.TransverseObjectiveExpansion

/-! MF07 boundary diagnostics for half fields, half masses, and visibility. -/
open MeasureTheory ProbabilityTheory
open scoped Topology
open PaperFormalization.MatrixFactorization
set_option autoImplicit false

example {d : Nat} (w : UnitSphere d) : transverseHalfField (0 : Weight d) w = 0 := by
  simp [transverseHalfField]

-- Normal input is removed by the tangent projection at the pole.
example {d : Nat} (w : UnitSphere d) : transverseHalfField w.val w = 0 := by
  simp [transverseHalfField, real_inner_self_eq_norm_sq]

example {d : Nat} (pole : UnitSphere d) (r : Real) (hr : 0 < r) (hrpi : r < Real.pi/2) :
    variationEnergy (transverseCenterVariation pole r hr hrpi 0) = 0 := by
  rw [transverseCenterVariation_energy pole r hr hrpi 0 (by simp)]
  simp

-- A unit transverse direction has product energy one-half, not one or two.
example {d : Nat} (pole : UnitSphere d) (r : Real) (hr : 0 < r) (hrpi : r < Real.pi/2)
    (s : Weight d) (hs : inner Real pole.val s = 0) (hunit : norm s = 1) :
    variationEnergy (transverseCenterVariation pole r hr hrpi s) = (1/2 : Real) := by
  rw [transverseCenterVariation_energy pole r hr hrpi s hs, hunit]
  norm_num

example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (pole : UnitSphere d) (z : Weight d) :
    transverseFeature O a pole 0 z = 0 := by simp [transverseFeature]

-- The linear Hermite mode exposes the exact half-field coefficient.
example {d h : Nat} (a : Nat → Weight h) (pole : UnitSphere d) (s z : Weight d) :
    transverseFeature {1} a pole s z = ((1/2 : Real)*inner Real s z) • a 1 := by
  simp [transverseFeature, finiteHermiteActivationJet, normalizedHermiteJet, hermiteRealPolynomial,
    Polynomial.hermite_one]

example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n)
    (pole other : UnitSphere d) (s : Weight d) :
    transverseTeacherSignal O a pole s (antipodalMeasure other) = 0 := by
  simp [transverseTeacherSignal, finiteHermite_mean_antipodal O a hO other]

-- Empty activation supplies no strict visibility even for a nonzero field.
example {d h : Nat} (a : Nat → Weight h) (pole : UnitSphere d) (s : Weight d)
    (teacher : Measure (UnitSphere d)) : transverseTeacherSignal ∅ a pole s teacher = 0 := by
  simp [transverseTeacherSignal, transverseFeature, finiteHermiteActivationJet]

-- A nonintegral power between two and three is still a genuine little-o remainder.
example {d : Nat} (pole : UnitSphere d) (r : Real) (hr : 0 < r) (hrpi : r < Real.pi/2)
    (s : Weight d) (lambda : Real) :
    Asymptotics.IsLittleO (𝓝 (0 : Real))
      (variationRegularizer (transverseCenterVariation pole r hr hrpi s) lambda (5/2))
      (fun t => t^2) :=
  transverse_center_regularizer_littleO pole r hr hrpi s lambda (5/2) (by norm_num)

-- Vanishing teacher signal leaves a flat quadratic expansion, not strict decrease.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n)
    (pole other : UnitSphere d) (r : Real) (hr : 0 < r) (hrpi : r < Real.pi/2)
    (s : Weight d) (hs : inner Real pole.val s = 0) (lambda p : Real) (hp : 2 < p) :
    let F := variationObjective O a (transverseCenterVariation pole r hr hrpi s) lambda p
      (antipodalMeasure other) (antipodalMeasure other)
    Asymptotics.IsLittleO (𝓝 (0 : Real)) (fun t => F t-F 0) (fun t => t^2) := by
  have he := transverse_center_objective_expansion O a hO pole r hr hrpi s hs lambda p hp (antipodalMeasure other)
  simpa [transverseTeacherSignal, finiteHermite_mean_antipodal O a hO other] using he
