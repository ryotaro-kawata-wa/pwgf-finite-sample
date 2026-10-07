import PaperFormalization.MatrixFactorization.SphericalObjectiveTeacher

/-! MF05 boundary diagnostics for the literal objective, center, and teacher.
These include nonintegral p, zero activation, vanishing teacher signal, and
signed time. The verification receipt records their actual execution.
-/
open MeasureTheory ProbabilityTheory
open PaperFormalization.MatrixFactorization
set_option autoImplicit false

example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (pole : UnitSphere d)
    (p : Real) (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d)) :
    modelObjective O a pole 0 p mu1 mu2 teacher1 teacher2 = modelFitting O a mu1 mu2 teacher1 teacher2 := by
  simp [modelObjective, metricRegularizer]

-- The teacher's objective is generally its nonzero regularization cost.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (pole : UnitSphere d)
    (lambda p : Real) (teacher1 teacher2 : Measure (UnitSphere d)) :
    modelObjective O a pole lambda p teacher1 teacher2 teacher1 teacher2 =
      metricRegularizer pole lambda p teacher1 teacher2 := by simp [modelObjective]

example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (P : SphericalVariation d)
    (p : Real) (teacher1 teacher2 : Measure (UnitSphere d)) (t : Real) :
    variationObjective O a P 0 p teacher1 teacher2 t = variationFitting O a P teacher1 teacher2 t := by
  simp [variationObjective_split, variationRegularizer]

-- Center flatness retains a real, nonintegral exponent between two and three.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (hO : ∀ n, n ∈ O → Odd n) (P : SphericalVariation d) (lambda : Real)
    (hZ : variationTransport P 0 = 0) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] :
    HasDerivAt (variationObjective O a P lambda (5/2) teacher teacher) 0 0 :=
  (spherical_objective_center_variations O a hO P lambda (5/2) (by norm_num) hZ teacher teacher).1

-- The same-density assertion is an equality of actual pushed measures.
example {d : Nat} (P : SphericalVariation d) (hZ : variationTransport P 0 = 0)
    (hv : P.velocity 1 = P.velocity 0) :
    (P.measure 1).map (sphericalExpFamily (P.velocity 1) (P.tangent 1) (-7)) =
      (P.measure 0).map (sphericalExpFamily (P.velocity 0) (P.tangent 0) (-7)) :=
  center_same_velocity_pushforwards P hZ hv (-7)

-- A teacher with zero odd feature has no strict center escape signal.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (hO : ∀ n, n ∈ O → Odd n) (P : SphericalVariation d) (pole : UnitSphere d) (z : Weight d) :
    centerFittingPairing O a P (antipodalMeasure pole) (antipodalMeasure pole) z = 0 := by
  simp [centerFittingPairing, teacherOutput, finiteHermite_mean_antipodal O a hO pole]

example {d h : Nat} (a : Nat → Weight h) (P : SphericalVariation d)
    (lambda p : Real) (hp : 2 < p) (hZ : variationTransport P 0 = 0)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    HasDerivAt (deriv (variationObjective ∅ a P lambda p teacher teacher)) 0 0 := by
  have hd := (spherical_objective_center_variations ∅ a (by simp) P lambda p hp hZ teacher teacher).2
  apply hd.congr_deriv
  simp [centerFittingPairing, teacherOutput, meanFeature, finiteHermiteActivation]

-- Empty activation does not remove the metric curvature at positive transport.
example {d h : Nat} (a : Nat → Weight h) (P : SphericalVariation d)
    (lambda : Real) (hlambda : 0 < lambda) (hZ : 0 < variationTransport P 0)
    (hE : 0 < variationEnergy P) :
    0 < deriv (deriv (variationObjective ∅ a P lambda (5/2) (P.measure 0) (P.measure 1))) 0 :=
  spherical_objective_teacher_second_pos ∅ a P lambda (5/2) hlambda (by norm_num) hZ hE
