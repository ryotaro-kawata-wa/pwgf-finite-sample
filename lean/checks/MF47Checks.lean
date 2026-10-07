import PaperFormalization.MatrixFactorization.SourceAnnularCurvature

open MeasureTheory ProbabilityTheory
open PaperFormalization.MatrixFactorization

-- The reconstruction covers empty, gapped, and non-odd finite degree sets.
example {d h : Nat} (a : Nat → Weight h) (X Y : ActiveMomentSpace d ∅) (z : Weight d) :
    sourceChaosMatrixPolynomial ∅ a X Y z = 0 := by
  rw [sourceChaosMatrixPolynomial_eq_outer]
  simp [activeHermiteFeature_apply, outer]
  rfl
example {d h : Nat} (O : Finset Nat) (X Y : ActiveMomentSpace d O) (z : Weight d) :
    sourceChaosMatrixPolynomial O (fun _ => (0 : Weight h)) X Y z = 0 := by
  rw [sourceChaosMatrixPolynomial_eq_outer]
  simp [activeHermiteFeature_apply, outer]
  rfl
example {d h : Nat} (a : Nat → Weight h) (X Y : ActiveMomentSpace d {3, 7}) (z : Weight d) :
    sourceChaosMatrixPolynomial {3, 7} a X Y z =
      outer (activeHermiteFeature {3, 7} a z X) (activeHermiteFeature {3, 7} a z Y) :=
  sourceChaosMatrixPolynomial_eq_outer _ _ _ _ _
example {d h : Nat} (a : Nat → Weight h) (X Y : ActiveMomentSpace d {0, 2}) (z : Weight d) :
    sourceChaosMatrixPolynomial {0, 2} a X Y z =
      outer (activeHermiteFeature {0, 2} a z X) (activeHermiteFeature {0, 2} a z Y) :=
  sourceChaosMatrixPolynomial_eq_outer _ _ _ _ _
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (Y : ActiveMomentSpace d O) (z : Weight d) :
    sourceChaosMatrixPolynomial O a 0 Y z = 0 := by
  rw [sourceChaosMatrixPolynomial_eq_outer]
  simp [outer]
  rfl
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (X : ActiveMomentSpace d O) (z : Weight d) :
    sourceChaosMatrixPolynomial O a X 0 z = 0 := by
  rw [sourceChaosMatrixPolynomial_eq_outer]
  simp [outer]
  rfl

-- The equality is ambient and retains a zero teacher or student block.
example {d h : Nat} (pole : UnitSphere d) (O : Finset Nat) (a : Nat → Weight h)
    (X : ActiveMomentCoordinates d O) :
    sourceCoefficientFitPolynomial O a 0 X = activeFittingPolynomial O a 0 X :=
  sourceCoefficientFitPolynomial_eq_actual pole O a 0 X
example {d h : Nat} (pole : UnitSphere d) (O : Finset Nat) (a : Nat → Weight h)
    (teacher : ActiveMomentSpace d O) :
    sourceCoefficientFitPolynomial O a teacher 0 = activeFittingPolynomial O a teacher 0 :=
  sourceCoefficientFitPolynomial_eq_actual pole O a teacher 0
example {d h : Nat} (pole : UnitSphere d) (O : Finset Nat) (a : Nat → Weight h)
    (teacher : ActiveMomentSpace d O) :
    sourceCoefficientFitPolynomial O a teacher = activeFittingPolynomial O a teacher :=
  sourceCoefficientFitPolynomial_eq_actual_fun pole O a teacher
example {d h : Nat} (pole : UnitSphere d) (O : Finset Nat) (a : Nat → Weight h)
    (teacher : Measure (UnitSphere d)) [IsFiniteMeasure teacher] :
    sourceFitCurvatureConstant O a teacher 0 = activeGaussianFitCurvatureConstant O a teacher 0 :=
  sourceFitCurvatureConstant_eq_actual pole O a teacher 0
example {d h : Nat} (pole : UnitSphere d) (O : Finset Nat) (a : Nat → Weight h)
    (teacher : Measure (UnitSphere d)) [IsFiniteMeasure teacher] :
    0 ≤ sourceFitCurvatureConstant O a teacher 0 :=
  sourceFitCurvatureConstant_nonneg pole O a teacher 0 (by norm_num)
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (teacher : ActiveMomentSpace d O) :
    sourceCoefficientFitPolynomial O a teacher (WithLp.toLp 2 ![teacher, 0]) = 0 :=
  sourceCoefficientFitPolynomial_teacher O a teacher

-- The original Gaussian residual is truly integrable, with no probability
-- or nonzero-output restriction inserted into these finite-measure identities.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (X Y U V : ActiveMomentSpace d O) :
    Integrable (fun z : Weight d =>
      ‖outer (activeHermiteFeature O a z X) (activeHermiteFeature O a z Y) -
        outer (activeHermiteFeature O a z U) (activeHermiteFeature O a z V)‖ ^ 2)
      (stdGaussian (Weight d)) := by
  simpa only [sourceChaosMatrixPolynomial_eq_outer] using
    sourceChaosMatrixPolynomial_residual_integrable O a X Y U V
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (P : SphericalVariation d)
    (teacher : Measure (UnitSphere d)) [IsFiniteMeasure teacher] :
    sourceCoefficientFitPolynomial O a (rawActiveMoment O teacher)
      (activeMomentMapAlongRetract O P.measure P.velocity P.tangent (-1)) =
      variationRetractedFitting O a P teacher teacher (-1) :=
  sourceCoefficientFitPolynomial_along_retract O a P teacher (-1)
example {d h : Nat} (pole : UnitSphere d) (O : Finset Nat) (a : Nat → Weight h)
    (teacher : Measure (UnitSphere d)) [IsFiniteMeasure teacher] :
    sourceFitCurvatureConstant O a teacher (Real.sqrt (O.card : Real)) =
      activeGaussianFitCurvatureConstant O a teacher (Real.sqrt (O.card : Real)) :=
  sourceFitCurvatureConstant_eq_actual pole O a teacher _
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (P : SphericalVariation d) (lambda zeta : Real)
    (teacher : Measure (UnitSphere d)) [IsFiniteMeasure teacher]
    (hE : variationEnergy P = 0) :
    (lambda * sphericalRadialWeight P.radius * zeta ^ ((5 : Real)/2 - 2) -
      sourceFitCurvatureConstant O a teacher 0) * variationEnergy P = 0 := by rw [hE, mul_zero]
