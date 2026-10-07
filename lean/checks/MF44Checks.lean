import PaperFormalization.MatrixFactorization.FirstChaosFittingIdentity
import PaperFormalization.MatrixFactorization.HermiteTensorExplicit

open MeasureTheory ProbabilityTheory PaperFormalization.MatrixFactorization

-- Zeroth chaos retains its scalar unit even in zero spatial dimension.
example (z u : Weight 0) :
    inner Real (normalizedHermiteTensor 0 0 z).val (tensorPower 0 u) = 1 :=
  normalizedHermiteTensor_power_zero 0 z u

-- No trace is the identity at every tensor order, including zero.
example (d n : Nat) : tensorTraceTo d n n = ContinuousLinearMap.id Real _ :=
  tensorTraceTo_self d n

-- Nonunit observations retain the exact norm normalization.
example {d n : Nat} (z u : Weight d) (hu : u ≠ 0) :
    inner Real (normalizedHermiteTensor d n z).val (tensorPower n u) =
      ‖u‖ ^ n * normalizedHermite n (inner Real u z / ‖u‖) :=
  normalizedHermiteTensor_directional z u hu

example {d : Nat} (z : Weight d) :
    inner Real (normalizedHermiteTensor d 1 z).val (tensorPower 1 0) = 0 := by
  simp [normalizedHermiteTensor_power_one]

example {d : Nat} (z : Weight d) :
    inner Real (normalizedHermiteTensor d 2 z).val (tensorPower 2 0) = 0 := by
  simp [normalizedHermiteTensor_power_two]

-- The original Kronecker identity and the three printed low-order tensors.
example {d : Nat} (I : Fin 2 → Fin d) : tensorIdentity d I = if I 0 = I 1 then 1 else 0 :=
  tensorIdentity_apply I
example (z : Weight 0) : (normalizedHermiteTensor 0 0 z).val = tensorPower 0 z :=
  normalizedHermiteTensor_zero_eq 0 z
example {d : Nat} (z : Weight d) : (normalizedHermiteTensor d 1 z).val = tensorPower 1 z :=
  normalizedHermiteTensor_one_eq z
example {d : Nat} (z : Weight d) : (normalizedHermiteTensor d 2 z).val =
    (Real.sqrt 2)⁻¹ • (tensorPower 2 z - tensorIdentity d) := normalizedHermiteTensor_two_eq z

-- Arbitrary first tensors, rather than a supplied unit-direction subset.
example {d : Nat} (T : MomentTensor d 1) : ∃ u : Weight d, T = tensorPower 1 u :=
  exists_eq_tensorPower_one T
example {d : Nat} (z : Weight d) (A B : MomentTensor d 1) :
    inner Real (normalizedHermiteTensor d 1 z).val A *
      inner Real (normalizedHermiteTensor d 1 z).val B =
      normalizedChaosCoefficient 1 1 0 *
        inner Real (normalizedHermiteTensor d 2 z).val
          (tensorSymmetrize d 2 (tensorContractOrders d 1 1 0 (by decide) (by decide) A B)) +
      normalizedChaosCoefficient 1 1 1 *
        inner Real (normalizedHermiteTensor d 0 z).val
          (tensorSymmetrize d 0 (tensorContractOrders d 1 1 1 (by decide) (by decide) A B)) :=
  normalizedHermiteTensor_product_one z A B

-- Zero output coefficients are permitted in the actual matrix identity.
example {d h : Nat} (X Y : ActiveMomentSpace d {1}) (z : Weight d) :
    sourceChaosMatrixPolynomial {1} (fun _ => (0 : Weight h)) X Y z =
      outer (activeHermiteFeature {1} (fun _ => (0 : Weight h)) z X)
        (activeHermiteFeature {1} (fun _ => (0 : Weight h)) z Y) :=
  sourceChaosMatrixPolynomial_singleton_one _ X Y z

example {d h : Nat} (a : Nat → Weight h) (X Y : ActiveMomentSpace d {1}) (z : Weight d) :
    sourceChaosMatrixPolynomial {1} a X Y z =
      outer (activeHermiteFeature {1} a z X) (activeHermiteFeature {1} a z Y) :=
  sourceChaosMatrixPolynomial_singleton_one a X Y z

example {d h : Nat} (pole : UnitSphere d) (a : Nat → Weight h)
    (teacher : ActiveMomentSpace d {1}) (X : ActiveMomentCoordinates d {1}) :
    sourceCoefficientFitPolynomial {1} a teacher X = activeFittingPolynomial {1} a teacher X :=
  sourceCoefficientFitPolynomial_singleton_one_eq_actual pole a teacher X

example {d h : Nat} (pole : UnitSphere d) (a : Nat → Weight h)
    (teacher mu nu : Measure (UnitSphere d))
    [IsFiniteMeasure teacher] [IsFiniteMeasure mu] [IsFiniteMeasure nu] :
    sourceCoefficientFitPolynomial {1} a (rawActiveMoment {1} teacher) (activeMomentMap {1} mu nu) =
      fittingEnergy (stdGaussian (Weight d))
        (fun z => outer (meanFeature (finiteHermiteActivation {1} a) teacher z)
          (meanFeature (finiteHermiteActivation {1} a) teacher z))
        (meanFeature (finiteHermiteActivation {1} a) mu)
        (meanFeature (finiteHermiteActivation {1} a) nu) :=
  sourceCoefficientFitPolynomial_one_original_measures pole a teacher mu nu

example {d h : Nat} (pole : UnitSphere d) (a : Nat → Weight h)
    (teacher : Measure (UnitSphere d)) [IsFiniteMeasure teacher] :
    activeC2CurvatureConstant (sourceCoefficientFitPolynomial {1} a (rawActiveMoment {1} teacher)) 0 =
      activeGaussianFitCurvatureConstant {1} a teacher 0 :=
  sourceCoefficient_curvature_constant_one pole a teacher 0
