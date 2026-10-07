import PaperFormalization.MatrixFactorization.SourceChaosFitPolynomial

open MeasureTheory ProbabilityTheory PaperFormalization.MatrixFactorization

example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (q : Nat) :
    ContDiff Real ⊤ (fun P : ActiveMomentSpace d O × ActiveMomentSpace d O =>
      activeChaosCoefficient O a q P.1 P.2) := activeChaosCoefficient_contDiff O a q

example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (q : Nat)
    (hq : 2 * activationOrder O < q) : activeChaosCoefficient (d := d) O a q = 0 :=
  activeChaosCoefficient_eq_zero_of_degree_lt O a q hq

example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (hO : ∀ n ∈ O, Odd n) : activeChaosCoefficient (d := d) O a 1 = 0 :=
  activeChaosCoefficient_eq_zero_of_odd O a hO 1 (by decide)

example {d h : Nat} (a : Nat → Weight h) (q : Nat) :
    activeChaosCoefficient (d := d) ∅ a q = 0 := by simp

example {d h n : Nat} (a b : Weight h) (T : SymmetricMomentTensor d n) :
    ‖tensorMatrixCoefficient a b T‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 * ‖T‖ ^ 2 :=
  tensorMatrixCoefficient_norm_sq a b T

example {d : Nat} (T : SymmetricMomentTensor d 0) (a b : Weight 0) :
    ‖tensorMatrixCoefficient a b T‖ ^ 2 = 0 := by
  rw [tensorMatrixCoefficient_norm_sq]
  simp [EuclideanSpace.real_norm_sq_eq]

example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (teacher : ActiveMomentSpace d O) :
    ContDiff Real ⊤ (sourceCoefficientFitPolynomial O a teacher) :=
  sourceCoefficientFitPolynomial_contDiff O a teacher

example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (teacher : ActiveMomentSpace d O) (X : ActiveMomentCoordinates d O) :
    0 ≤ sourceCoefficientFitPolynomial O a teacher X :=
  sourceCoefficientFitPolynomial_nonneg O a teacher X

example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (teacher : ActiveMomentSpace d O) :
    sourceCoefficientFitPolynomial O a teacher (WithLp.toLp 2 ![teacher, 0]) = 0 :=
  sourceCoefficientFitPolynomial_teacher O a teacher

example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (X : ActiveMomentCoordinates d O)
    (q : Nat) (hq : q ∉ activeChaosDegrees O) : sourceActiveCoefficient O a q X = 0 :=
  sourceActiveCoefficient_eq_zero_of_not_mem O a q hq X

example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (X Y U V : ActiveMomentSpace d O) :
    Integrable (fun z : Weight d =>
      ‖sourceChaosMatrixPolynomial O a X Y z - sourceChaosMatrixPolynomial O a U V z‖ ^ 2)
      (stdGaussian (Weight d)) := sourceChaosMatrixPolynomial_residual_integrable O a X Y U V

example {d h : Nat} (pole : UnitSphere d) (O : Finset Nat) (a : Nat → Weight h)
    (teacher : ActiveMomentSpace d O) (X : ActiveMomentCoordinates d O) :
    sourceCoefficientFitPolynomial O a teacher X =
      (1 / 2 : Real) * ∫ z : Weight d,
        ‖sourceChaosMatrixPolynomial O a (X 0 + X 1) (X 0 - X 1) z -
          sourceChaosMatrixPolynomial O a teacher teacher z‖ ^ 2 ∂stdGaussian (Weight d) :=
  sourceCoefficientFitPolynomial_parseval pole O a teacher X
