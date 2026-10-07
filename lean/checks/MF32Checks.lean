import PaperFormalization.MatrixFactorization.ActiveMomentCoordinates

open MeasureTheory
open PaperFormalization.MatrixFactorization

-- The zeroth order retains its probability normalization and unit tensor norm.
example {d : Nat} (w : UnitSphere d) : ‖tensorPower 0 w.val‖ = 1 := tensorPower_unit_norm w
example {d : Nat} (w : Weight d) : ‖tensorPower 0 w‖ = 1 := by simp [tensorPower_norm]
example {d : Nat} (w : Weight d) : ‖tensorPower 1 w‖ = ‖w‖ := by simp [tensorPower_norm]
example {d : Nat} (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] :
    ‖rawMoment mu 0‖ ≤ 1 := rawMoment_norm_le_one mu 0

-- Atomic antipodal measures and empty active sets require no extra hypotheses.
example {d : Nat} (a : UnitSphere d) (n : Nat) :
    ‖rawMoment (antipodalMeasure a) n‖ ≤ 1 := rawMoment_norm_le_one _ n
example {d : Nat} (O : Finset Nat) (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu] :
    antisymmetricActiveMoment O mu mu = 0 := antisymmetricActiveMoment_diagonal O mu
example {d : Nat} (X : ActiveMomentSpace d ∅) : ‖X‖ = 0 := activeMoment_empty_norm d X
example {d : Nat} (mu nu : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu] : ‖antisymmetricActiveMoment ∅ mu nu‖ ≤ 0 := by
  rw [activeMoment_empty_norm]

-- The inherited Hilbert norm includes both components with the exact factor.
example {d : Nat} {O : Finset Nat} (X Y : ActiveMomentSpace d O) :
    ‖activeCoordinates X Y‖ ^ 2 = (1 / 2 : Real) * (‖X‖ ^ 2 + ‖Y‖ ^ 2) :=
  activeCoordinates_norm_sq X Y
example {d : Nat} {O : Finset Nat} (X : ActiveMomentSpace d O) :
    ‖activeCoordinates X X‖ ^ 2 = ‖X‖ ^ 2 := by rw [activeCoordinates_norm_sq]; ring
example {d : Nat} {O : Finset Nat} (X : ActiveMomentSpace d O) :
    ‖activeCoordinates X (-X)‖ ^ 2 = ‖X‖ ^ 2 := by rw [activeCoordinates_norm_sq, norm_neg]; ring
example (d : Nat) (O : Finset Nat) :
    IsCompact ((fun A : ActiveMomentSpace d O =>
      (WithLp.toLp 2 ![0, A] : ActiveMomentCoordinates d O)) '' Metric.closedBall 0 0) :=
  activeAntisymmetricBall_compact d O 0

-- The finite raw map reconstructs tensors, with explicit oddness for the branch.
example {d : Nat} (O : Finset Nat) (mu nu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] [IsFiniteMeasure nu] :
    activeMomentMap O mu nu 0 + activeMomentMap O mu nu 1 = rawActiveMoment O mu :=
  activeMoment_left_reconstruction O mu nu
example {d : Nat} (O : Finset Nat) (hO : ∀ n ∈ O, Odd n)
    (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] :
    activeMomentMap O mu (reflectedMeasure mu) 0 = 0 := symmetricActiveMoment_reflected O hO mu
example {d : Nat} (O : Finset Nat) (hO : ∀ n ∈ O, Odd n) (a : UnitSphere d) :
    rawActiveMoment O (antipodalMeasure a) = 0 := rawActiveMoment_antipodal O hO a
example {d : Nat} (O : Finset Nat) (mu nu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    ‖antisymmetricActiveMoment O mu nu‖ ^ 2 ≤ (O.card : Real) :=
  antisymmetricActiveMoment_norm_sq_le O mu nu
