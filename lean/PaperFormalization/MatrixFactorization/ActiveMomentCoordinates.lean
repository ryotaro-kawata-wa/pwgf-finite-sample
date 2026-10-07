import PaperFormalization.MatrixFactorization.ActiveMomentHilbert

/-! # MF32: the Hilbert product of symmetric and antisymmetric active blocks

The product carries its L2 norm. In particular the change of variables has
exact squared norm factor 1/2, for both velocities and accelerations.
-/
open MeasureTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

abbrev ActiveMomentCoordinates (d : Nat) (O : Finset Nat) :=
  PiLp 2 (fun _ : Fin 2 => ActiveMomentSpace d O)

noncomputable def activeCoordinates {d : Nat} {O : Finset Nat}
    (X Y : ActiveMomentSpace d O) : ActiveMomentCoordinates d O :=
  WithLp.toLp 2 ![(1 / 2 : Real) • (X + Y), (1 / 2 : Real) • (X - Y)]

@[simp] theorem activeCoordinates_zero {d : Nat} {O : Finset Nat}
    (X Y : ActiveMomentSpace d O) :
    activeCoordinates X Y 0 = (1 / 2 : Real) • (X + Y) := rfl

@[simp] theorem activeCoordinates_one {d : Nat} {O : Finset Nat}
    (X Y : ActiveMomentSpace d O) :
    activeCoordinates X Y 1 = (1 / 2 : Real) • (X - Y) := rfl

/-- Exact source product normalization, with no sup-norm product hidden in it. -/
theorem activeCoordinates_norm_sq {d : Nat} {O : Finset Nat}
    (X Y : ActiveMomentSpace d O) :
    ‖activeCoordinates X Y‖ ^ 2 = (1 / 2 : Real) * (‖X‖ ^ 2 + ‖Y‖ ^ 2) := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  simp only [activeCoordinates_zero, activeCoordinates_one, norm_smul]
  rw [show ‖(1 / 2 : Real)‖ = 1 / 2 by norm_num]
  nlinarith [parallelogram_law_with_norm Real X Y]

/-- The same identity applies to each actual tensor velocity or acceleration. -/
theorem activeCoordinates_block_norm_sq {d : Nat} {O : Finset Nat}
    (X Y : ActiveMomentSpace d O) :
    ‖activeCoordinates X Y‖ ^ 2 =
      (1 / 2 : Real) * ∑ n : O, (‖X.val n‖ ^ 2 + ‖Y.val n‖ ^ 2) := by
  rw [activeCoordinates_norm_sq, activeMoment_norm_sq, activeMoment_norm_sq,
    Finset.sum_add_distrib]

noncomputable def activeMomentMap {d : Nat} (O : Finset Nat)
    (mu nu : Measure (UnitSphere d)) [IsFiniteMeasure mu] [IsFiniteMeasure nu] :
    ActiveMomentCoordinates d O := activeCoordinates (rawActiveMoment O mu) (rawActiveMoment O nu)

@[simp] theorem activeMomentMap_symmetric {d : Nat} (O : Finset Nat)
    (mu nu : Measure (UnitSphere d)) [IsFiniteMeasure mu] [IsFiniteMeasure nu] :
    activeMomentMap O mu nu 0 = symmetricActiveMoment O mu nu := rfl

@[simp] theorem activeMomentMap_antisymmetric {d : Nat} (O : Finset Nat)
    (mu nu : Measure (UnitSphere d)) [IsFiniteMeasure mu] [IsFiniteMeasure nu] :
    activeMomentMap O mu nu 1 = antisymmetricActiveMoment O mu nu := rfl

/-- The antisymmetric source ball is an actual finite-dimensional compact set. -/
theorem activeAntisymmetricBall_compact (d : Nat) (O : Finset Nat) (R : Real) :
    IsCompact ((fun A : ActiveMomentSpace d O =>
      (WithLp.toLp 2 ![0, A] : ActiveMomentCoordinates d O)) '' Metric.closedBall 0 R) := by
  apply (isCompact_closedBall (0 : ActiveMomentSpace d O) R).image
  fun_prop

/-- An empty active set has exactly zero raw norm; no positivity of its size is needed. -/
theorem activeMoment_empty_norm (d : Nat) (X : ActiveMomentSpace d ∅) : ‖X‖ = 0 := by
  have h := activeMoment_norm_sq X
  simp at h
  simp [h]

end PaperFormalization.MatrixFactorization
