import PaperFormalization.MatrixFactorization.TensorHilbertNorm

/-! # MF32: the source active symmetric tensor Hilbert space

We use an L2 direct sum of full Hilbert--Schmidt tensor blocks and then its
permutation-invariant subspace. The induced norm is precisely the manuscript's
unweighted raw norm, rather than the sup norm on ordinary function spaces.
-/
open MeasureTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

abbrev ActiveTensorBlock (d : Nat) (O : Finset Nat) :=
  PiLp 2 (fun n : O => MomentTensor d n.val)

/-- Symmetry is a linear constraint on full tensor coordinates. -/
def activeSymmetricSubmodule (d : Nat) (O : Finset Nat) :
    Submodule Real (ActiveTensorBlock d O) where
  carrier := {X | ∀ (n : O) (I : Fin n.val → Fin d) (e : Equiv.Perm (Fin n.val)),
    X n (I.comp e) = X n I}
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    intro n I e
    rfl
  add_mem' := by
    intro X Y hX hY n I e
    change X n (I.comp e) + Y n (I.comp e) = X n I + Y n I
    rw [hX n I e, hY n I e]
  smul_mem' := by
    intro c X hX n I e
    change c * X n (I.comp e) = c * X n I
    rw [hX n I e]

abbrev ActiveMomentSpace (d : Nat) (O : Finset Nat) :=
  activeSymmetricSubmodule d O

/-- The raw source norm is the sum of the full tensor Hilbert--Schmidt squares. -/
theorem activeMoment_norm_sq {d : Nat} {O : Finset Nat} (X : ActiveMomentSpace d O) :
    ‖X‖ ^ 2 = ∑ n : O, ‖X.val n‖ ^ 2 := by
  exact PiLp.norm_sq_eq_of_L2 _ X.val

/-- Symmetry is part of the type, and is preserved without reweighting. -/
theorem activeMoment_permutation {d : Nat} {O : Finset Nat}
    (X : ActiveMomentSpace d O) (n : O) (I : Fin n.val → Fin d)
    (e : Equiv.Perm (Fin n.val)) : X.val n (I.comp e) = X.val n I :=
  X.property n I e

noncomputable def rawActiveMoment {d : Nat} (O : Finset Nat)
    (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu] : ActiveMomentSpace d O :=
  ⟨WithLp.toLp 2 (fun n : O => rawMoment mu n.val),
    fun n I e => rawMoment_permutation mu I e⟩

@[simp] theorem rawActiveMoment_apply {d : Nat} (O : Finset Nat)
    (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu] (n : O) :
    (rawActiveMoment O mu).val n = rawMoment mu n.val := rfl

noncomputable def symmetricActiveMoment {d : Nat} (O : Finset Nat)
    (mu nu : Measure (UnitSphere d)) [IsFiniteMeasure mu] [IsFiniteMeasure nu] :
    ActiveMomentSpace d O := (1 / 2 : Real) • (rawActiveMoment O mu + rawActiveMoment O nu)

noncomputable def antisymmetricActiveMoment {d : Nat} (O : Finset Nat)
    (mu nu : Measure (UnitSphere d)) [IsFiniteMeasure mu] [IsFiniteMeasure nu] :
    ActiveMomentSpace d O := (1 / 2 : Real) • (rawActiveMoment O mu - rawActiveMoment O nu)

@[simp] theorem symmetricActiveMoment_apply {d : Nat} (O : Finset Nat)
    (mu nu : Measure (UnitSphere d)) [IsFiniteMeasure mu] [IsFiniteMeasure nu] (n : O) :
    (symmetricActiveMoment O mu nu).val n = symmetricMoment mu nu n.val := rfl

@[simp] theorem antisymmetricActiveMoment_apply {d : Nat} (O : Finset Nat)
    (mu nu : Measure (UnitSphere d)) [IsFiniteMeasure mu] [IsFiniteMeasure nu] (n : O) :
    (antisymmetricActiveMoment O mu nu).val n = antisymmetricMoment mu nu n.val := rfl

/-- The finite moment map reconstructs the active tensors, not the measures. -/
theorem activeMoment_left_reconstruction {d : Nat} (O : Finset Nat)
    (mu nu : Measure (UnitSphere d)) [IsFiniteMeasure mu] [IsFiniteMeasure nu] :
    symmetricActiveMoment O mu nu + antisymmetricActiveMoment O mu nu = rawActiveMoment O mu := by
  apply Subtype.ext
  apply PiLp.ext
  intro n
  exact rawMoment_left_reconstruction mu nu n.val

theorem activeMoment_right_reconstruction {d : Nat} (O : Finset Nat)
    (mu nu : Measure (UnitSphere d)) [IsFiniteMeasure mu] [IsFiniteMeasure nu] :
    symmetricActiveMoment O mu nu - antisymmetricActiveMoment O mu nu = rawActiveMoment O nu := by
  apply Subtype.ext
  apply PiLp.ext
  intro n
  exact rawMoment_right_reconstruction mu nu n.val

/-- The universal active radius uses the cardinality without dimension loss. -/
theorem antisymmetricActiveMoment_norm_sq_le {d : Nat} (O : Finset Nat)
    (mu nu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    ‖antisymmetricActiveMoment O mu nu‖ ^ 2 ≤ (O.card : Real) := by
  rw [activeMoment_norm_sq]
  calc
    (∑ n : O, ‖(antisymmetricActiveMoment O mu nu).val n‖ ^ 2) ≤ ∑ _n : O, (1 : Real) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [antisymmetricActiveMoment_apply]
      have h := antisymmetricMoment_norm_le_one mu nu n.val
      nlinarith [norm_nonneg (antisymmetricMoment mu nu n.val)]
    _ = (O.card : Real) := by simp

/-- This is the explicit radius offered in the source curvature lemma. -/
theorem antisymmetricActiveMoment_norm_le {d : Nat} (O : Finset Nat)
    (mu nu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    ‖antisymmetricActiveMoment O mu nu‖ ≤ Real.sqrt (O.card : Real) := by
  exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    (antisymmetricActiveMoment_norm_sq_le O mu nu)

/-- The reflected branch has vanishing symmetric active coordinates. -/
theorem symmetricActiveMoment_reflected {d : Nat} (O : Finset Nat)
    (hO : ∀ n ∈ O, Odd n) (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] :
    symmetricActiveMoment O mu (reflectedMeasure mu) = 0 := by
  apply Subtype.ext
  apply PiLp.ext
  intro n
  exact reflected_branch_symmetric_zero mu n.val (hO n.val n.property)

/-- Equal laws give zero antisymmetric coordinates at every degree. -/
theorem antisymmetricActiveMoment_diagonal {d : Nat} (O : Finset Nat)
    (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu] :
    antisymmetricActiveMoment O mu mu = 0 := by
  simp [antisymmetricActiveMoment]

/-- The odd active target is the source origin in the symmetric Hilbert space. -/
theorem rawActiveMoment_antipodal {d : Nat} (O : Finset Nat)
    (hO : ∀ n ∈ O, Odd n) (a : UnitSphere d) :
    rawActiveMoment O (antipodalMeasure a) = 0 := by
  apply Subtype.ext
  apply PiLp.ext
  intro n
  exact rawMoment_antipodal_odd a n.val (hO n.val n.property)

end PaperFormalization.MatrixFactorization
