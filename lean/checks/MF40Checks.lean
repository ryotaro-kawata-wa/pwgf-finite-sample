import PaperFormalization.MatrixFactorization.UnitTensorPowerSpan
open PaperFormalization.MatrixFactorization
set_option synthInstance.maxHeartbeats 80000

-- The actual average handles zero tensors, arbitrary nonsymmetric inputs, and slot cancellation.
example (d n : Nat) : tensorSymmetrize d n 0 = 0 := map_zero _
example {d n : Nat} (T : MomentTensor d n) :
    tensorSymmetrize d n (tensorSymmetrize d n T) = tensorSymmetrize d n T :=
  tensorSymmetrize_idempotent T
example {d n : Nat} (T : MomentTensor d n) (e : Equiv.Perm (Fin n)) :
    tensorSymmetrize d n (T - tensorPermute e T) = 0 := by
  rw [map_sub, tensorSymmetrize_permute, sub_self]
example {d n : Nat} (T : MomentTensor d n) : ‖tensorSymmetrize d n T‖ ≤ ‖T‖ :=
  tensorSymmetrize_norm_le T

-- Empty tensor products retain their unit scalar, including spatial dimension zero.
example : Submodule.span Real (Set.range (@symmetricTensorPower 0 0)) = ⊤ :=
  symmetricTensorPower_span 0 0
example (d n : Nat) : tensorPower (n + 1) (0 : Weight d) = 0 := tensorPower_zero_succ d n
example {d : Nat} (w : Weight d) : tensorPower 3 ((-1 : Real) • w) = -tensorPower 3 w := by
  rw [tensorPower_smul]
  norm_num
example {d : Nat} (w : Weight d) : tensorPower 0 ((0 : Real) • w) = tensorPower 0 w := by
  rw [tensorPower_smul, pow_zero, one_smul]

-- Full tensor separation does not need positive spatial dimension.
example {n : Nat} (T : MomentTensor 0 n) (hT : T ∈ symmetricTensorSubmodule 0 n)
    (hz : ∀ w : Weight 0, inner Real T (tensorPower n w) = 0) : T = 0 :=
  symmetricTensor_eq_zero_of_power_inner_zero T hT hz

-- Unit-power spanning explicitly keeps a sphere point for the degree-zero case.
example {d : Nat} (pole : UnitSphere d) :
    Submodule.span Real (Set.range (fun w : UnitSphere d => symmetricTensorPower 0 w.val)) = ⊤ :=
  symmetricUnitTensorPower_span pole 0
example {d : Nat} (pole : UnitSphere d) :
    Submodule.span Real (Set.range (fun w : UnitSphere d => symmetricTensorPower 5 w.val)) = ⊤ :=
  symmetricUnitTensorPower_span pole 5
example {d n : Nat} (pole : UnitSphere d) (L : SymmetricMomentTensor d n →ₗ[Real] Real)
    (hz : ∀ w : UnitSphere d, L (symmetricTensorPower n w.val) = 0) : L = 0 :=
  symmetricTensor_linear_ext_on_units pole L 0 hz
