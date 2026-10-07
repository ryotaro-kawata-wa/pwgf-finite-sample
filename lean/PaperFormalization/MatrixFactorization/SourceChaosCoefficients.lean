import PaperFormalization.MatrixFactorization.NormalizedChaosCoefficient
import PaperFormalization.MatrixFactorization.VectorHermiteParseval
import PaperFormalization.MatrixFactorization.ActiveHermiteFeature
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

/-! # MF43: the literal finite source matrix-tensor coefficients

Every term uses the source's actual matched-index contraction, normalized
coefficient, output outer product, and symmetric projection. This file
constructs the displayed coefficient polynomial without presupposing the
separate Hermite product identity that connects it to the original features.
-/
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

/-- The exact symmetric average, with its range recorded in the type. -/
noncomputable def tensorSymmetrizeRange (d n : Nat) :
    MomentTensor d n →ₗ[Real] SymmetricMomentTensor d n :=
  (tensorSymmetrize d n).toLinearMap.codRestrict (symmetricTensorSubmodule d n)
    (tensorSymmetrize_symmetric (d := d) (n := n))

/-- Attach the original output outer-product entries to a symmetric spatial
coefficient. The output norm is the L2 sum of all matrix-entry tensor norms. -/
noncomputable def tensorMatrixCoefficient {d h n : Nat} (a b : Weight h) :
    SymmetricMomentTensor d n →ₗ[Real] SymmetricHermiteCoefficient d (Fin h × Fin h) n where
  toFun T := WithLp.toLp 2 (fun ij => (a ij.1 * b ij.2) • T)
  map_add' T U := by
    apply PiLp.ext
    intro ij
    exact smul_add _ _ _
  map_smul' c T := by
    apply PiLp.ext
    intro ij
    exact smul_comm _ _ _

@[simp] theorem tensorMatrixCoefficient_apply {d h n : Nat} (a b : Weight h)
    (T : SymmetricMomentTensor d n) (ij : Fin h × Fin h) :
    tensorMatrixCoefficient a b T ij = (a ij.1 * b ij.2) • T := rfl

/-- The output outer product and spatial coefficient retain exactly their
original Hilbert--Schmidt norm factors. -/
theorem tensorMatrixCoefficient_norm_sq {d h n : Nat} (a b : Weight h)
    (T : SymmetricMomentTensor d n) :
    ‖tensorMatrixCoefficient a b T‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 * ‖T‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  simp only [tensorMatrixCoefficient_apply, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, EuclideanSpace.real_norm_sq_eq]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

/-- One summand of the printed coefficient, with all three tensor-order
conditions explicitly checked. -/
noncomputable def normalizedChaosTerm {d h n m r q : Nat}
    (hn : r ≤ n) (hm : r ≤ m) (hq : n + m - 2 * r = q) (a b : Weight h) :
    MomentTensor d n →ₗ[Real] MomentTensor d m →ₗ[Real]
      SymmetricHermiteCoefficient d (Fin h × Fin h) q :=
  normalizedChaosCoefficient n m r •
    ((tensorContractOrders d n m r hn hm).compr₂
      ((tensorMatrixCoefficient a b).comp ((tensorSymmetrizeRange d q).comp
        (tensorOrderEquiv (d := d) hq).toLinearEquiv.toLinearMap)))

/-- Every output entry is exactly the printed normalized scalar coefficient
times the symmetrized source contraction, in the original spatial norm. -/
theorem normalizedChaosTerm_apply {d h n m r q : Nat}
    (hn : r ≤ n) (hm : r ≤ m) (hq : n + m - 2 * r = q) (a b : Weight h)
    (A : MomentTensor d n) (B : MomentTensor d m) (ij : Fin h × Fin h) :
    (normalizedChaosTerm hn hm hq a b A B ij).val =
      (normalizedChaosCoefficient n m r * (a ij.1 * b ij.2)) •
        tensorSymmetrize d q
          (tensorOrderEquiv hq (tensorContractOrders d n m r hn hm A B)) := by
  simp [normalizedChaosTerm, tensorMatrixCoefficient, tensorSymmetrizeRange, smul_smul]

/-- Projection of the unchanged active raw tensor space onto one original
order. No coefficient weighting is applied to its norm. -/
noncomputable def activeTensorProjection {d : Nat} {O : Finset Nat} (n : O) :
    ActiveMomentSpace d O →ₗ[Real] MomentTensor d n.val :=
  ((PiLp.proj (𝕜 := Real) 2 (fun n : O => MomentTensor d n.val) n).comp
    (activeSymmetricSubmodule d O).subtypeL).toLinearMap

@[simp] theorem activeTensorProjection_apply {d : Nat} {O : Finset Nat}
    (n : O) (X : ActiveMomentSpace d O) : activeTensorProjection n X = X.val n := rfl

/-- The source's finite matrix-tensor coefficient at order `q`, as an actual
bilinear map of the two raw active moment blocks. -/
noncomputable def activeChaosCoefficient {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (q : Nat) :
    ActiveMomentSpace d O →ₗ[Real] ActiveMomentSpace d O →ₗ[Real]
      SymmetricHermiteCoefficient d (Fin h × Fin h) q := by
  classical
  exact ∑ n : O, ∑ m : O, ∑ r : Fin (min n.val m.val + 1),
    if hq : n.val + m.val - 2 * r.val = q then
      (normalizedChaosTerm (d := d)
        (by have := r.isLt; omega : r.val ≤ n.val)
        (by have := r.isLt; omega : r.val ≤ m.val) hq (a n.val) (a m.val)).compl₁₂
        (activeTensorProjection n) (activeTensorProjection m)
    else 0

/-- The literal source coefficient is smooth on the full ambient active
space, including all directions transverse to the antisymmetric branch. -/
theorem activeChaosCoefficient_contDiff {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (q : Nat) :
    ContDiff Real ⊤ (fun P : ActiveMomentSpace d O × ActiveMomentSpace d O =>
      activeChaosCoefficient O a q P.1 P.2) := by
  let B : ActiveMomentSpace d O →L[Real] ActiveMomentSpace d O →L[Real]
      SymmetricHermiteCoefficient d (Fin h × Fin h) q :=
    (activeChaosCoefficient (d := d) O a q).toContinuousBilinearMap
  exact B.isBoundedBilinearMap.contDiff

/-- A finite activation gives no coefficient above twice its actual maximal
active order. This includes the empty active set. -/
theorem activeChaosCoefficient_eq_zero_of_degree_lt {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (q : Nat) (hq : 2 * activationOrder O < q) :
    activeChaosCoefficient (d := d) O a q = 0 := by
  classical
  unfold activeChaosCoefficient
  apply Finset.sum_eq_zero
  intro n _
  apply Finset.sum_eq_zero
  intro m _
  apply Finset.sum_eq_zero
  intro r _
  have hn : n.val ≤ activationOrder O := Finset.le_sup (f := id) n.property
  have hm : m.val ≤ activationOrder O := Finset.le_sup (f := id) m.property
  exact dif_neg (by omega)

/-- Odd active inputs contribute only even output chaos degrees. -/
theorem activeChaosCoefficient_eq_zero_of_odd {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n) (q : Nat) (hq : Odd q) :
    activeChaosCoefficient (d := d) O a q = 0 := by
  classical
  unfold activeChaosCoefficient
  apply Finset.sum_eq_zero
  intro n _
  apply Finset.sum_eq_zero
  intro m _
  apply Finset.sum_eq_zero
  intro r _
  obtain ⟨i, hi⟩ := hO n.val n.property
  obtain ⟨j, hj⟩ := hO m.val m.property
  obtain ⟨k, hk⟩ := hq
  have hr := r.isLt
  exact dif_neg (by omega)

@[simp] theorem activeChaosCoefficient_empty {d h : Nat} (a : Nat → Weight h) (q : Nat) :
    activeChaosCoefficient (d := d) ∅ a q = 0 := by
  classical
  simp [activeChaosCoefficient]

end PaperFormalization.MatrixFactorization
