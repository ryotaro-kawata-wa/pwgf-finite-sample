import PaperFormalization.MatrixFactorization.TensorHermiteEvaluation
import PaperFormalization.MatrixFactorization.ActiveMomentCoordinates

/-! # MF37: the literal mean feature from the source active raw moments

All lower Hermite terms use contractions of the original active-order tensor.
The resulting feature is a continuous linear map on the unchanged symmetric
Hilbert space. Its equality to the original sphere integral is proved below.
-/
open MeasureTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

/-- A continuous linear functional commutes with the original Bochner moment integral. -/
theorem tensorHermiteEvaluation_rawMoment {d n : Nat} (z : Weight d)
    (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu] :
    tensorHermiteEvaluation d n z (rawMoment mu n) =
      ∫ w : UnitSphere d, normalizedHermite n (inner Real w.val z) ∂mu := by
  rw [rawMoment, ← (tensorHermiteEvaluation d n z).integral_comp_comm (rawMoment_integrable mu n)]
  simp only [tensorHermiteEvaluation_unit]

noncomputable def activeHermiteFeature {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (z : Weight d) : ActiveMomentSpace d O →L[Real] Weight h :=
  ∑ n : O,
    ((tensorHermiteEvaluation d n.val z).comp
      ((PiLp.proj (𝕜 := Real) 2 (fun n : O => MomentTensor d n.val) n).comp
        (activeSymmetricSubmodule d O).subtypeL)).smulRight (a n.val)

@[simp] theorem activeHermiteFeature_apply {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (z : Weight d) (X : ActiveMomentSpace d O) :
    activeHermiteFeature O a z X =
      ∑ n : O, tensorHermiteEvaluation d n.val z (X.val n) • a n.val := by
  simp [activeHermiteFeature]

/-- This is an identity of the original features, not a new definition of the model. -/
theorem activeHermiteFeature_rawMoment {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (z : Weight d) (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu] :
    activeHermiteFeature O a z (rawActiveMoment O mu) =
      meanFeature (finiteHermiteActivation O a) mu z := by
  classical
  rw [activeHermiteFeature_apply]
  simp only [rawActiveMoment_apply, tensorHermiteEvaluation_rawMoment]
  unfold meanFeature finiteHermiteActivation
  have hi (n : Nat) : Integrable (fun w : UnitSphere d =>
      normalizedHermite n (inner Real w.val z) • a n) mu :=
    sphere_integrable mu _ (((normalizedHermite_continuous n).comp
      (f := fun w : UnitSphere d => inner Real w.val z) (by fun_prop)).smul continuous_const)
  rw [integral_finsetSum O (fun n _ => hi n)]
  simp only [integral_smul_const]
  exact Finset.sum_coe_sort O (fun n => (∫ w : UnitSphere d,
    normalizedHermite n (inner Real w.val z) ∂mu) • a n)

/-- At every actual active tensor, the Gaussian-input feature is smooth. -/
theorem activeHermiteFeature_contDiff_input {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (X : ActiveMomentSpace d O) :
    ContDiff Real ⊤ (fun z : Weight d => activeHermiteFeature O a z X) := by
  classical
  simp only [activeHermiteFeature_apply]
  apply ContDiff.sum
  intro n hn
  exact ((tensorHermiteEvaluation_contDiff d n.val).comp
    (contDiff_const.prodMk contDiff_id)).smul contDiff_const

/-- The two source blocks reconstruct the first original feature. -/
theorem activeHermiteFeature_left {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu nu : Measure (UnitSphere d)) [IsFiniteMeasure mu] [IsFiniteMeasure nu] (z : Weight d) :
    activeHermiteFeature O a z
      (activeMomentMap O mu nu 0 + activeMomentMap O mu nu 1) =
      meanFeature (finiteHermiteActivation O a) mu z := by
  rw [activeMomentMap_symmetric, activeMomentMap_antisymmetric, activeMoment_left_reconstruction]
  exact activeHermiteFeature_rawMoment O a z mu

/-- The second source block uses S-A with the original sign. -/
theorem activeHermiteFeature_right {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu nu : Measure (UnitSphere d)) [IsFiniteMeasure mu] [IsFiniteMeasure nu] (z : Weight d) :
    activeHermiteFeature O a z
      (activeMomentMap O mu nu 0 - activeMomentMap O mu nu 1) =
      meanFeature (finiteHermiteActivation O a) nu z := by
  rw [activeMomentMap_symmetric, activeMomentMap_antisymmetric, activeMoment_right_reconstruction]
  exact activeHermiteFeature_rawMoment O a z nu

end PaperFormalization.MatrixFactorization
