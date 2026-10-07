import PaperFormalization.MatrixFactorization.RawMomentRetractionJets
import PaperFormalization.MatrixFactorization.ActiveMomentCoordinates

/-! # MF35: actual raw moment derivatives in the symmetric active Hilbert space

Orthogonal projection is used only to construct Hilbert-valued derivatives.
Uniqueness of the ambient derivative proves that every component is the
original raw moment jet; projection does not alter the tensor data.
-/
open MeasureTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def rawActiveAlongRetract {d : Nat} (O : Finset Nat) (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (t : Real) : ActiveMomentSpace d O := rawActiveMoment O (mu.map (sphericalRetractFamily v hv t))

noncomputable def rawActiveRetractTensorFirst {d : Nat} (O : Finset Nat) (mu : Measure (UnitSphere d))
    (v : UnitSphere d → Weight d) (t : Real) : ActiveTensorBlock d O :=
  WithLp.toLp 2 (fun n : O => rawMomentAlongRetractFirst n.val mu v t)

noncomputable def rawActiveRetractTensorSecond {d : Nat} (O : Finset Nat) (mu : Measure (UnitSphere d))
    (v : UnitSphere d → Weight d) (t : Real) : ActiveTensorBlock d O :=
  WithLp.toLp 2 (fun n : O => rawMomentAlongRetractSecond n.val mu v t)

noncomputable def rawActiveRetractFirst {d : Nat} (O : Finset Nat) (mu : Measure (UnitSphere d))
    (v : UnitSphere d → Weight d) (t : Real) : ActiveMomentSpace d O :=
  (activeSymmetricSubmodule d O).orthogonalProjectionOnto (rawActiveRetractTensorFirst O mu v t)

noncomputable def rawActiveRetractSecond {d : Nat} (O : Finset Nat) (mu : Measure (UnitSphere d))
    (v : UnitSphere d → Weight d) (t : Real) : ActiveMomentSpace d O :=
  (activeSymmetricSubmodule d O).orthogonalProjectionOnto (rawActiveRetractTensorSecond O mu v t)

/-- The full tensor family differentiates componentwise in its L2 direct sum. -/
theorem rawActiveRetractTensor_hasDerivAt {d : Nat} (O : Finset Nat) (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (t : Real) :
    HasDerivAt (fun s => (rawActiveAlongRetract O mu v hv s).val) (rawActiveRetractTensorFirst O mu v t) t := by
  have h := (PiLp.hasFDerivAt_toLp (𝕜 := Real) 2 (fun n : O => rawMomentAlongRetract n.val mu v hv t)).comp_hasDerivAt t
    (hasDerivAt_pi.mpr (fun n : O => (rawMomentAlongRetract_variations (n := n.val) mu v hv hc t).1))
  convert h using 1 <;> rfl

theorem rawActiveRetractTensorFirst_hasDerivAt {d : Nat} (O : Finset Nat) (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (t : Real) :
    HasDerivAt (rawActiveRetractTensorFirst O mu v) (rawActiveRetractTensorSecond O mu v t) t := by
  have h := (PiLp.hasFDerivAt_toLp (𝕜 := Real) 2 (fun n : O => rawMomentAlongRetractFirst n.val mu v t)).comp_hasDerivAt t
    (hasDerivAt_pi.mpr (fun n : O => (rawMomentAlongRetract_variations (n := n.val) mu v hv hc t).2))
  convert h using 1 <;> rfl

/-- The derivative is taken in the actual symmetric source subspace. -/
theorem rawActiveAlongRetract_hasDerivAt {d : Nat} (O : Finset Nat) (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (t : Real) :
    HasDerivAt (rawActiveAlongRetract O mu v hv) (rawActiveRetractFirst O mu v t) t := by
  have h := (activeSymmetricSubmodule d O).orthogonalProjectionOnto.hasFDerivAt.comp_hasDerivAt t
    (rawActiveRetractTensor_hasDerivAt O mu v hv hc t)
  have he : (fun s => (activeSymmetricSubmodule d O).orthogonalProjectionOnto
      (rawActiveAlongRetract O mu v hv s).val) = rawActiveAlongRetract O mu v hv := by
    funext s
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
  rw [← he]
  exact h

/-- Projection leaves the actual first tensor derivative unchanged. -/
theorem rawActiveRetractFirst_val {d : Nat} (O : Finset Nat) (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (t : Real) :
    (rawActiveRetractFirst O mu v t).val = rawActiveRetractTensorFirst O mu v t := by
  have h := (activeSymmetricSubmodule d O).subtypeL.hasFDerivAt.comp_hasDerivAt t
    (rawActiveAlongRetract_hasDerivAt O mu v hv hc t)
  exact h.unique (rawActiveRetractTensor_hasDerivAt O mu v hv hc t)

theorem rawActiveRetractFirst_hasDerivAt {d : Nat} (O : Finset Nat) (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (t : Real) :
    HasDerivAt (rawActiveRetractFirst O mu v) (rawActiveRetractSecond O mu v t) t := by
  exact (activeSymmetricSubmodule d O).orthogonalProjectionOnto.hasFDerivAt.comp_hasDerivAt t
    (rawActiveRetractTensorFirst_hasDerivAt O mu v hv hc t)

/-- Projection also leaves the full second tensor derivative unchanged. -/
theorem rawActiveRetractSecond_val {d : Nat} (O : Finset Nat) (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (t : Real) :
    (rawActiveRetractSecond O mu v t).val = rawActiveRetractTensorSecond O mu v t := by
  have h := (activeSymmetricSubmodule d O).subtypeL.hasFDerivAt.comp_hasDerivAt t
    (rawActiveRetractFirst_hasDerivAt O mu v hv hc t)
  have he : (fun s => (rawActiveRetractFirst O mu v s).val) = rawActiveRetractTensorFirst O mu v :=
    funext (rawActiveRetractFirst_val O mu v hv hc)
  change HasDerivAt (fun s => (rawActiveRetractFirst O mu v s).val) (rawActiveRetractSecond O mu v t).val t at h
  rw [he] at h
  exact h.unique (rawActiveRetractTensorFirst_hasDerivAt O mu v hv hc t)

end PaperFormalization.MatrixFactorization
