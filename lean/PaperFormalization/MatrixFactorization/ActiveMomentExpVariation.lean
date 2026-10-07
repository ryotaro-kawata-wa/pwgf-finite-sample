import PaperFormalization.MatrixFactorization.RawMomentJetNorms
import PaperFormalization.MatrixFactorization.ActiveMomentCoordinates

/-! # MF34: actual raw moment derivatives in the symmetric active Hilbert space

Orthogonal projection is used only to construct Hilbert-valued derivatives.
Uniqueness of the ambient derivative proves that every component is the
original raw moment jet; projection does not alter the tensor data.
-/
open MeasureTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def rawActiveAlongExp {d : Nat} (O : Finset Nat) (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (t : Real) : ActiveMomentSpace d O := rawActiveMoment O (mu.map (sphericalExpFamily v hv t))

noncomputable def rawActiveTensorFirst {d : Nat} (O : Finset Nat) (mu : Measure (UnitSphere d))
    (v : UnitSphere d → Weight d) (t : Real) : ActiveTensorBlock d O :=
  WithLp.toLp 2 (fun n : O => rawMomentAlongExpFirst n.val mu v t)

noncomputable def rawActiveTensorSecond {d : Nat} (O : Finset Nat) (mu : Measure (UnitSphere d))
    (v : UnitSphere d → Weight d) (t : Real) : ActiveTensorBlock d O :=
  WithLp.toLp 2 (fun n : O => rawMomentAlongExpSecond n.val mu v t)

noncomputable def rawActiveFirst {d : Nat} (O : Finset Nat) (mu : Measure (UnitSphere d))
    (v : UnitSphere d → Weight d) (t : Real) : ActiveMomentSpace d O :=
  (activeSymmetricSubmodule d O).orthogonalProjectionOnto (rawActiveTensorFirst O mu v t)

noncomputable def rawActiveSecond {d : Nat} (O : Finset Nat) (mu : Measure (UnitSphere d))
    (v : UnitSphere d → Weight d) (t : Real) : ActiveMomentSpace d O :=
  (activeSymmetricSubmodule d O).orthogonalProjectionOnto (rawActiveTensorSecond O mu v t)

/-- The full tensor family differentiates componentwise in its L2 direct sum. -/
theorem rawActiveTensor_hasDerivAt {d : Nat} (O : Finset Nat) (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (t : Real) :
    HasDerivAt (fun s => (rawActiveAlongExp O mu v hv s).val) (rawActiveTensorFirst O mu v t) t := by
  have h := (PiLp.hasFDerivAt_toLp (𝕜 := Real) 2 (fun n : O => rawMomentAlongExp n.val mu v hv t)).comp_hasDerivAt t
    (hasDerivAt_pi.mpr (fun n : O => (rawMomentAlongExp_variations (n := n.val) mu v hv hc t).1))
  convert h using 1 <;> rfl

theorem rawActiveTensorFirst_hasDerivAt {d : Nat} (O : Finset Nat) (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (t : Real) :
    HasDerivAt (rawActiveTensorFirst O mu v) (rawActiveTensorSecond O mu v t) t := by
  have h := (PiLp.hasFDerivAt_toLp (𝕜 := Real) 2 (fun n : O => rawMomentAlongExpFirst n.val mu v t)).comp_hasDerivAt t
    (hasDerivAt_pi.mpr (fun n : O => (rawMomentAlongExp_variations (n := n.val) mu v hv hc t).2))
  convert h using 1 <;> rfl

/-- The derivative is taken in the actual symmetric source subspace. -/
theorem rawActiveAlongExp_hasDerivAt {d : Nat} (O : Finset Nat) (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (t : Real) :
    HasDerivAt (rawActiveAlongExp O mu v hv) (rawActiveFirst O mu v t) t := by
  have h := (activeSymmetricSubmodule d O).orthogonalProjectionOnto.hasFDerivAt.comp_hasDerivAt t
    (rawActiveTensor_hasDerivAt O mu v hv hc t)
  have he : (fun s => (activeSymmetricSubmodule d O).orthogonalProjectionOnto
      (rawActiveAlongExp O mu v hv s).val) = rawActiveAlongExp O mu v hv := by
    funext s
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
  rw [← he]
  exact h

/-- Projection leaves the actual first tensor derivative unchanged. -/
theorem rawActiveFirst_val {d : Nat} (O : Finset Nat) (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (t : Real) :
    (rawActiveFirst O mu v t).val = rawActiveTensorFirst O mu v t := by
  have h := (activeSymmetricSubmodule d O).subtypeL.hasFDerivAt.comp_hasDerivAt t
    (rawActiveAlongExp_hasDerivAt O mu v hv hc t)
  exact h.unique (rawActiveTensor_hasDerivAt O mu v hv hc t)

theorem rawActiveFirst_hasDerivAt {d : Nat} (O : Finset Nat) (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (t : Real) :
    HasDerivAt (rawActiveFirst O mu v) (rawActiveSecond O mu v t) t := by
  exact (activeSymmetricSubmodule d O).orthogonalProjectionOnto.hasFDerivAt.comp_hasDerivAt t
    (rawActiveTensorFirst_hasDerivAt O mu v hv hc t)

/-- Projection also leaves the full second tensor derivative unchanged. -/
theorem rawActiveSecond_val {d : Nat} (O : Finset Nat) (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0)
    (hc : Continuous v) (t : Real) :
    (rawActiveSecond O mu v t).val = rawActiveTensorSecond O mu v t := by
  have h := (activeSymmetricSubmodule d O).subtypeL.hasFDerivAt.comp_hasDerivAt t
    (rawActiveFirst_hasDerivAt O mu v hv hc t)
  have he : (fun s => (rawActiveFirst O mu v s).val) = rawActiveTensorFirst O mu v :=
    funext (rawActiveFirst_val O mu v hv hc)
  change HasDerivAt (fun s => (rawActiveFirst O mu v s).val) (rawActiveSecond O mu v t).val t at h
  rw [he] at h
  exact h.unique (rawActiveTensorFirst_hasDerivAt O mu v hv hc t)

end PaperFormalization.MatrixFactorization
