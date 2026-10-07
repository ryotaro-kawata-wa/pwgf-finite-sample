import PaperFormalization.MatrixFactorization.TensorTrace

/-! # MF37: repeated contractions and the unit-sphere moment identities

Order transports only rewrite equal natural-number indices. Repeated traces
are actual continuous linear contractions, including zero traces and degree zero.
-/
open MeasureTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def tensorOrderEquiv {d m n : Nat} (h : m = n) :
    MomentTensor d m ≃ₗᵢ[Real] MomentTensor d n := by
  subst n
  exact LinearIsometryEquiv.refl Real (MomentTensor d m)

@[simp] theorem tensorOrderEquiv_tensorPower {d m n : Nat} (h : m = n) (w : Weight d) :
    tensorOrderEquiv h (tensorPower m w) = tensorPower n w := by
  subst n
  rfl

noncomputable def tensorIteratedTrace (d k : Nat) :
    (r : Nat) → MomentTensor d (k + 2 * r) →L[Real] MomentTensor d k
  | 0 => (tensorOrderEquiv (d := d) (by omega : k + 2 * 0 = k)).toContinuousLinearMap
  | r + 1 => (tensorIteratedTrace d k r).comp
      ((tensorTrace d (k + 2 * r)).comp
        (tensorOrderEquiv (d := d) (by omega : k + 2 * (r + 1) = (k + 2 * r) + 2)).toContinuousLinearMap)

/-- Each contracted pair contributes one squared norm, with no extra coefficient. -/
theorem tensorIteratedTrace_tensorPower {d k : Nat} (r : Nat) (w : Weight d) :
    tensorIteratedTrace d k r (tensorPower (k + 2 * r) w) =
      (‖w‖ ^ 2) ^ r • tensorPower k w := by
  induction r with
  | zero => simp [tensorIteratedTrace]
  | succ r ih =>
    change tensorIteratedTrace d k r (tensorTrace d (k + 2 * r)
      (tensorOrderEquiv (by omega : k + 2 * (r + 1) = (k + 2 * r) + 2)
        (tensorPower (k + 2 * (r + 1)) w))) = _
    rw [tensorOrderEquiv_tensorPower, tensorTrace_tensorPower, map_smul, ih, smul_smul]
    exact congrArg (fun c : Real => c • tensorPower k w) (pow_succ' (‖w‖ ^ 2) r).symm

/-- Unit normalization turns an actual higher-order raw tensor into its lower order. -/
theorem tensorIteratedTrace_unit {d k : Nat} (r : Nat) (w : UnitSphere d) :
    tensorIteratedTrace d k r (tensorPower (k + 2 * r) w.val) = tensorPower k w.val := by
  have hw : ‖w.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using w.property
  simp [tensorIteratedTrace_tensorPower, hw]

/-- Bochner integration commutes with the genuine contraction map. -/
theorem tensorIteratedTrace_rawMoment {d k : Nat} (r : Nat)
    (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu] :
    tensorIteratedTrace d k r (rawMoment mu (k + 2 * r)) = rawMoment mu k := by
  rw [rawMoment, ← (tensorIteratedTrace d k r).integral_comp_comm (rawMoment_integrable mu _)]
  simp only [tensorIteratedTrace_unit, rawMoment]

end PaperFormalization.MatrixFactorization
