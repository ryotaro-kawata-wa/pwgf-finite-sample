import PaperFormalization.MatrixFactorization.TensorJetBounds
import PaperFormalization.MatrixFactorization.SphericalExponential

/-! # MF33: full tensor jets of the actual spherical EXP path

The estimates hold at every signed time. They retain the sharp degree factors
and the genuine constant speed of EXP, including zero velocity and both poles.
-/
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def sphericalTensorFirst {d : Nat} (n : Nat) (w : UnitSphere d)
    (v : Weight d) (t : Real) : MomentTensor d n :=
  tensorFirstJet n (sphereExpVector w (t • v)) (sphereExpVelocity w v t)

noncomputable def sphericalTensorSecond {d : Nat} (n : Nat) (w : UnitSphere d)
    (v : Weight d) (t : Real) : MomentTensor d n :=
  tensorSecondJet n (sphereExpVector w (t • v)) (sphereExpVelocity w v t)
    (-(‖v‖ ^ 2) • sphereExpVector w (t • v))

theorem sphericalTensor_hasDerivAt {d n : Nat} (w : UnitSphere d) (v : Weight d) (t : Real) :
    HasDerivAt (fun s => tensorPower n (sphereExpVector w (s • v)))
      (sphericalTensorFirst n w v t) t :=
  tensorPower_hasDerivAt (sphereExpVector_hasDerivAt w v t)

theorem sphericalTensorFirst_hasDerivAt {d n : Nat} (w : UnitSphere d) (v : Weight d) (t : Real) :
    HasDerivAt (sphericalTensorFirst n w v) (sphericalTensorSecond n w v t) t :=
  tensorFirstJet_hasDerivAt (sphereExpVector_hasDerivAt w v t) (sphereExpVelocity_hasDerivAt w v t)

/-- The first derivative carries exactly n times the original particle speed. -/
theorem sphericalTensorFirst_norm_le {d n : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t : Real) :
    ‖sphericalTensorFirst n w v t‖ ≤ (n : Real) * ‖v‖ := by
  let y := sphericalExp w (t • v) (by rw [inner_smul_right, hv, mul_zero])
  have h := tensorFirstJet_norm_le (n := n) y (sphereExpVelocity w v t)
  rw [sphereExpVelocity_norm w v hv] at h
  exact h

/-- Radial acceleration contributes the diagonal n terms to the n-squared bound. -/
theorem sphericalTensorSecond_norm_le {d n : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t : Real) :
    ‖sphericalTensorSecond n w v t‖ ≤ (n : Real) ^ 2 * ‖v‖ ^ 2 := by
  let y := sphericalExp w (t • v) (by rw [inner_smul_right, hv, mul_zero])
  have hy : ‖y.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using y.property
  have ha : ‖-(‖v‖ ^ 2) • y.val‖ ≤ ‖sphereExpVelocity w v t‖ ^ 2 := by
    rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hy, mul_one,
      sphereExpVelocity_norm w v hv]
  have h := tensorSecondJet_norm_le (n := n) y (sphereExpVelocity w v t) (-(‖v‖ ^ 2) • y.val) ha
  rw [sphereExpVelocity_norm w v hv] at h
  exact h

theorem sphericalTensorFirst_continuous {d : Nat} (n : Nat)
    (v : UnitSphere d → Weight d) (hc : Continuous v) :
    Continuous (fun z : Real × UnitSphere d => sphericalTensorFirst n z.2 (v z.2) z.1) := by
  have hp : Continuous (fun z : Real × UnitSphere d => sphereExpVector z.2 (z.1 • v z.2)) := by
    unfold sphereExpVector
    fun_prop
  have hd : Continuous (fun z : Real × UnitSphere d => sphereExpVelocity z.2 (v z.2) z.1) := by
    unfold sphereExpVelocity
    fun_prop
  have h := (tensorFirstJet_continuous d n).comp (hp.prodMk hd)
  convert h using 1 <;> rfl

theorem sphericalTensorSecond_continuous {d : Nat} (n : Nat)
    (v : UnitSphere d → Weight d) (hc : Continuous v) :
    Continuous (fun z : Real × UnitSphere d => sphericalTensorSecond n z.2 (v z.2) z.1) := by
  have hp : Continuous (fun z : Real × UnitSphere d => sphereExpVector z.2 (z.1 • v z.2)) := by
    unfold sphereExpVector
    fun_prop
  have hd : Continuous (fun z : Real × UnitSphere d => sphereExpVelocity z.2 (v z.2) z.1) := by
    unfold sphereExpVelocity
    fun_prop
  have ha : Continuous (fun z : Real × UnitSphere d => -(‖v z.2‖ ^ 2) • sphereExpVector z.2 (z.1 • v z.2)) := by
    exact (((hc.comp continuous_snd).norm.pow 2).neg).smul hp
  have h := (tensorSecondJet_continuous d n).comp ((hp.prodMk hd).prodMk ha)
  convert h using 1 <;> rfl

@[simp] theorem sphericalTensorFirst_zero {d n : Nat} (w : UnitSphere d) (v : Weight d) :
    sphericalTensorFirst n w v 0 = tensorFirstJet n w.val v := by
  simp [sphericalTensorFirst]

@[simp] theorem sphericalTensorSecond_zero {d n : Nat} (w : UnitSphere d) (v : Weight d) :
    sphericalTensorSecond n w v 0 = tensorSecondJet n w.val v (-(‖v‖ ^ 2) • w.val) := by
  simp [sphericalTensorSecond]

end PaperFormalization.MatrixFactorization
