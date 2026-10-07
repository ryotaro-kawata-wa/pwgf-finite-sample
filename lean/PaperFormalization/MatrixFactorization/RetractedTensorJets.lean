import PaperFormalization.MatrixFactorization.TensorAccelerationBound
import PaperFormalization.MatrixFactorization.SphericalTensorJets
import PaperFormalization.MatrixFactorization.GeneralRetractionDifferential

/-! # MF35: raw tensor jets along the manuscript's normalized retraction

Uniform bounds justify differentiation under the original measure. At zero,
the literal first and second tensor jets agree with those of spherical EXP.
-/
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def retractedTensorFirst {d : Nat} (n : Nat) (w : UnitSphere d)
    (v : Weight d) (t : Real) : MomentTensor d n :=
  tensorFirstJet n (sphericalRetractVector w v t) (sphericalRetractVelocity w v t)

noncomputable def retractedTensorSecond {d : Nat} (n : Nat) (w : UnitSphere d)
    (v : Weight d) (t : Real) : MomentTensor d n :=
  tensorSecondJet n (sphericalRetractVector w v t) (sphericalRetractVelocity w v t)
    (sphericalRetractAcceleration w v t)

theorem retractedTensor_hasDerivAt {d n : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t : Real) :
    HasDerivAt (fun s => tensorPower n (sphericalRetractVector w v s))
      (retractedTensorFirst n w v t) t :=
  tensorPower_hasDerivAt (sphericalRetractVector_hasDerivAt w v hv t)

theorem retractedTensorFirst_hasDerivAt {d n : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t : Real) :
    HasDerivAt (retractedTensorFirst n w v) (retractedTensorSecond n w v t) t :=
  tensorFirstJet_hasDerivAt (sphericalRetractVector_hasDerivAt w v hv t)
    (sphericalRetractVelocity_hasDerivAt w v hv t)

/-- This uniform envelope is used only for differentiation, not the final sharp bound. -/
theorem retractedTensorFirst_norm_le {d n : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t : Real) :
    ‖retractedTensorFirst n w v t‖ ≤ (2 * (n : Real)) * ‖v‖ := by
  have h := tensorFirstJet_norm_le (n := n) (sphericalRetract w v hv t) (sphericalRetractVelocity w v t)
  have hvb := mul_le_mul_of_nonneg_left (sphericalRetractVelocity_norm_le w v hv t) (Nat.cast_nonneg n)
  change ‖retractedTensorFirst n w v t‖ ≤ _ at h
  nlinarith

theorem retractedTensorSecond_norm_le {d n : Nat} (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (t : Real) :
    ‖retractedTensorSecond n w v t‖ ≤ (6 * (n : Real) ^ 2) * ‖v‖ ^ 2 := by
  have hspeed := (sq_le_sq₀ (norm_nonneg (sphericalRetractVelocity w v t))
    (mul_nonneg (by norm_num : (0 : Real) ≤ 2) (norm_nonneg v))).mpr
      (sphericalRetractVelocity_norm_le w v hv t)
  have hspeed6 : ‖sphericalRetractVelocity w v t‖ ^ 2 ≤ 6 * ‖v‖ ^ 2 := by
    nlinarith [sq_nonneg ‖v‖]
  have h := tensorSecondJet_norm_le_of_bounds (n := n) (sphericalRetract w v hv t)
    (sphericalRetractVelocity w v t) (sphericalRetractAcceleration w v t) (6 * ‖v‖ ^ 2)
    hspeed6 (sphericalRetractAcceleration_norm_le w v hv t)
  convert h using 1 <;> first | rfl | ring

theorem retractedTensorFirst_continuous {d : Nat} (n : Nat)
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) :
    Continuous (fun z : Real × UnitSphere d => retractedTensorFirst n z.2 (v z.2) z.1) := by
  have hp := (sphericalRetractFamily_continuous v hv hc).subtype_val
  have hd := sphericalRetractVelocity_continuous v hv hc
  have h := (tensorFirstJet_continuous d n).comp (hp.prodMk hd)
  convert h using 1 <;> rfl

theorem retractedTensorSecond_continuous {d : Nat} (n : Nat)
    (v : UnitSphere d → Weight d) (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) :
    Continuous (fun z : Real × UnitSphere d => retractedTensorSecond n z.2 (v z.2) z.1) := by
  have hp := (sphericalRetractFamily_continuous v hv hc).subtype_val
  have hd := sphericalRetractVelocity_continuous v hv hc
  have ha := sphericalRetractAcceleration_continuous v hv hc
  have h := (tensorSecondJet_continuous d n).comp ((hp.prodMk hd).prodMk ha)
  convert h using 1 <;> rfl

/-- The pathwise equality concerns exactly the first jet at the initial parameter. -/
theorem retractedTensorFirst_zero_eq_exp {d n : Nat} (w : UnitSphere d) (v : Weight d) :
    retractedTensorFirst n w v 0 = sphericalTensorFirst n w v 0 := by
  simp only [retractedTensorFirst, sphericalTensorFirst_zero,
    sphericalRetractVector_zero, sphericalRetractVelocity_zero]

/-- The radial acceleration is retained in the second-jet equality. -/
theorem retractedTensorSecond_zero_eq_exp {d n : Nat} (w : UnitSphere d) (v : Weight d) :
    retractedTensorSecond n w v 0 = sphericalTensorSecond n w v 0 := by
  simp only [retractedTensorSecond, sphericalTensorSecond_zero,
    sphericalRetractVector_zero, sphericalRetractVelocity_zero, sphericalRetractAcceleration_zero]

end PaperFormalization.MatrixFactorization
