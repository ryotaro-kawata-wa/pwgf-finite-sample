import PaperFormalization.MatrixFactorization.HermiteDerivatives
import PaperFormalization.MatrixFactorization.SphericalGeodesicShift

/-! # MF04: actual feature derivatives along the spherical EXP

The activation is the original finite normalized-Hermite activation at order
zero. Both derivatives below follow the actual EXP point and its velocity.
In particular, the second derivative contains the sphere's radial acceleration;
an output-linear ray cannot replace this term.
-/
open MeasureTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def sphericalFeatureJet {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (z : Weight d) (t : Real) : Weight h :=
  finiteHermiteActivationJet k O a (inner Real (geodesicPoint w v hv t).val z)

noncomputable def sphericalFeatureFirst {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (z : Weight d) (t : Real) : Weight h :=
  inner Real (sphereExpVelocity w v t) z • sphericalFeatureJet (k+1) O a w v hv z t

noncomputable def sphericalFeatureSecond {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (z : Weight d) (t : Real) : Weight h :=
  (inner Real (sphereExpVelocity w v t) z)^2 • sphericalFeatureJet (k+2) O a w v hv z t -
    ((norm v)^2 * inner Real (geodesicPoint w v hv t).val z) •
      sphericalFeatureJet (k+1) O a w v hv z t

@[simp] theorem sphericalFeatureJet_zero_order {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (z : Weight d) (t : Real) :
    sphericalFeatureJet 0 O a w v hv z t =
      finiteHermiteActivation O a (inner Real (geodesicPoint w v hv t).val z) := by
  simp only [sphericalFeatureJet, finiteHermiteActivationJet_zero]

theorem sphericalFeatureJet_hasDerivAt {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (z : Weight d) (t : Real) :
    HasDerivAt (sphericalFeatureJet k O a w v hv z)
      (sphericalFeatureFirst k O a w v hv z t) t := by
  have hd : HasDerivAt (fun s => inner Real (geodesicPoint w v hv s).val z)
      (inner Real (sphereExpVelocity w v t) z) t := by
    simpa only [geodesicPoint_val, inner_zero_right, zero_add] using
      (sphereExpVector_hasDerivAt w v t).inner Real (hasDerivAt_const t z)
  exact (finiteHermiteActivationJet_hasDerivAt k O a _).scomp t hd

theorem sphericalFeatureFirst_hasDerivAt {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (z : Weight d) (t : Real) :
    HasDerivAt (sphericalFeatureFirst k O a w v hv z)
      (sphericalFeatureSecond k O a w v hv z t) t := by
  have hd : HasDerivAt (fun s => inner Real (sphereExpVelocity w v s) z)
      (-(norm v)^2 * inner Real (geodesicPoint w v hv t).val z) t := by
    have hi := (sphereExpVelocity_hasDerivAt w v t).inner Real (hasDerivAt_const t z)
    apply hi.congr_deriv
    simp only [inner_zero_right, zero_add, real_inner_smul_left, geodesicPoint_val]
  have hi := hd.smul (sphericalFeatureJet_hasDerivAt (k+1) O a w v hv z t)
  apply hi.congr_deriv
  simp only [sphericalFeatureFirst, sphericalFeatureSecond, Nat.add_assoc]
  module

theorem sphericalFeatureJet_second_derivative {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (z : Weight d) (t : Real) :
    HasDerivAt (deriv (sphericalFeatureJet k O a w v hv z))
      (sphericalFeatureSecond k O a w v hv z t) t := by
  have he : deriv (sphericalFeatureJet k O a w v hv z) = sphericalFeatureFirst k O a w v hv z := by
    funext s
    exact (sphericalFeatureJet_hasDerivAt k O a w v hv z s).deriv
  rw [he]
  exact sphericalFeatureFirst_hasDerivAt k O a w v hv z t

@[simp] theorem sphericalFeatureJet_at_zero {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (z : Weight d) :
    sphericalFeatureJet k O a w v hv z 0 = finiteHermiteActivationJet k O a (inner Real w.val z) := by
  simp only [sphericalFeatureJet, geodesicPoint_zero]

@[simp] theorem sphericalFeatureFirst_at_zero {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (z : Weight d) :
    sphericalFeatureFirst k O a w v hv z 0 =
      inner Real v z • finiteHermiteActivationJet (k+1) O a (inner Real w.val z) := by
  simp only [sphericalFeatureFirst, sphereExpVelocity_at_zero, sphericalFeatureJet_at_zero]

@[simp] theorem sphericalFeatureSecond_at_zero {d h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) (z : Weight d) :
    sphericalFeatureSecond k O a w v hv z 0 =
      (inner Real v z)^2 • finiteHermiteActivationJet (k+2) O a (inner Real w.val z) -
        ((norm v)^2 * inner Real w.val z) • finiteHermiteActivationJet (k+1) O a (inner Real w.val z) := by
  simp only [sphericalFeatureSecond, sphereExpVelocity_at_zero, sphericalFeatureJet_at_zero,
    geodesicPoint_zero]

end PaperFormalization.MatrixFactorization
