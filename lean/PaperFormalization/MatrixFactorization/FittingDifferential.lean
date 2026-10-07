import PaperFormalization.MatrixFactorization.FittingEnergy

/-! # MF04: pointwise matrix-product fitting derivatives

These are calculus adapters for the literal Frobenius outer-product loss.
The subsequent spherical source theorem supplies the feature jets and their
Gaussian domination from the original activation and measures. In particular,
the second derivative retains both the squared first output derivative and
the residual paired with the full second output derivative.
-/

open MeasureTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def outerFirst {h : Nat} (x y dx dy : Weight h) : Output h :=
  outer dx y + outer x dy

noncomputable def outerSecond {h : Nat} (x y dx dy ddx ddy : Weight h) : Output h :=
  outer ddx y + (2 : Real) • outer dx dy + outer x ddy

theorem outer_hasDerivAt {h : Nat} {X Y : Real → Weight h} {dx dy : Weight h} {t : Real}
    (hx : HasDerivAt X dx t) (hy : HasDerivAt Y dy t) :
    HasDerivAt (fun s => outer (X s) (Y s)) (outerFirst (X t) (Y t) dx dy) t := by
  have hprod : HasDerivAt (fun (s : Real) (ij : Fin h × Fin h) => X s ij.1 * Y s ij.2)
      (fun ij => dx ij.1 * Y t ij.2 + X t ij.1 * dy ij.2) t := by
    apply hasDerivAt_pi.mpr
    intro ij
    have hxi : HasDerivAt (fun s => X s ij.1) (dx ij.1) t :=
      (PiLp.hasFDerivAt_apply (𝕜 := Real) 2 (X t) ij.1).comp_hasDerivAt t hx
    have hyi : HasDerivAt (fun s => Y s ij.2) (dy ij.2) t :=
      (PiLp.hasFDerivAt_apply (𝕜 := Real) 2 (Y t) ij.2).comp_hasDerivAt t hy
    exact hxi.mul hyi
  have hd := (PiLp.hasFDerivAt_toLp (𝕜 := Real) 2 (fun ij : Fin h × Fin h => X t ij.1 * Y t ij.2)).comp_hasDerivAt t hprod
  apply hd.congr_deriv
  rfl

theorem outerFirst_hasDerivAt {h : Nat} {X Y DX DY : Real → Weight h}
    {ddx ddy : Weight h} {t : Real}
    (hx : HasDerivAt X (DX t) t) (hy : HasDerivAt Y (DY t) t)
    (hdx : HasDerivAt DX ddx t) (hdy : HasDerivAt DY ddy t) :
    HasDerivAt (fun s => outerFirst (X s) (Y s) (DX s) (DY s))
      (outerSecond (X t) (Y t) (DX t) (DY t) ddx ddy) t := by
  have hd := (outer_hasDerivAt hdx hy).add (outer_hasDerivAt hx hdy)
  apply hd.congr_deriv
  simp only [outerFirst, outerSecond]
  module

noncomputable def matrixPointLoss {h : Nat} (H : Output h) (x y : Weight h) : Real :=
  norm (outer x y-H)^2/2

noncomputable def matrixPointFirst {h : Nat} (H : Output h) (x y dx dy : Weight h) : Real :=
  inner Real (outer x y-H) (outerFirst x y dx dy)

noncomputable def matrixPointSecond {h : Nat} (H : Output h) (x y dx dy ddx ddy : Weight h) : Real :=
  norm (outerFirst x y dx dy)^2 + inner Real (outer x y-H) (outerSecond x y dx dy ddx ddy)

theorem matrixPointLoss_hasDerivAt {h : Nat} {X Y : Real → Weight h}
    (H : Output h) {dx dy : Weight h} {t : Real}
    (hx : HasDerivAt X dx t) (hy : HasDerivAt Y dy t) :
    HasDerivAt (fun s => matrixPointLoss H (X s) (Y s))
      (matrixPointFirst H (X t) (Y t) dx dy) t := by
  have hd := (((outer_hasDerivAt hx hy).sub_const H).norm_sq).div_const 2
  apply hd.congr_deriv
  simp only [matrixPointFirst]
  ring

theorem matrixPointFirst_hasDerivAt {h : Nat} {X Y DX DY : Real → Weight h}
    (H : Output h) {ddx ddy : Weight h} {t : Real}
    (hx : HasDerivAt X (DX t) t) (hy : HasDerivAt Y (DY t) t)
    (hdx : HasDerivAt DX ddx t) (hdy : HasDerivAt DY ddy t) :
    HasDerivAt (fun s => matrixPointFirst H (X s) (Y s) (DX s) (DY s))
      (matrixPointSecond H (X t) (Y t) (DX t) (DY t) ddx ddy) t := by
  have hd := ((outer_hasDerivAt hx hy).sub_const H).inner Real
    (outerFirst_hasDerivAt hx hy hdx hdy)
  apply hd.congr_deriv
  simp only [matrixPointSecond, real_inner_self_eq_norm_sq, add_comm]

end PaperFormalization.MatrixFactorization
