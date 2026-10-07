import PaperFormalization.MatrixFactorization.SphericalCharacteristicRadialDecay
import PaperFormalization.MatrixFactorization.SphericalCurveCostDifferential
import PaperFormalization.MatrixFactorization.SphericalCapStateBounds
import PaperFormalization.MatrixFactorization.AssignedCostCurveDifferential
import PaperFormalization.MatrixFactorization.SphericalCurveCostAtPole
import PaperFormalization.MatrixFactorization.SphericalCharacteristicTransport
open MeasureTheory
namespace PaperFormalization.MatrixFactorization.MF14NonpoleChecks
open PaperFormalization.MatrixFactorization
set_option autoImplicit false

-- Tangency is derived for any actual sphere curve; no tangent premise is supplied.
example {d : Nat} (w : Real → UnitSphere d) (v : Weight d) (t : Real)
    (hw : HasDerivAt (fun s => (w s).val) v t) : inner Real (w t).val v = 0 :=
  sphereCurve_derivative_tangent w v t hw

-- A nonpole constant path has zero cost derivative at every real parameter.
example {d : Nat} (y x : UnitSphere d) (t : Real)
    (hr : 0 < sphericalDistance x y) (hs : sphericalDistance x y < Real.pi) :
    HasDerivAt (fun _ : Real => poleCost y x) 0 t := by
  simpa only [inner_zero_right] using
    poleCost_curve_hasDerivAt_nonpole y (fun _ => x) 0 t (hasDerivAt_const t x.val) hr hs

-- The computed gradient pairing equals the ordinary derivative of the literal cost.
example {d : Nat} (y : UnitSphere d) (w : Real → UnitSphere d) (v : Weight d) (t : Real)
    (hw : HasDerivAt (fun s => (w s).val) v t)
    (hr : 0 < sphericalDistance (w t) y) (hs : sphericalDistance (w t) y < Real.pi) :
    deriv (fun s => poleCost y (w s)) t = inner Real (poleGradient y (w t)) v :=
  (poleCost_curve_hasDerivAt_nonpole y w v t hw hr hs).deriv
end PaperFormalization.MatrixFactorization.MF14NonpoleChecks

open MeasureTheory
namespace PaperFormalization.MatrixFactorization.MF14CapBoundsChecks
open PaperFormalization.MatrixFactorization
set_option autoImplicit false

-- The actual two-marginal transport infimum is bounded from the original cap class.
example {d : Nat} (pole : UnitSphere d) (r : Real)
    (mu : Fin 2 → Measure (UnitSphere d)) (hc : ∀ i, TwoCapClass pole r (mu i)) :
    productAntipodalTransportSq pole (mu 0) (mu 1) ≤ 2*r^2 :=
  productAntipodalTransportSq_le_caps pole r mu hc

-- Setting lambda to zero removes the metric contribution from the uniform field bound.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (pole : UnitSphere d) (r p : Real)
    (mu : Fin 2 → Measure (UnitSphere d)) (hc : ∀ i, TwoCapClass pole r (mu i)) (hp : 2 < p)
    (teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2]
    (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (mu i).support) :
    norm (sphericalObjectiveGradient O a pole 0 p (mu 0) (mu 1) teacher1 teacher2 i w) ≤
      fittingCurvatureConstant d O a := by
  simpa only [abs_zero, zero_mul, add_zero] using
    sphericalObjectiveGradient_norm_le_cap O a pole r 0 p mu hc hp teacher1 teacher2 i w hw
end PaperFormalization.MatrixFactorization.MF14CapBoundsChecks

open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

example {d : Nat} (a : UnitSphere d)
    (r : Real) (w : Real → UnitSphere d) (t : Real)
    (hr : r < Real.pi/2)
    (hw : w t ∈ sphericalCap a r ∪ sphericalCap (reflect a) r)
    (hc : ContinuousAt w t) :
    (fun s => assignedPole a (w s)) =ᶠ[𝓝 t] (fun _ => assignedPole a (w t)) := by
  exact assignedPole_curve_eventually_constant a r w t hr hw hc

example {d : Nat} (a : UnitSphere d)
    (r : Real) (w : Real → UnitSphere d) (t : Real)
    (hr : r < Real.pi/2)
    (hw : w t ∈ sphericalCap a r ∪ sphericalCap (reflect a) r)
    (hc : ContinuousAt w t) :
    (fun s => assignedCost a (w s)) =ᶠ[𝓝 t]
      (fun s => poleCost (assignedPole a (w t)) (w s)) := by
  exact assignedCost_curve_eventually_poleCost a r w t hr hw hc

example {d : Nat} (y : UnitSphere d)
    (w : Real → UnitSphere d) (v : Weight d) (t : Real)
    (hw : HasDerivAt (fun s => (w s).val) v t)
    (hs : sphericalDistance (w t) y < Real.pi) :
    HasDerivAt (fun s => poleCost y (w s))
      (inner Real (poleGradient y (w t)) v) t := by
  exact poleCost_curve_hasDerivAt y w v t hw hs

example {d : Nat} (a : UnitSphere d)
    (r : Real) (w : Real → UnitSphere d) (v : Weight d) (t : Real)
    (hr : r < Real.pi/2)
    (hw : w t ∈ sphericalCap a r ∪ sphericalCap (reflect a) r)
    (hd : HasDerivAt (fun s => (w s).val) v t) :
    HasDerivAt (fun s => assignedCost a (w s))
      (inner Real (assignedGradient a (w t)) v) t := by
  exact assignedCost_curve_hasDerivAt a r w v t hr hw hd

example
    {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
    {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
    {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (initial i).support)
    (t : Real) (ht : t ∈ Ioo (0 : Real) T) :
    HasDerivAt (fun s => assignedCost pole (X.characteristic i s w))
      (-inner Real (sphericalObjectiveGradient O a pole lambda p
        (X.measure 0 t) (X.measure 1 t) teacher teacher i (X.characteristic i t w))
        (assignedGradient pole (X.characteristic i t w))) t := by
  exact SphericalCharacteristicSolution.assignedCost_hasDerivAt X i w hw t ht

end PaperFormalization.MatrixFactorization

namespace PaperFormalization.MatrixFactorization.MF14PoleChecks
open PaperFormalization.MatrixFactorization

-- The global angular/chord comparison is exact at antipodal points.
example {d : Nat} (y : UnitSphere d) :
    (sphericalDistance y (reflect y))^2 =
      Real.pi^2/4 * norm (y.val-(reflect y).val)^2 := by
  simp only [sphericalDistance_antipode, reflect_val, sub_neg_eq_add]
  rw [← two_smul Real y.val, norm_smul, unitSphere_norm]
  norm_num

-- A stationary pole curve is included even with zero velocity.
example {d : Nat} (y : UnitSphere d) (t : Real) :
    HasDerivAt (fun _ : Real => poleCost y y) 0 t :=
  poleCost_curve_hasDerivAt_at_pole y (fun _ => y) 0 t (hasDerivAt_const t y.val) rfl

-- Passing through the pole requires no exponential-path representation.
example {d : Nat} (y : UnitSphere d) (w : Real → UnitSphere d)
    (v : Weight d) (t : Real) (hw : HasDerivAt (fun s => (w s).val) v t)
    (hy : w t = y) :
    HasDerivAt (fun s => poleCost y (w s)) (inner Real (poleGradient y (w t)) v) t := by
  simpa only [hy, poleGradient_self, inner_zero_left] using
    poleCost_curve_hasDerivAt_at_pole y w v t hw hy

-- The halfcost remains defined at the antipode; no derivative there is asserted.
example {d : Nat} (y : UnitSphere d) :
    poleCost y (reflect y) = Real.pi^2/2 := by
  rw [poleCost, sphericalDistance_comm, sphericalDistance_antipode]

end PaperFormalization.MatrixFactorization.MF14PoleChecks

namespace PaperFormalization.MatrixFactorization.MF14TransportChecks
open PaperFormalization.MatrixFactorization MeasureTheory Set
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}
-- Actual assignment at the initial endpoint is included without differentiating the endpoint.
example (X : SphericalCharacteristicSolution O a pole radius lambda (5/2) teacher initial T)
    (i : Fin 2) :
    sphericalWassersteinSq (X.measure i 0) (antipodalMeasure pole) =
      2*∫ w, assignedCost pole (X.characteristic i 0 w) ∂initial i :=
  X.transport_integral i 0 ⟨le_rfl,X.time_nonneg⟩
-- The ordinary derivative exchange includes the fractional exponent 5/2 and either sign of lambda.
example (X : SphericalCharacteristicSolution O a pole radius lambda (5/2) teacher initial T)
    [IsProbabilityMeasure teacher] (t : Real) (ht : t ∈ Ioo (0:Real) T) :
    HasDerivAt (fun s => productAntipodalTransportSq pole (X.measure 0 s) (X.measure 1 s))
      (-2*(∑ i : Fin 2, ∫ w, inner Real (sphericalObjectiveGradient O a pole lambda (5/2)
        (X.measure 0 t) (X.measure 1 t) teacher teacher i w) (assignedGradient pole w) ∂X.measure i t)) t :=
  X.productTransport_hasDerivAt (by norm_num) t ht
end PaperFormalization.MatrixFactorization.MF14TransportChecks

open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

example
    {d h : Nat} {O : Finset Nat} {a : Nat → Weight h}
    (hO : ∀ n ∈ O, Odd n) {pole : UnitSphere d} {radius lambda p : Real}
    {teacher : Measure (UnitSphere d)} [IsProbabilityMeasure teacher]
    {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (hlambda : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (t : Real) (ht : t ∈ Ioo (0 : Real) T)
    (hsmall : productAntipodalTransportSq pole (X.measure 0 t) (X.measure 1 t) ≤
      coarseRadialRadius lambda p (fittingCurvatureConstant d O a/64)) :
    deriv (fun s => productAntipodalTransportSq pole (X.measure 0 s) (X.measure 1 s)) t ≤
      -lambda*(productAntipodalTransportSq pole (X.measure 0 t) (X.measure 1 t))^(p/2) := by
  exact SphericalCharacteristicSolution.radial_transport_deriv_le hO X hunique hinitial hlambda hp hp4 t ht hsmall

example
    {d h : Nat} {O : Finset Nat} {a : Nat → Weight h}
    (hO : ∀ n ∈ O, Odd n) {pole : UnitSphere d} {radius lambda p : Real}
    {teacher : Measure (UnitSphere d)} [IsProbabilityMeasure teacher]
    {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (hlambda : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (t : Real) (ht : t ∈ Ioo (0 : Real) T)
    (hsmall : productAntipodalTransportSq pole (X.measure 0 t) (X.measure 1 t) ≤
      coarseRadialRadius lambda p (fittingCurvatureConstant d O a/64)) :
    deriv (fun s => productAntipodalTransportSq pole (X.measure 0 s) (X.measure 1 s)) t ≤ 0 := by
  exact SphericalCharacteristicSolution.radial_transport_deriv_nonpos hO X hunique hinitial hlambda hp hp4 t ht hsmall

end PaperFormalization.MatrixFactorization
