import PaperFormalization.MatrixFactorization.SphericalCharacteristicTransport
import PaperFormalization.MatrixFactorization.SphericalCharacteristicSymmetry
import PaperFormalization.MatrixFactorization.CoarseRadialPositivity

/-! # Actual radial decay along the original characteristic flow

The transport derivative is obtained from the characteristic ODE and original
measure differentiation theorem. Branch invariance follows from uniqueness.
Only the current coarse smallness condition is assumed; no desired differential
inequality, trajectory confinement, or global flow existence is a premise.
-/
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The actual transport derivative obeys the source radial differential
inequality in the explicit coarse neighborhood on the fixed cap interval. -/
theorem SphericalCharacteristicSolution.radial_transport_deriv_le
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
  have htc : t ∈ Icc (0 : Real) T := ⟨ht.1.le,ht.2.le⟩
  have hbranch := spherical_characteristic_antibranch_invariant hO X hunique hinitial t htc
  have hsmall' : productAntipodalTransportSq pole (X.measure 0 t)
      (reflectedMeasure (X.measure 0 t)) ≤
      coarseRadialRadius lambda p (fittingCurvatureConstant d O a/64) := by
    simpa only [hbranch] using hsmall
  have hlower := antisymmetric_radial_pairing_small O a hO pole radius lambda p
    hlambda hp hp4 (X.measure 0 t) (X.cap 0 t htc) teacher hsmall'
  rw [(X.productTransport_hasDerivAt hp t ht).deriv]
  simp only [Fin.sum_univ_two,hbranch]
  change -2*antisymmetricRadialObjectivePairing O a pole lambda p (X.measure 0 t) teacher ≤ _
  linarith

/-- Zero transport is included in the nonpositive derivative conclusion. -/
theorem SphericalCharacteristicSolution.radial_transport_deriv_nonpos
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
  have htc : t ∈ Icc (0 : Real) T := ⟨ht.1.le,ht.2.le⟩
  letI : IsProbabilityMeasure (X.measure 0 t) := (X.cap 0 t htc).probability
  letI : IsProbabilityMeasure (X.measure 1 t) := (X.cap 1 t htc).probability
  have hZ : 0 ≤ productAntipodalTransportSq pole (X.measure 0 t) (X.measure 1 t) :=
    add_nonneg (sphericalWassersteinSq_nonneg _ _) (sphericalWassersteinSq_nonneg _ _)
  exact (X.radial_transport_deriv_le hO hunique hinitial hlambda hp hp4 t ht hsmall).trans
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlambda.le) (Real.rpow_nonneg hZ _))

end PaperFormalization.MatrixFactorization
