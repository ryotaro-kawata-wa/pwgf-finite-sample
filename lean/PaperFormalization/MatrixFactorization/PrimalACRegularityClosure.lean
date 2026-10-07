import PaperFormalization.MatrixFactorization.PrimalACIntegralReplacement

/-! # MF25: integral, supported regularity and the first complete cap interval

Verification status and conditional scope: see `MF25_VALIDATION.md`. This endpoint consumes one fixed primal AC trajectory,
not a collection of unrelated finite solutions. It derives the speed estimate,
the integral equation, all-supported time Lipschitzness, joint continuity and
a common first cap interval. The full objective and the original laws remain
literal. No optimal dual potential or supportwise classical dual gradient is
an input. No global confinement, global uniqueness or manuscript-class
identification is claimed by this checkpoint.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Source-oriented analytic bridge for the explicitly specified AC class.
AC, Borel representatives, and primal first variation remain visible in the
input type; none is claimed to follow from a bare continuity equation. -/
theorem primal_ac_characteristic_first_cap {d h : Nat} {O : Finset Nat}
    {a : Nat → Weight h} {pole : UnitSphere d} {lambda p : Real}
    {teacher : Measure (UnitSphere d)} {initial : Fin 2 → Measure (UnitSphere d)}
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r : Real) (hc : ∀ i, TwoCapClass pole r (initial i)) :
    let M := primalObjectiveSpeedBound d O a lambda p
    let tau := primalInitialCapTime d O a pole r lambda p initial
    0 ≤ M ∧ 0 < tau ∧
    (∀ i w, w ∈ (initial i).support →
      LipschitzOnWith (Real.nnabs M) (fun t => X.characteristic i t w) (Ici (0 : Real))) ∧
    (∀ i, ContinuousOn (fun tw : Real × UnitSphere d => X.characteristic i tw.1 tw.2)
      ((Ici (0 : Real)) ×ˢ (initial i).support)) ∧
    (∀ i s t, 0 ≤ s → 0 ≤ t → ∀ᵐ w ∂initial i,
      IntervalIntegrable (fun u => X.pullbackGradient i u w) volume s t ∧
      (X.characteristic i t w).val - (X.characteristic i s w).val =
        -(∫ u in s..t, X.pullbackGradient i u w)) ∧
    (∀ i t, t ∈ Icc (0 : Real) tau → TwoCapClass pole r (X.measure i t)) ∧
    (∀ᵐ t ∂volume.restrict (Icc (0 : Real) tau), ∀ i,
      X.gradient i t =ᵐ[X.measure i t]
        sphericalObjectiveGradient O a pole lambda p (X.measure 0 t) (X.measure 1 t)
          teacher teacher i) := by
  have hfirst := X.first_cap_laws hl hp r hc
  exact ⟨primalObjectiveSpeedBound_nonneg d O a lambda p hl,
    hfirst.1, X.supported_lipschitz hl hp, X.supported_joint_continuity hl hp,
    X.integral_equation_ae hl hp, hfirst.2, X.first_cap_gradient_ae hl hp r hc⟩

end PaperFormalization.MatrixFactorization
