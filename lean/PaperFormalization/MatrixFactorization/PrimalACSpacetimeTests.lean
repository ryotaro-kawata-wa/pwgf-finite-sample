import PaperFormalization.MatrixFactorization.SphericalTestGradient
import PaperFormalization.MatrixFactorization.ACWeightedTestIdentity

/-! # MF31: intrinsic spacetime test form of the spherical continuity equation

The tests eta(t) phi(w) have the source spherical-gradient pairing and the
original measurable velocity. Endpoint terms and true temporal integrability
are explicit. No pointwise identity at exceptional times is assumed.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

/-- The scalar time weight produces the full endpoint term in the weak PDE. -/
theorem PrimalACCharacteristicData.weak_spacetime_integral
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (phi : Weight d → Real) (hphi : ContDiff Real 1 phi)
    (eta : Real → Real) (heta : ContDiff Real 1 eta) (i : Fin 2)
    (s t : Real) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    IntervalIntegrable (fun r => deriv eta r * (∫ w, phi w.val ∂X.measure i r) -
      eta r * X.currentTestFlux phi i r) volume s t ∧
    (∫ r in s..t, (deriv eta r * (∫ w, phi w.val ∂X.measure i r) -
      eta r * X.currentTestFlux phi i r)) =
      eta t * (∫ w, phi w.val ∂X.measure i t) - eta s * (∫ w, phi w.val ∂X.measure i s) := by
  apply ac_weighted_test_identity
    (fun r => ∫ w, phi w.val ∂X.measure i r) (X.currentTestFlux phi i) eta s t
    (X.weak_test_ac hl hp phi hphi i s t hs ht)
    (X.weak_continuity_integral hl hp phi hphi i s t hs ht).1 ?_ heta
  exact ae_nonnegative_to_segment hs ht
    ((X.weak_continuity_ae hl hp phi hphi i).mono (fun r hr => hr.2))

/-- Exact intrinsic form with the original spherical gradient representative. -/
theorem PrimalACCharacteristicData.spherical_spacetime_integral
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (phi : Weight d → Real) (hphi : ContDiff Real 1 phi)
    (eta : Real → Real) (heta : ContDiff Real 1 eta) (i : Fin 2)
    (s t : Real) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    IntervalIntegrable (fun r => deriv eta r * (∫ w, phi w.val ∂X.measure i r) -
      eta r * (∫ w, inner Real (sphericalTestGradient phi w) (X.gradient i r w) ∂X.measure i r))
      volume s t ∧
    (∫ r in s..t, (deriv eta r * (∫ w, phi w.val ∂X.measure i r) -
      eta r * (∫ w, inner Real (sphericalTestGradient phi w) (X.gradient i r w) ∂X.measure i r))) =
      eta t * (∫ w, phi w.val ∂X.measure i t) - eta s * (∫ w, phi w.val ∂X.measure i s) := by
  have H := X.weak_spacetime_integral hl hp phi hphi eta heta i s t hs ht
  have he := ae_nonnegative_to_segment hs ht
    ((X.sphericalTestFlux_ae phi hphi i).mono (fun r hr => hr.2))
  have heq : (fun r => deriv eta r * (∫ w, phi w.val ∂X.measure i r) -
      eta r * X.currentTestFlux phi i r) =ᵐ[volume.restrict (uIoc s t)]
      fun r => deriv eta r * (∫ w, phi w.val ∂X.measure i r) -
        eta r * (∫ w, inner Real (sphericalTestGradient phi w) (X.gradient i r w) ∂X.measure i r) := by
    apply (ae_restrict_iff' measurableSet_uIoc).mpr
    filter_upwards [he] with r hr hmem
    rw [hr (uIoc_subset_uIcc hmem)]
  refine ⟨H.1.congr_ae heq, ?_⟩
  exact (intervalIntegral.integral_congr_ae_restrict heq).symm.trans H.2

/-- Vanishing temporal endpoint weights give the distributional test identity. -/
theorem PrimalACCharacteristicData.spherical_spacetime_zero_boundary
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (phi : Weight d → Real) (hphi : ContDiff Real 1 phi)
    (eta : Real → Real) (heta : ContDiff Real 1 eta) (i : Fin 2)
    (s t : Real) (hs : 0 ≤ s) (ht : 0 ≤ t) (hes : eta s = 0) (het : eta t = 0) :
    (∫ r in s..t, (deriv eta r * (∫ w, phi w.val ∂X.measure i r) -
      eta r * (∫ w, inner Real (sphericalTestGradient phi w) (X.gradient i r w) ∂X.measure i r))) = 0 := by
  simpa only [hes, het, zero_mul, sub_self] using
    (X.spherical_spacetime_integral hl hp phi hphi eta heta i s t hs ht).2

end PaperFormalization.MatrixFactorization
