import PaperFormalization.MatrixFactorization.IntrinsicACIntegratedEnergy
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

-- 01: the constructed gradient is tangent everywhere.
example (phi : Weight d → Real) (w : UnitSphere d) :
    inner Real w.val (sphericalTestGradient phi w) = 0 := sphericalTestGradient_tangent phi w

-- 02: the intrinsic pairing agrees with the actual differential on tangent directions.
example (phi : Weight d → Real) (w : UnitSphere d) (v : Weight d)
    (hv : inner Real w.val v = 0) :
    inner Real (sphericalTestGradient phi w) v = fderiv Real phi w.val v :=
  sphericalTestGradient_pairing phi w v hv

-- 03: zero velocity is not excluded from the pairing identity.
example (phi : Weight d → Real) (w : UnitSphere d) :
    inner Real (sphericalTestGradient phi w) (0 : Weight d) = 0 := by simp

-- 04: compact ambient support is unnecessary for continuity on the sphere.
example (phi : Weight d → Real) (hphi : ContDiff Real 1 phi) :
    Continuous (sphericalTestGradient phi) := sphericalTestGradient_continuous phi hphi

-- 05: the source-gradient PDE is valid with lambda zero.
example (X : PrimalACCharacteristicData O a pole 0 p teacher initial)
    [IsProbabilityMeasure teacher] (hp : 2 < p)
    (phi : Weight d → Real) (hphi : ContDiff Real 1 phi) (i : Fin 2) :
    ∀ᵐ t ∂volume.restrict (Ici (0 : Real)),
      Integrable (fun w => inner Real (sphericalTestGradient phi w) (X.gradient i t w))
        (X.measure i t) ∧
      HasDerivAt (fun r => ∫ w, phi w.val ∂X.measure i r)
        (-(∫ w, inner Real (sphericalTestGradient phi w) (X.gradient i t w) ∂X.measure i t)) t :=
  X.spherical_weak_continuity_ae le_rfl hp phi hphi i

-- 06: a constant time weight recovers the endpoint flux equation.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (phi : Weight d → Real) (hphi : ContDiff Real 1 phi) (i : Fin 2)
    (s t : Real) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (∫ r in s..t, -(∫ w, inner Real (sphericalTestGradient phi w) (X.gradient i r w)
      ∂X.measure i r)) = (∫ w, phi w.val ∂X.measure i t) - (∫ w, phi w.val ∂X.measure i s) := by
  simpa using (X.spherical_spacetime_integral hl hp phi hphi
    (fun _ => (1 : Real)) contDiff_const i s t hs ht).2

-- 07: zero endpoint weights give the distributional test identity.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (phi : Weight d → Real) (hphi : ContDiff Real 1 phi)
    (eta : Real → Real) (heta : ContDiff Real 1 eta) (i : Fin 2)
    (s t : Real) (hs : 0 ≤ s) (ht : 0 ≤ t) (hes : eta s = 0) (het : eta t = 0) :
    (∫ r in s..t, (deriv eta r * (∫ w, phi w.val ∂X.measure i r) -
      eta r * (∫ w, inner Real (sphericalTestGradient phi w) (X.gradient i r w) ∂X.measure i r))) = 0 :=
  X.spherical_spacetime_zero_boundary hl hp phi hphi eta heta i s t hs ht hes het

-- 08: time-weighted AC integration supports reversed endpoints.
example (m j eta : Real → Real) (s t : Real)
    (hm : AbsolutelyContinuousOnInterval m t s) (hj : IntervalIntegrable j volume t s)
    (hd : ∀ᵐ r : Real, r ∈ uIcc t s → HasDerivAt m (-j r) r)
    (heta : ContDiff Real 1 eta) :
    IntervalIntegrable (fun r => deriv eta r * m r - eta r * j r) volume t s ∧
    (∫ r in t..s, (deriv eta r * m r - eta r * j r)) = eta s * m s - eta t * m t :=
  ac_weighted_test_identity m j eta t s hm hj hd heta

-- 09: the stored original-gradient energy is nonnegative at every time.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial) (t : Real) :
    0 ≤ X.originalGradientEnergy t := X.originalGradientEnergy_nonneg t

-- 10: original energy admits signed integrals, including reverse time pairs.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r : Real) (hcaps : ∀ i t, 0 ≤ t → TwoCapClass pole r (X.measure i t))
    (s t : Real) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    IntervalIntegrable X.originalGradientEnergy volume t s ∧
    (∫ u in t..s, X.originalGradientEnergy u) = X.objective t - X.objective s :=
  X.integrated_original_energy hl hp r hcaps t s ht hs

-- 11: actual full-objective AC follows without a positive regularization coefficient.
example (X : PrimalACCharacteristicData O a pole 0 p teacher initial)
    [IsProbabilityMeasure teacher] (hp : 2 < p)
    (r : Real) (hcaps : ∀ i t, 0 ≤ t → TwoCapClass pole r (X.measure i t))
    (s t : Real) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    AbsolutelyContinuousOnInterval X.objective s t :=
  X.objective_ac_of_caps le_rfl hp r hcaps s t hs ht

-- 12: the accumulated action uses the actual original representative and initial value.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r : Real) (hcaps : ∀ i t, 0 ≤ t → TwoCapClass pole r (X.measure i t))
    (t : Real) (ht : 0 ≤ t) :
    X.objective t + (∫ u in 0..t, X.originalGradientEnergy u) = X.objective 0 :=
  X.original_energy_balance hl hp r hcaps t ht

end PaperFormalization.MatrixFactorization
