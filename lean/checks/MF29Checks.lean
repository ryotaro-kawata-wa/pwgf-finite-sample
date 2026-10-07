import PaperFormalization.MatrixFactorization.PrimalACWeakContinuity
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

-- 01: the bound requires no compact support for the ambient test.
example (phi : Weight d → Real) (hphi : ContDiff Real 1 phi) :
    ∃ C : Real, 0 ≤ C ∧ ∀ x : Weight d, norm x ≤ 1 → norm (fderiv Real phi x) ≤ C :=
  smooth_test_derivative_bound phi hphi

-- 02: the supported extension at time zero is the actual original label.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (initial i).support) :
    X.supportedAmbient i 0 w = w.val := by
  rw [X.supportedAmbient_eq i 0 le_rfl w hw, X.initial_map i w hw]

-- 03: an unsupported label is used only by the auxiliary zero extension.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (i : Fin 2) (t : Real) (w : UnitSphere d) (hw : w ∉ (initial i).support) :
    X.supportedAmbient i t w = 0 := by simp [PrimalACCharacteristicData.supportedAmbient, hw]

-- 04: both supported and auxiliary values lie in the unit ball.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (i : Fin 2) (t : Real) (w : UnitSphere d) : norm (X.supportedAmbient i t w) ≤ 1 :=
  X.supportedAmbient_norm_le i t w

-- 05: the test path stays AC with zero regularization coefficient.
example (X : PrimalACCharacteristicData O a pole 0 p teacher initial)
    [IsProbabilityMeasure teacher] (hp : 2 < p)
    (phi : Weight d → Real) (hphi : ContDiff Real 1 phi)
    (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (initial i).support)
    (s t : Real) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    AbsolutelyContinuousOnInterval (fun r => phi (X.characteristic i r w).val) t s :=
  X.smoothTest_ac le_rfl hp phi hphi i w hw t s ht hs

-- 06: product integrability includes a zero-length time interval.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (phi : Weight d → Real) (hphi : ContDiff Real 1 phi) (i : Fin 2) :
    Integrable (fun tw : Real × UnitSphere d => X.testFlux phi i tw.1 tw.2)
      ((volume.restrict (uIcc (0 : Real) 0)).prod (initial i)) :=
  X.testFlux_integrable_prod hl hp phi hphi i 0 0 le_rfl le_rfl

-- 07: signed Fubini includes reversed endpoints and true iterated integrability.
example (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    (f : Real → UnitSphere d → Weight d) (s t : Real)
    (hf : Integrable (fun rw : Real × UnitSphere d => f rw.1 rw.2)
      ((volume.restrict (uIcc t s)).prod mu)) :
    IntervalIntegrable (fun r => ∫ w, f r w ∂mu) volume t s ∧
    Integrable (fun w => ∫ r in t..s, f r w) mu ∧
    (∫ w, (∫ r in t..s, f r w) ∂mu) = ∫ r in t..s, (∫ w, f r w ∂mu) :=
  signed_integral_fubini mu f t s hf

-- 08: spatial flux integrability is claimed only at the original AE times.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (phi : Weight d → Real) (hphi : ContDiff Real 1 phi) (i : Fin 2) :
    ∀ᵐ t ∂volume.restrict (Ici (0 : Real)),
      Integrable (fun w => fderiv Real phi w.val (X.gradient i t w)) (X.measure i t) :=
  X.currentTestFlux_integrable_ae phi hphi i

-- 09: weak continuity is about the original laws and supports reverse time pairs.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (phi : Weight d → Real) (hphi : ContDiff Real 1 phi) (i : Fin 2)
    (s t : Real) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    IntervalIntegrable (X.currentTestFlux phi i) volume t s ∧
    (∫ w, phi w.val ∂X.measure i s) - (∫ w, phi w.val ∂X.measure i t) =
      -(∫ r in t..s, X.currentTestFlux phi i r) :=
  X.weak_continuity_integral hl hp phi hphi i t s ht hs

-- 10: the initial-law boundary is the actual original initial measure.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (phi : Weight d → Real) (hphi : ContDiff Real 1 phi) (i : Fin 2)
    (t : Real) (ht : 0 ≤ t) :
    (∫ w, phi w.val ∂X.measure i t) - (∫ w, phi w.val ∂initial i) =
      -(∫ r in 0..t, X.currentTestFlux phi i r) := by
  simpa only [X.initial_law] using (X.weak_continuity_integral hl hp phi hphi i 0 t le_rfl ht).2

-- 11: test means have genuine local AC, not only pointwise differentiability.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (phi : Weight d → Real) (hphi : ContDiff Real 1 phi) (i : Fin 2)
    (s t : Real) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    AbsolutelyContinuousOnInterval (fun r => ∫ w, phi w.val ∂X.measure i r) s t :=
  X.weak_test_ac hl hp phi hphi i s t hs ht

-- 12: the differential endpoint includes zero lambda and the original field.
example (X : PrimalACCharacteristicData O a pole 0 p teacher initial)
    [IsProbabilityMeasure teacher] (hp : 2 < p)
    (phi : Weight d → Real) (hphi : ContDiff Real 1 phi) (i : Fin 2) :
    ∀ᵐ t ∂volume.restrict (Ici (0 : Real)),
      Integrable (fun w => fderiv Real phi w.val (X.gradient i t w)) (X.measure i t) ∧
      HasDerivAt (fun r => ∫ w, phi w.val ∂X.measure i r)
        (-(∫ w, fderiv Real phi w.val (X.gradient i t w) ∂X.measure i t)) t :=
  X.weak_continuity_ae le_rfl hp phi hphi i

end PaperFormalization.MatrixFactorization
