import PaperFormalization.MatrixFactorization.PrimalACCapRestriction

/-! MF26 boundary/API diagnostics. Execution receipts: `MF26_VALIDATION.md`.
The whole pending declaration inventory is separately checked and axiom-audited
by the unit driver. These examples exercise the actual source-facing bridge. -/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

-- 01: the pole is included in the continuous gradient formula.
example (w : UnitSphere d) : ContinuousAt (poleGradient w) w :=
  poleGradient_continuousAt_short w w (by simpa using Real.pi_pos)

-- 02: the positive assigned pole is included, without a nonzero-radius-of-point premise.
example (r : Real) (hr : 0 < r) (hrpi : r < Real.pi/2) :
    ContinuousAt (assignedGradient pole) pole :=
  assignedGradient_continuousAt_caps pole r hrpi pole
    (Or.inl (sphericalCap_pole_mem pole r hr))

-- 03: the negative assigned pole is also included.
example (r : Real) (hr : 0 < r) (hrpi : r < Real.pi/2) :
    ContinuousAt (assignedGradient pole) (reflect pole) :=
  assignedGradient_continuousAt_caps pole r hrpi (reflect pole)
    (Or.inr (sphericalCap_pole_mem (reflect pole) r hr))

section Prefix
variable (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
  [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
  (r T : Real) (hT : 0 ≤ T)
  (hc : ∀ i t, t ∈ Icc (0 : Real) T → TwoCapClass pole r (X.measure i t))

-- 04: original-measure continuous tests include t=0.
example (i : Fin 2) (f : UnitSphere d → Real) (hf : Continuous f) :
    ContinuousOn (fun t => ∫ w, f w ∂X.measure i t) (Ici (0 : Real)) :=
  X.testIntegral_continuousOn hl hp i f hf

-- 05: Gaussian input zero does not need a positive-norm condition.
example (i : Fin 2) :
    ContinuousOn (fun t => meanFeature (finiteHermiteActivation O a) (X.measure i t) (0 : Weight d))
      (Ici (0 : Real)) :=
  X.meanFeature_continuousOn_time hl hp i 0

-- 06: a good particle prefix yields the existing record without current half-mass premises.
example (hinit : ∀ i, TwoCapClass pole r (initial i))
    (hin : ∀ i w, w ∈ (initial i).support → ∀ t ∈ Icc (0 : Real) T,
      X.characteristic i t w ∈ sphericalCap pole r ∪ sphericalCap (reflect pole) r) :
    ∃ Y : SphericalCharacteristicSolution O a pole r lambda p teacher initial T,
      Y.measure = X.measure ∧ Y.characteristic = X.characteristic :=
  ⟨X.classicalRestrictionOfGoodPrefix hl hp r T hT hinit hin,rfl,rfl⟩

-- 07: both actual fitting factors are covered (here the second).
example :
    ContinuousOn (fun tw : Real × UnitSphere d => sphericalFittingGradient O a
      (X.measure 0 tw.1) (X.measure 1 tw.1) teacher teacher 1 tw.2)
      ((Ici (0 : Real)) ×ˢ (univ : Set (UnitSphere d))) :=
  X.fittingGradient_continuousOn hl hp 1

-- 08: this is the genuine transport infimum, not a new assigned-cost definition.
example :
    ContinuousOn (fun t => productAntipodalTransportSq pole (X.measure 0 t) (X.measure 1 t))
      (Icc (0 : Real) T) :=
  X.capTransport_continuousOn hl hp r T hc

-- 09: no global continuity of the arbitrary representative is assumed.
example (i : Fin 2) :
    ContinuousOn (fun tw : Real × UnitSphere d => X.canonicalPullback i tw.1 tw.2)
      ((Icc (0 : Real) T) ×ˢ (initial i).support) :=
  X.canonicalPullback_continuousOn hl hp r T hT hc i

-- 10: signed segments need no endpoint ordering.
example (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (initial i).support)
    (s t : Real) (hs : s ∈ Icc (0 : Real) T) (ht : t ∈ Icc (0 : Real) T) :
    IntervalIntegrable (fun u => X.canonicalPullback i u w) volume s t :=
  X.canonicalPullback_intervalIntegrable hl hp r T hT hc i w hw s t hs ht

-- 11: joint Borel measurability is derived for the extension.
example (i : Fin 2) :
    Measurable (fun tw : Real × UnitSphere d => X.canonicalPrefixField i T tw.1 tw.2) :=
  X.canonicalPrefixField_measurable hl hp r T hT hc i

-- 12: the extension does not change any supported point in the prefix.
example (i : Fin 2) (t : Real) (ht : t ∈ Icc (0 : Real) T)
    (w : UnitSphere d) (hw : w ∈ (initial i).support) :
    X.canonicalPrefixField i T t w = X.canonicalPullback i t w :=
  X.canonicalPrefixField_eq i T t ht w hw

-- 13: off-prefix zero values belong only to the auxiliary extension.
example (i : Fin 2) (t : Real) (ht : t ∉ Icc (0 : Real) T) (w : UnitSphere d) :
    X.canonicalPrefixField i T t w = 0 := by
  simp [PrimalACCharacteristicData.canonicalPrefixField,ht]

-- 14: no original dynamics outside the support is inferred from zero extension.
example (i : Fin 2) (t : Real) (w : UnitSphere d) (hw : w ∉ (initial i).support) :
    X.canonicalPrefixField i T t w = 0 := by
  simp [PrimalACCharacteristicData.canonicalPrefixField,hw]

-- 15: domination is derived rather than a new certificate input.
example (i : Fin 2) :
    ∃ C : Real, 0 ≤ C ∧ ∀ t w, norm (X.canonicalPrefixField i T t w) ≤ C :=
  X.canonicalPrefixField_bounded hl hp r T hT hc i

-- 16: actual, unextended integral maps are continuous on the closed support.
example (i : Fin 2) (s t : Real) (hs : s ∈ Icc (0 : Real) T) (ht : t ∈ Icc (0 : Real) T) :
    ContinuousOn (fun w => ∫ u in s..t, X.canonicalPullback i u w) (initial i).support :=
  X.canonicalIntegral_continuousOn hl hp r T hT hc i s t hs ht

-- 17: the canonical equation holds at every supported point, not only atoms of positive mass.
example (i : Fin 2) (s t : Real) (hs : s ∈ Icc (0 : Real) T) (ht : t ∈ Icc (0 : Real) T)
    (w : UnitSphere d) (hw : w ∈ (initial i).support) :
    (X.characteristic i t w).val-(X.characteristic i s w).val =
      -(∫ u in s..t, X.canonicalPullback i u w) :=
  (X.canonical_integral_equation_supported hl hp r T hT hc i s t hs ht w hw).2

-- 18: reverse the endpoints without assuming a separate reverse ODE.
example (i : Fin 2) (s t : Real) (hs : s ∈ Icc (0 : Real) T) (ht : t ∈ Icc (0 : Real) T)
    (w : UnitSphere d) (hw : w ∈ (initial i).support) :
    (X.characteristic i s w).val-(X.characteristic i t w).val =
      -(∫ u in t..s, X.canonicalPullback i u w) :=
  (X.canonical_integral_equation_supported hl hp r T hT hc i t s ht hs w hw).2

-- 19: equal-time signed integration is retained.
example (i : Fin 2) (t : Real) (w : UnitSphere d) :
    (∫ u in t..t, X.canonicalPullback i u w) = 0 := by simp

-- 20: classical ODE at every interior time, with no endpoint derivative required.
example (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (initial i).support)
    (t : Real) (ht : t ∈ Ioo (0 : Real) T) :
    HasDerivAt (fun u => (X.characteristic i u w).val)
      (-X.canonicalPullback i t w) t :=
  X.canonical_ode_on_prefix hl hp r T hT hc i w hw t ht

-- 21: literal map and law preservation, not merely equal moments.
example :
    (X.toSphericalCapInterval hl hp r T hT hc).measure = X.measure ∧
    (X.toSphericalCapInterval hl hp r T hT hc).characteristic = X.characteristic :=
  ⟨rfl,rfl⟩

-- 22: zero-length prefix is legitimate and adds no endpoint derivative.
example (hinit : ∀ i, TwoCapClass pole r (initial i)) :
    ∃ Y : SphericalCharacteristicSolution O a pole r lambda p teacher initial 0,
      Y.measure = X.measure ∧ Y.characteristic = X.characteristic := by
  have hzero (i : Fin 2) (t : Real) (ht : t ∈ Icc (0 : Real) 0) :
      TwoCapClass pole r (X.measure i t) := by
    have he : t = 0 := le_antisymm ht.2 ht.1
    subst t
    simpa only [X.initial_law i] using hinit i
  exact ⟨X.toSphericalCapInterval hl hp r 0 (le_refl 0) hzero,rfl,rfl⟩

-- 23: the first classical restriction needs only original initial caps.
example (hinit : ∀ i, TwoCapClass pole r (initial i)) :
    ∃ tau : Real, 0 < tau ∧
      ∃ Y : SphericalCharacteristicSolution O a pole r lambda p teacher initial tau,
        Y.measure = X.measure ∧ Y.characteristic = X.characteristic := by
  rcases primal_ac_classical_first_cap X hl hp r hinit with ⟨htau,Y,hYm,hYp,hint⟩
  exact ⟨_,htau,Y,hYm,hYp⟩

end Prefix

-- 24: lambda=0 is allowed by the bridge; it is not divided out.
example (X : PrimalACCharacteristicData O a pole 0 p teacher initial)
    [IsProbabilityMeasure teacher] (hp : 2 < p) (r : Real)
    (hc : ∀ i, TwoCapClass pole r (initial i)) :
    ∃ tau : Real, 0 < tau ∧
      ∃ Y : SphericalCharacteristicSolution O a pole r 0 p teacher initial tau,
        Y.measure = X.measure ∧ Y.characteristic = X.characteristic := by
  rcases primal_ac_classical_first_cap X (le_refl 0) hp r hc with ⟨htau,Y,hYm,hYp,hint⟩
  exact ⟨_,htau,Y,hYm,hYp⟩

end PaperFormalization.MatrixFactorization
