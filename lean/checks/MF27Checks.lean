import PaperFormalization.MatrixFactorization.PrimalACGlobalAttraction

/-! MF27 boundary/API diagnostics. Execution receipts: `MF27_VALIDATION.md`.
All 53 named declarations are separately type/axiom-audited by the driver.
These tests keep probability domains, AE quantifiers, real times, and the
explicit primal uniqueness premise visible. They are not numerical tests. -/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat -> Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 -> Measure (UnitSphere d)}

-- 01: conull transfer, including atomic laws.
example (mu : Measure (UnitSphere d)) {P : UnitSphere d -> Prop}
    (hP : ∀ᵐ w ∂mu, P w) : ∀ᵐ w ∂reflectedMeasure mu, P (reflect w) :=
  ae_reflected_of_ae mu hP

-- 02: zero tangent.
example (w : UnitSphere d) : (BoundedTangentTest.zero d).reflected.field w = 0 := by
  simp [BoundedTangentTest.reflected_field, BoundedTangentTest.zero]

-- 03: no change in the reflected speed norm.
example (V : BoundedTangentTest d) (w : UnitSphere d) :
    norm (V.reflected.field w) = norm (V.field (reflect w)) := by simp

-- 04: two reflections recover the actual field.
example (V : BoundedTangentTest d) (w : UnitSphere d) :
    V.reflected.reflected.field w = V.field w := V.reflected_twice_field w

-- 05: either sign of time is allowed.
example (V : BoundedTangentTest d) (s : Real) (w : UnitSphere d) :
    V.reflected.expMap (-s) w = reflect (V.expMap (-s) (reflect w)) :=
  V.reflected_expMap (-s) w

-- 06: zero-time perturbation.
example (V : BoundedTangentTest d) (w : UnitSphere d) : V.reflected.expMap 0 w = w := by simp

-- 07: full measure equality, not a moment-only test.
example (V : BoundedTangentTest d) (mu : Measure (UnitSphere d)) (t : Real) :
    V.reflected.push (reflectedMeasure mu) t = reflectedMeasure (V.push mu t) :=
  V.reflected_push mu t

-- 08: conjugacy in the derivative's orientation.
example (V : BoundedTangentTest d) (mu : Measure (UnitSphere d)) (t : Real) :
    reflectedMeasure (V.push (reflectedMeasure mu) t) = V.reflected.push mu t :=
  V.push_reflected_inverse mu t

-- 09: zero-time pushed law.
example (V : BoundedTangentTest d) (mu : Measure (UnitSphere d)) :
    V.reflected.push (reflectedMeasure mu) 0 = reflectedMeasure mu := by simp

-- 10: true integrability before the tangent pairing.
example (V : BoundedTangentTest d) (mu : Measure (UnitSphere d))
    (g : UnitSphere d -> Weight d) (hg : Measurable g) (hi : Integrable g mu) :
    Integrable (fun w => inner Real (-g (reflect w)) (V.field w)) (reflectedMeasure mu) :=
  V.reflected_pairing_integrable mu g hg hi

-- 11: the sign of the reflected tangent pairing.
example (V : BoundedTangentTest d) (mu : Measure (UnitSphere d))
    (g : UnitSphere d -> Weight d) (hg : Measurable g) (hi : Integrable g mu) :
    (∫ w, inner Real (-g (reflect w)) (V.field w) ∂reflectedMeasure mu) =
      ∫ w, inner Real (g w) (V.reflected.field w) ∂mu :=
  V.reflected_pairing mu g hg hi

-- 12: no classical dual gradient in the primal reflection theorem.
example (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    (J : Measure (UnitSphere d) -> Real) (g : UnitSphere d -> Weight d)
    (H : HasSphereFirstVariation mu J g) :
    HasSphereFirstVariation (reflectedMeasure mu) (fun nu => J (reflectedMeasure nu))
      (fun w => -g (reflect w)) := H.reflected

-- 13: functional equality is required only on probability measures.
example (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    (J K : Measure (UnitSphere d) -> Real) (g : UnitSphere d -> Weight d)
    (H : HasSphereFirstVariation mu J g)
    (he : forall nu, IsProbabilityMeasure nu -> J nu = K nu) :
    HasSphereFirstVariation mu K g := H.congr_on_probability he

-- 14: the symmetric teacher is not reflected.
example (hO : forall n, n ∈ O -> Odd n) (mu : Fin 2 -> Measure (UnitSphere d))
    (hmu : forall i, IsProbabilityMeasure (mu i)) (i : Fin 2)
    (nu : Measure (UnitSphere d)) [IsProbabilityMeasure nu] :
    sourcePartialObjective O a pole lambda p (reflectionExchangePair mu) teacher i
      (reflectedMeasure nu) = sourcePartialObjective O a pole lambda p mu teacher i.rev nu :=
  sourcePartialObjective_reflected_active O a hO pole lambda p mu hmu teacher i nu

-- 15: transform both complete partial first variations.
example (hO : forall n, n ∈ O -> Odd n) (mu : Fin 2 -> Measure (UnitSphere d))
    (hmu : forall i, IsProbabilityMeasure (mu i)) (g : Fin 2 -> UnitSphere d -> Weight d)
    (H : forall i, HasSphereFirstVariation (mu i)
      (sourcePartialObjective O a pole lambda p mu teacher i) (g i)) :
    forall i, HasSphereFirstVariation (reflectionExchangePair mu i)
      (sourcePartialObjective O a pole lambda p (reflectionExchangePair mu) teacher i)
      (fun w => -g i.rev (reflect w)) :=
  source_primal_firstVariation_reflection_exchange O a hO pole lambda p mu hmu teacher g H

-- 16: actual joint Borel pullback, not separate measurability.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial) (i : Fin 2) :
    Measurable (fun tw : Real × UnitSphere d =>
      X.reflectionGradient i tw.1 (X.reflectionCharacteristic i tw.1 tw.2)) :=
  X.reflectionPullback_measurable i

-- 17: exact original-law pushforward, even at unused negative-time representatives.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (hO : forall n, n ∈ O -> Odd n) (i : Fin 2) (t : Real) :
    (X.reflectionExchange hO).measure i t = reflectedMeasure (X.measure i.rev t) :=
  X.reflectionExchange_measure hO i t

-- 18: original characteristic maps, not substitute solutions.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (hO : forall n, n ∈ O -> Odd n) (i : Fin 2) (t : Real) (w : UnitSphere d) :
    (X.reflectionExchange hO).characteristic i t w = reflect (X.characteristic i.rev t (reflect w)) := rfl

-- 19: original measurable gradient representative transforms with a minus sign.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (hO : forall n, n ∈ O -> Odd n) (i : Fin 2) (t : Real) (w : UnitSphere d) :
    (X.reflectionExchange hO).gradient i t w = -X.gradient i.rev t (reflect w) := rfl

-- 20: involution of actual maps.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (hO : forall n, n ∈ O -> Odd n) (i : Fin 2) (t : Real) (w : UnitSphere d) :
    ((X.reflectionExchange hO).reflectionExchange hO).characteristic i t w = X.characteristic i t w :=
  X.reflectionExchange_twice_characteristic hO i t w

-- 21: supported path uniqueness suffices; finite-cap uniqueness is absent.
example (hu : PrimalACPathUnique O a pole lambda p teacher initial) :
    PrimalACLawUnique O a pole lambda p teacher initial := hu.law_unique

-- 22: branch invariance from GLOBAL competitors.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (hO : forall n, n ∈ O -> Odd n) (hu : PrimalACLawUnique O a pole lambda p teacher initial)
    (hi : initial 1 = reflectedMeasure (initial 0)) :
    forall t, 0 ≤ t -> X.measure 1 t = reflectedMeasure (X.measure 0 t) :=
  X.antibranch_of_global_unique hO hu hi

-- 23: a concrete odd degree; no moment injectivity is invoked.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (hO : forall n, n ∈ O -> Odd n) (hu : PrimalACLawUnique O a pole lambda p teacher initial)
    (hi : initial 1 = reflectedMeasure (initial 0)) (t : Real) (ht : 0 ≤ t) :
    symmetricMoment (X.measure 0 t) (X.measure 1 t) 1 = 0 :=
  X.symmetric_odd_moment_zero hO hu hi t ht 1 (by decide)

-- 24: covariance does not need positive regularization or an exponent restriction.
noncomputable section
example (X : PrimalACCharacteristicData O a pole 0 p teacher initial)
    (hO : forall n, n ∈ O -> Odd n) :
    PrimalACCharacteristicData O a pole 0 p teacher (reflectionExchangePair initial) :=
  X.reflectionExchange hO
end

-- 25: true initial squared transport, with the source normalization.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial) :
    X.transport 0 = productAntipodalTransportSq pole (initial 0) (initial 1) := X.transport_initial

-- 26: zero transport is not excluded.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial) (t : Real) :
    0 ≤ X.transport t := X.transport_nonneg t

-- 27: initial fit value is not silently set to zero.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial) :
    X.objective 0 = modelObjective O a pole lambda p (initial 0) (initial 1) teacher teacher :=
  X.objective_initial

-- 28: zero initial transport gives stationary laws, including t=0.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (H : PrimalACGlobalEstimates X)
    (hz : productAntipodalTransportSq pole (initial 0) (initial 1) = 0) :
    forall i t, 0 ≤ t -> X.measure i t = antipodalMeasure pole :=
  H.zero_initial_stationary_laws hz

-- 29: representation is reconstructed AFTER confinement and keeps the laws.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p) (r : Real)
    (hcaps : forall i t, 0 ≤ t -> TwoCapClass pole r (X.measure i t)) :
    (X.toPotentialAfterConfinement hl hp r hcaps).measure = X.measure := rfl

-- 30: it also keeps every original map, without another uniqueness call.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p) (r : Real)
    (hcaps : forall i t, 0 ≤ t -> TwoCapClass pole r (X.measure i t)) :
    (X.toPotentialAfterConfinement hl hp r hcaps).characteristic = X.characteristic := rfl

-- 31: transfer of ESTIMATES, without potential-class uniqueness.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (H : PrimalACGlobalEstimates X) [IsProbabilityMeasure teacher]
    (hl : 0 ≤ lambda) (hp : 2 < p) (r : Real)
    (hcaps : forall i t, 0 ≤ t -> TwoCapClass pole r (X.measure i t)) :
    PotentialGlobalEstimates (X.toPotentialAfterConfinement hl hp r hcaps) :=
  H.toPotentialEstimates hl hp r hcaps

-- 32: degree zero is ONE, unlike odd moments.
example (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    (i : Fin 2) (t : Real) (I : Fin 0 -> Fin d) : rawMoment (X.measure i t) 0 I = 1 := by
  letI := X.measure_probability i t
  exact rawMoment_zero_apply (X.measure i t) I

section GlobalCases
variable (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
  [IsProbabilityMeasure teacher] (hO : forall n, n ∈ O -> Odd n)
  (hu : PrimalACLawUnique O a pole lambda p teacher initial)
  (hi : initial 1 = reflectedMeasure (initial 0))
  (r : Real) (hc : forall i, TwoCapClass pole r (initial i))
  (hl : 0 < lambda) (hp : 2 < p) (hp3 : p < 3)
  (zstar : Real) (hzstar : 0 < zstar)
  (hrad : sourceRadialConstant d O a teacher*zstar^((4-p)/2) ≤ lambda/2)
  (hforce : (sourceFittingConstant d O a teacher/lambda)*zstar^((3-p)/2) ≤ r/2)
  (hinit : productAntipodalTransportSq pole (initial 0) (initial 1) ≤ zstar)
include hO hu hi hc hl hp hp3 hzstar hrad hforce hinit

-- 33: caps are an OUTPUT from closed initial margins.
example : (forall i t, 0 ≤ t -> TwoCapClass pole r (X.measure i t)) ∧ PrimalACGlobalEstimates X :=
  X.source_global_estimates hO hu hi r hc hl hp hp3 zstar hzstar hrad hforce hinit

-- 34: exercise the final theorem, not only separate scalar helpers.
example : X.sourceBarrier < r ∧
    Tendsto X.transport atTop (𝓝 0) ∧
    (forall i n, Odd n -> Tendsto (fun t => rawMoment (X.measure i t) n) atTop (𝓝 0)) := by
  obtain ⟨hB, hb, hpart, hcaps, hsupp, H, hZ, hD, hmarg, hmom, hodd, hs, ha, he, hz⟩ :=
    primal_ac_global_attraction X hO hu hi r hc hl hp hp3 zstar hzstar hrad hforce hinit
  exact ⟨hB, hZ, hodd⟩

-- 35: the energy uses the ORIGINAL measurable gradient, only at legitimate AE times.
example : ∀ᵐ t ∂volume.restrict (Ioi (0 : Real)),
    HasDerivAt X.objective (-X.originalGradientEnergy t) t := by
  obtain ⟨hcaps, H⟩ := X.source_global_estimates hO hu hi r hc hl hp hp3 zstar hzstar hrad hforce hinit
  filter_upwards [H.original_energy_identity_ae hl hp r hcaps] with t ht
  exact ht.2.1

-- 36: closed zero initial data survives the assembled final endpoint.
example (hz : productAntipodalTransportSq pole (initial 0) (initial 1) = 0) :
    forall i t, 0 ≤ t -> X.measure i t = antipodalMeasure pole := by
  have H := (X.source_global_estimates hO hu hi r hc hl hp hp3 zstar hzstar hrad hforce hinit).2
  exact H.zero_initial_stationary_laws hz

end GlobalCases
end PaperFormalization.MatrixFactorization
