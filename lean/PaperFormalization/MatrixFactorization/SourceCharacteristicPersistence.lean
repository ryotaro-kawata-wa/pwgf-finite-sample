import PaperFormalization.MatrixFactorization.SourceInitialMargin
import PaperFormalization.MatrixFactorization.SourceCharacteristicRadial
import PaperFormalization.MatrixFactorization.SphericalCharacteristicDecayClosure

/-! # The printed initial margin along actual cap-interval characteristics

Only the initial source Cstar margin is supplied. Its closed inequality is
preserved by a scalar first-exit argument applied to the actual transport
curve. The energy identity and exact decay profile are reused from the proved
original-law calculus. No coarse radius, current-smallness assumption, global
cap confinement, or flow existence conclusion is introduced here.
-/
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}

/-- The actual transport stays below its initial value and preserves precisely
the closed printed half-margin, including equality in the initial condition. -/
theorem SphericalCharacteristicSolution.transport_persists_source
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (hsmall0 : sourceRadialConstant d O a teacher*
      (productAntipodalTransportSq pole (initial 0) (initial 1))^((4-p)/2) ≤ lambda/2) :
    AntitoneOn X.transport (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, 0 ≤ X.transport t ∧
        X.transport t ≤ productAntipodalTransportSq pole (initial 0) (initial 1) ∧
        sourceRadialConstant d O a teacher*(X.transport t)^((4-p)/2) ≤ lambda/2 := by
  have he : 2-p/2 = (4-p)/2 := by ring
  have hinit : sourceRadialConstant d O a teacher*(X.transport 0)^(2-p/2) ≤ lambda/2 := by
    simpa only [he,X.transport_initial] using hsmall0
  have hb := scalar_source_initial_margin (f := X.transport) X.time_nonneg hl
    (sourceBranchConstants_nonneg d O a teacher).1 (by linarith : 1 < p/2) (by linarith : p/2 < 2)
    X.productTransport_continuousOn
    (fun t ht => (X.productTransport_hasDerivAt hp t ht).differentiableAt)
    X.productTransport_nonneg
    (fun t ht => X.transport_deriv_le_source_remainder hO hunique hinitial hp t ht) hinit
  refine ⟨hb.1,?_⟩
  intro t ht
  exact ⟨X.productTransport_nonneg t ht,
    by simpa only [X.transport_initial] using hb.2.1 t ht,
    by simpa only [he] using hb.2.2.1 t ht⟩

/-- The initial printed margin suffices for the actual transport differential
inequality at every interior time; no positive-time margin is supplied. -/
theorem SphericalCharacteristicSolution.transport_deriv_le_source_from_initial
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (hsmall0 : sourceRadialConstant d O a teacher*
      (productAntipodalTransportSq pole (initial 0) (initial 1))^((4-p)/2) ≤ lambda/2)
    (t : Real) (ht : t ∈ Ioo 0 T) :
    deriv X.transport t ≤ -lambda*(X.transport t)^(p/2) := by
  have hs := (X.transport_persists_source hO hunique hinitial hl hp hp4 hsmall0).2 t
    ⟨ht.1.le,ht.2.le⟩
  have he : 2-p/2 = (4-p)/2 := by ring
  have hm : sourceRadialConstant d O a teacher*(X.transport t)^(2-p/2) ≤ lambda/2 := by
    simpa only [he] using hs.2.2
  have hb := source_power_error_absorbed hs.1 (by linarith : 0 < p/2)
    (by linarith : p/2 < 2) hm
  have hi := X.transport_deriv_le_source_remainder hO hunique hinitial hp t ht
  nlinarith

/-- The exact source decay profile follows for every closed time, including
zero initial transport and trajectories which reach zero. -/
theorem SphericalCharacteristicSolution.transport_decay_source
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (hsmall0 : sourceRadialConstant d O a teacher*
      (productAntipodalTransportSq pole (initial 0) (initial 1))^((4-p)/2) ≤ lambda/2) :
    AntitoneOn X.transport (Icc 0 T) ∧
      (∀ t ∈ Ioo 0 T, deriv X.transport t ≤ -lambda*(X.transport t)^(p/2)) ∧
      ∀ t ∈ Icc 0 T, 0 ≤ X.transport t ∧
        X.transport t ≤ powerDecayProfile lambda ((p-2)/2)
          (productAntipodalTransportSq pole (initial 0) (initial 1)) t ∧
        powerDecayProfile lambda ((p-2)/2)
          (productAntipodalTransportSq pole (initial 0) (initial 1)) t ≤
            productAntipodalTransportSq pole (initial 0) (initial 1) := by
  have hs := X.transport_persists_source hO hunique hinitial hl hp hp4 hsmall0
  have hi := X.transport_deriv_le_source_from_initial hO hunique hinitial hl hp hp4 hsmall0
  have ha : 0 < (p-2)/2 := by linarith
  have hdec := scalar_power_decay (f := X.transport) X.time_nonneg hl.le ha
    X.productTransport_continuousOn
    (fun t ht => (X.productTransport_hasDerivAt hp t ht).differentiableAt)
    X.productTransport_nonneg (by
      have he : (p-2)/2+1 = p/2 := by ring
      simpa only [he] using hi)
  refine ⟨hs.1,hi,?_⟩
  intro t ht
  have h0 := X.productTransport_nonneg 0 ⟨le_rfl,X.time_nonneg⟩
  change 0 ≤ X.transport 0 at h0
  rw [X.transport_initial] at h0
  refine ⟨(hs.2 t ht).1,?_,powerDecayProfile_le_initial hl.le ha h0 ht.1⟩
  simpa only [X.transport_initial] using hdec.2 t ht

/-- Zero hitting persists on the remaining cap interval under the printed
initial condition, with no inverse power evaluated at zero. -/
theorem SphericalCharacteristicSolution.transport_zero_persists_source
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (hsmall0 : sourceRadialConstant d O a teacher*
      (productAntipodalTransportSq pole (initial 0) (initial 1))^((4-p)/2) ≤ lambda/2)
    (s t : Real) (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T)
    (hst : s ≤ t) (hz : X.transport s = 0) : X.transport t = 0 :=
  scalar_zero_persists X.productTransport_nonneg
    (X.transport_persists_source hO hunique hinitial hl hp hp4 hsmall0).1 hs ht hst hz

/-- The full original objective satisfies the printed quantitative energy
bound from the initial source margin alone. -/
theorem SphericalCharacteristicSolution.objective_deriv_le_source_from_initial
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (hsmall0 : sourceRadialConstant d O a teacher*
      (productAntipodalTransportSq pole (initial 0) (initial 1))^((4-p)/2) ≤ lambda/2)
    (t : Real) (ht : t ∈ Ioo 0 T) :
    deriv X.objective t ≤ -(lambda^2/4)*(X.transport t)^(p-1) := by
  have htc : t ∈ Icc (0 : Real) T := ⟨ht.1.le,ht.2.le⟩
  have hs := (X.transport_persists_source hO hunique hinitial hl hp hp4 hsmall0).2 t htc
  have hg := X.gradientEnergy_lower_source hO hunique hinitial hl hp hp4 t htc hs.2.2
  rw [(X.objective_hasDerivAt hp t ht).deriv]
  simpa only [neg_mul] using neg_le_neg hg

/-- Source-facing dissipation on the given cap interval, using the literal
printed initial Cstar condition and the exact source decay denominator. -/
theorem spherical_characteristic_source_cap_interval_dissipation
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (hsmall0 : sourceRadialConstant d O a teacher*
      (productAntipodalTransportSq pole (initial 0) (initial 1))^((4-p)/2) ≤ lambda/2) :
    (∀ i t, t ∈ Icc (0 : Real) T →
      Integrable (fun w => norm (sphericalObjectiveGradient O a pole lambda p
        (X.measure 0 t) (X.measure 1 t) teacher teacher i w)^2) (X.measure i t)) ∧
    AntitoneOn X.objective (Icc 0 T) ∧ AntitoneOn X.transport (Icc 0 T) ∧
    (∀ t ∈ Icc (0 : Real) T, 0 ≤ X.transport t ∧
      X.transport t ≤ (X.transport 0) /
        (1+(lambda*(p-2)/2)*(X.transport 0)^((p-2)/2)*t)^(2/(p-2)) ∧
      X.transport t ≤ X.transport 0 ∧
      sourceRadialConstant d O a teacher*(X.transport t)^((4-p)/2) ≤ lambda/2 ∧
      X.objective t ≤ X.objective 0) ∧
    (∀ t ∈ Ioo (0 : Real) T,
      HasDerivAt X.objective (-X.gradientEnergy t) t ∧
      deriv X.transport t ≤ -lambda*(X.transport t)^(p/2) ∧
      deriv X.objective t ≤ -(lambda^2/4)*(X.transport t)^(p-1) ∧
      (0 < X.transport t → deriv X.objective t < 0)) ∧
    (∀ s t, s ∈ Icc (0 : Real) T → t ∈ Icc (0 : Real) T → s ≤ t →
      X.transport s = 0 → ∀ i : Fin 2, X.measure i t = antipodalMeasure pole) := by
  have hdec := X.transport_decay_source hO hunique hinitial hl hp hp4 hsmall0
  have hper := X.transport_persists_source hO hunique hinitial hl hp hp4 hsmall0
  have henergy := X.objective_antitoneOn hp
  refine ⟨?_,henergy,hdec.1,?_,?_,?_⟩
  · intro i t ht
    exact X.gradientEnergy_integrable i t ht
  · intro t ht
    have hd := hdec.2.2 t ht
    have hm := hper.2 t ht
    refine ⟨hd.1,?_,?_,hm.2.2,henergy ⟨le_rfl,X.time_nonneg⟩ ht ht.1⟩
    · rw [X.transport_initial]
      simpa only [powerDecayProfile_source_form] using hd.2.1
    · simpa only [X.transport_initial] using hm.2.1
  · intro t ht
    have he := X.objective_deriv_le_source_from_initial hO hunique hinitial hl hp hp4 hsmall0 t ht
    refine ⟨X.objective_hasDerivAt hp t ht,hdec.2.1 t ht,he,?_⟩
    intro hz
    exact he.trans_lt (mul_neg_of_neg_of_pos (by nlinarith [sq_pos_of_pos hl])
      (Real.rpow_pos_of_pos hz _))
  · intro s t hs ht hst hz
    exact X.zero_transport_laws t ht
      (X.transport_zero_persists_source hO hunique hinitial hl hp hp4 hsmall0 s t hs ht hst hz)

end PaperFormalization.MatrixFactorization
