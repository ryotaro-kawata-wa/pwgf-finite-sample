import PaperFormalization.MatrixFactorization.SphericalCharacteristicEnergy

/-! # MF15: source-facing finite-cap interval endpoint

This endpoint calls the actual-law constructions, not
an abstract supplied energy inequality. The initial transport is allowed to
equal the existing coarse radius, and zero hitting identifies both original
current laws. It remains an estimate on an already given cap interval.
The particle/support barrier, global confinement, and the manuscript's sharp
L4 constants are explicitly NOT conclusions of this checkpoint.
-/
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}

/-- At zero actual product transport, neither marginal can hide positive cost. -/
theorem SphericalCharacteristicSolution.zero_transport_laws
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (t : Real) (ht : t ∈ Icc 0 T) (hz : X.transport t = 0) :
    ∀ i : Fin 2, X.measure i t = antipodalMeasure pole := by
  letI : IsProbabilityMeasure (X.measure 0 t) := (X.cap 0 t ht).probability
  letI : IsProbabilityMeasure (X.measure 1 t) := (X.cap 1 t ht).probability
  have h0 := sphericalWassersteinSq_nonneg (X.measure 0 t) (antipodalMeasure pole)
  have h1 := sphericalWassersteinSq_nonneg (X.measure 1 t) (antipodalMeasure pole)
  change sphericalWassersteinSq (X.measure 0 t) (antipodalMeasure pole) +
    sphericalWassersteinSq (X.measure 1 t) (antipodalMeasure pole) = 0 at hz
  have hz0 : sphericalWassersteinSq (X.measure 0 t) (antipodalMeasure pole) = 0 := by
    linarith
  have hz1 : sphericalWassersteinSq (X.measure 1 t) (antipodalMeasure pole) = 0 := by
    linarith
  intro i
  fin_cases i
  · exact zeroTransport_eq_antipodal pole radius _ (X.cap 0 t ht) hz0
  · exact zeroTransport_eq_antipodal pole radius _ (X.cap 1 t ht) hz1

/-- The time-zero value is the actual source objective of the initial laws. -/
@[simp] theorem SphericalCharacteristicSolution.objective_initial
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T) :
    X.objective 0 = modelObjective O a pole lambda p (initial 0) (initial 1) teacher teacher := by
  simp only [SphericalCharacteristicSolution.objective,X.initial_law]

/-- All source-facing conclusions available on the fixed cap interval.
Only source uniqueness, branch initial data, parameters and the INITIAL coarse
squared-distance bound are inputs. No positive-time smallness, pre-assumed
energy chain rule, no-hitting condition, or global continuity of the field is
added. The printed decay expression is exact; the basin coefficient is coarse. -/
theorem spherical_characteristic_cap_interval_dissipation
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (hsmall0 : productAntipodalTransportSq pole (initial 0) (initial 1) ≤
      coarseRadialRadius lambda p (fittingCurvatureConstant d O a/64)) :
    (∀ i t, t ∈ Icc (0 : Real) T →
      Integrable (fun w => norm (sphericalObjectiveGradient O a pole lambda p
        (X.measure 0 t) (X.measure 1 t) teacher teacher i w)^2) (X.measure i t)) ∧
    AntitoneOn X.objective (Icc 0 T) ∧ AntitoneOn X.transport (Icc 0 T) ∧
    (∀ t ∈ Icc (0 : Real) T,
      0 ≤ X.transport t ∧
      X.transport t ≤
        (X.transport 0) /
          (1+(lambda*(p-2)/2)*(X.transport 0)^((p-2)/2)*t)^(2/(p-2)) ∧
      X.transport t ≤ X.transport 0 ∧
      X.objective t ≤ X.objective 0) ∧
    (∀ t ∈ Ioo (0 : Real) T,
      HasDerivAt X.objective (-X.gradientEnergy t) t ∧
      deriv X.transport t ≤ -lambda*(X.transport t)^(p/2) ∧
      deriv X.objective t ≤ -(lambda^2/4)*(X.transport t)^(p-1) ∧
      (0 < X.transport t → deriv X.objective t < 0)) ∧
    (∀ s t, s ∈ Icc (0 : Real) T → t ∈ Icc (0 : Real) T → s ≤ t →
      X.transport s = 0 → ∀ i : Fin 2, X.measure i t = antipodalMeasure pole) := by
  have hdec := X.transport_decay hO hunique hinitial hl hp hp4 hsmall0
  have hper := X.transport_persists hO hunique hinitial hl hp hp4 hsmall0
  have henergy := X.objective_antitoneOn hp
  refine ⟨?_,henergy,hdec.1,?_,?_,?_⟩
  · intro i t ht
    exact X.gradientEnergy_integrable i t ht
  · intro t ht
    have hd := hdec.2.2 t ht
    have hm := hper.2 t ht
    refine ⟨hd.1,?_,?_,henergy ⟨le_rfl,X.time_nonneg⟩ ht ht.1⟩
    · rw [X.transport_initial]
      simpa only [powerDecayProfile_source_form] using hd.2.1
    · simpa only [X.transport_initial] using hm.2.1
  · intro t ht
    exact ⟨X.objective_hasDerivAt hp t ht,hdec.2.1 t ht,
      X.objective_deriv_le_from_initial hO hunique hinitial hl hp hp4 hsmall0 t ht,
      X.objective_deriv_negative_from_initial hO hunique hinitial hl hp hp4 hsmall0 t ht⟩
  · intro s t hs ht hst hz
    exact X.zero_transport_laws t ht
      (X.transport_zero_persists hO hunique hinitial hl hp hp4 hsmall0 s t hs ht hst hz)

end PaperFormalization.MatrixFactorization
