import PaperFormalization.MatrixFactorization.PrimalACConfinement
import PaperFormalization.MatrixFactorization.PowerDecayAsymptotics

/-! # MF27: sharp all-time estimates on the same primal AC trajectory

Verification status and conditional scope: see `MF27_VALIDATION.md`. The output bundle below is constructed after
confinement, not included among trajectory assumptions. Every finite record
is the MF26 restriction of this one X, with literally the same laws and maps.
Global uniqueness is only used by the preceding global reflection argument.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

noncomputable def PrimalACCharacteristicData.transport
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial) (t : Real) : Real :=
  productAntipodalTransportSq pole (X.measure 0 t) (X.measure 1 t)

noncomputable def PrimalACCharacteristicData.objective
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial) (t : Real) : Real :=
  modelObjective O a pole lambda p (X.measure 0 t) (X.measure 1 t) teacher teacher

/-- Canonical energy. The original measurable representative is related to it
at its actual AE times in PrimalACOriginalEnergy, not pointwise by definition. -/
noncomputable def PrimalACCharacteristicData.gradientEnergy
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial) (t : Real) : Real :=
  ∑ i : Fin 2, ∫ w, norm (sphericalObjectiveGradient O a pole lambda p
    (X.measure 0 t) (X.measure 1 t) teacher teacher i w)^2 ∂X.measure i t

@[simp] theorem PrimalACCharacteristicData.transport_initial
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial) :
    X.transport 0 = productAntipodalTransportSq pole (initial 0) (initial 1) := by
  simp only [PrimalACCharacteristicData.transport, X.initial_law]

@[simp] theorem PrimalACCharacteristicData.objective_initial
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial) :
    X.objective 0 = modelObjective O a pole lambda p (initial 0) (initial 1) teacher teacher := by
  simp only [PrimalACCharacteristicData.objective, X.initial_law]

theorem PrimalACCharacteristicData.transport_nonneg
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial) (t : Real) :
    0 ≤ X.transport t := by
  letI := X.measure_probability 0 t
  letI := X.measure_probability 1 t
  exact add_nonneg (sphericalWassersteinSq_nonneg _ _) (sphericalWassersteinSq_nonneg _ _)

/-- Output only: no estimate or all-time cap certificate is a new model field. -/
structure PrimalACGlobalEstimates
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial) : Prop where
  transport_antitone : AntitoneOn X.transport (Ici (0 : Real))
  objective_antitone : AntitoneOn X.objective (Ici (0 : Real))
  decay : ∀ t : Real, 0 ≤ t →
    0 ≤ X.transport t ∧
    X.transport t ≤ powerDecayProfile lambda ((p-2)/2) (X.transport 0) t ∧
    powerDecayProfile lambda ((p-2)/2) (X.transport 0) t ≤ X.transport 0
  gradient_integrable : ∀ i t, 0 ≤ t →
    Integrable (fun w => norm (sphericalObjectiveGradient O a pole lambda p
      (X.measure 0 t) (X.measure 1 t) teacher teacher i w)^2) (X.measure i t)
  energy_derivative : ∀ t : Real, 0 < t → HasDerivAt X.objective (-X.gradientEnergy t) t
  transport_differential : ∀ t : Real, 0 < t →
    deriv X.transport t ≤ -lambda*(X.transport t)^(p/2)
  energy_differential : ∀ t : Real, 0 < t →
    deriv X.objective t ≤ -(lambda^2/4)*(X.transport t)^(p-1)
  zero_laws : ∀ s t : Real, 0 ≤ s → s ≤ t → X.transport s = 0 →
    ∀ i : Fin 2, X.measure i t = antipodalMeasure pole

/-- Adapter after caps and the branch have been proved; finite uniqueness is absent.
The horizon t+1 keeps every positive evaluation time in the ordinary interior. -/
theorem PrimalACCharacteristicData.global_estimates_of_caps
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (r : Real) (hcaps : ∀ i t, 0 ≤ t → TwoCapClass pole r (X.measure i t))
    (hb : ∀ t : Real, 0 ≤ t → X.measure 1 t = reflectedMeasure (X.measure 0 t))
    (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (hsmall0 : sourceRadialConstant d O a teacher*
      (productAntipodalTransportSq pole (initial 0) (initial 1))^((4-p)/2) ≤ lambda/2) :
    PrimalACGlobalEstimates X := by
  let Y := fun (U : Real) (hU : 0 ≤ U) =>
    X.toSphericalCapInterval hl.le hp r U hU (fun i t ht => hcaps i t ht.1)
  have hbranch (U : Real) (hU : 0 ≤ U) : ∀ t ∈ Icc (0 : Real) U,
      (Y U hU).measure 1 t = reflectedMeasure ((Y U hU).measure 0 t) :=
    fun t ht => hb t ht.1
  have hanti : AntitoneOn X.transport (Ici (0 : Real)) := by
    intro s hs t ht hst
    exact ((Y t ht).transport_persists_of_branch hO (hbranch t ht) hl hp hp4 hsmall0).1
      ⟨hs, hst⟩ ⟨ht, le_rfl⟩ hst
  have hdec : ∀ t : Real, 0 ≤ t →
      0 ≤ X.transport t ∧
      X.transport t ≤ powerDecayProfile lambda ((p-2)/2) (X.transport 0) t ∧
      powerDecayProfile lambda ((p-2)/2) (X.transport 0) t ≤ X.transport 0 := by
    intro t ht
    have hh := ((Y t ht).transport_decay_of_branch hO (hbranch t ht) hl hp hp4 hsmall0).2.2
      t ⟨ht, le_rfl⟩
    have he : (Y t ht).transport t = X.transport t := rfl
    simpa only [he, X.transport_initial] using hh
  refine ⟨hanti, ?_, hdec, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs t ht hst
    exact (Y t ht).objective_antitoneOn hp ⟨hs, hst⟩ ⟨ht, le_rfl⟩ hst
  · intro i t ht
    exact (Y t ht).gradientEnergy_integrable i t ⟨ht, le_rfl⟩
  · intro t ht
    exact (Y (t+1) (by linarith)).objective_hasDerivAt hp t ⟨ht, by linarith⟩
  · intro t ht
    exact (Y (t+1) (by linarith)).transport_differential_of_branch
      hO (hbranch (t+1) (by linarith)) hl hp hp4 hsmall0 t ⟨ht, by linarith⟩
  · intro t ht
    exact ((Y (t+1) (by linarith)).energy_differential_of_branch
      hO (hbranch (t+1) (by linarith)) hl hp hp4 hsmall0 t ⟨ht, by linarith⟩).2
  · intro s t hs hst hz i
    have ht : 0 ≤ t := hs.trans hst
    have hzero : X.transport t = 0 :=
      le_antisymm (by simpa only [hz] using hanti hs ht hst) (hdec t ht).1
    exact (Y t ht).zero_transport_laws t ⟨ht, le_rfl⟩ hzero i

/-- Initial source margins and the explicit global primal uniqueness supply
both confinement and every dynamical estimate. No potential data are supplied. -/
theorem PrimalACCharacteristicData.source_global_estimates
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hu : PrimalACLawUnique O a pole lambda p teacher initial)
    (hi : initial 1 = reflectedMeasure (initial 0))
    (r : Real) (hc : ∀ i, TwoCapClass pole r (initial i))
    (hl : 0 < lambda) (hp : 2 < p) (hp3 : p < 3)
    (zstar : Real) (hzstar : 0 < zstar)
    (hrad : sourceRadialConstant d O a teacher*zstar^((4-p)/2) ≤ lambda/2)
    (hforce : (sourceFittingConstant d O a teacher/lambda)*zstar^((3-p)/2) ≤ r/2)
    (hinit : productAntipodalTransportSq pole (initial 0) (initial 1) ≤ zstar) :
    (∀ i t, 0 ≤ t → TwoCapClass pole r (X.measure i t)) ∧ PrimalACGlobalEstimates X := by
  have hconf := X.source_confinement hO hu hi r hc hl hp hp3 zstar hzstar hrad hforce hinit
  have hcaps := hconf.2.2.1
  have hZ0 : 0 ≤ productAntipodalTransportSq pole (initial 0) (initial 1) := by
    simpa only [X.transport_initial] using X.transport_nonneg 0
  have hm := source_basin_initial_margins O a teacher lambda p r zstar
    (productAntipodalTransportSq pole (initial 0) (initial 1)) hl hp3 hZ0 hinit hrad hforce
  exact ⟨hcaps, X.global_estimates_of_caps hO r hcaps
    (X.antibranch_of_global_unique hO hu hi) hl hp (by linarith) hm.1⟩

end PaperFormalization.MatrixFactorization
