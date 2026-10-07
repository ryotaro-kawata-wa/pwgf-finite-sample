import PaperFormalization.MatrixFactorization.PotentialCharacteristicConfinement
import PaperFormalization.MatrixFactorization.PowerDecayAsymptotics

/-! # MF23: estimates on one represented global trajectory

Execution records: `MF23_VALIDATION.md`.

Every finite object below is a literal restriction of
one global trajectory. Global cap membership is proved by source_confinement
before the source-facing theorem invokes this file's restriction adapter.
PotentialGlobalEstimates is an OUTPUT proposition, never a model premise.
The source-to-classical-optimal-potential representation bridge remains open.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

noncomputable def PotentialCharacteristicFlow.transport
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial) (t : Real) : Real :=
  productAntipodalTransportSq pole (X.measure 0 t) (X.measure 1 t)

noncomputable def PotentialCharacteristicFlow.objective
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial) (t : Real) : Real :=
  modelObjective O a pole lambda p (X.measure 0 t) (X.measure 1 t) teacher teacher

noncomputable def PotentialCharacteristicFlow.gradientEnergy
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial) (t : Real) : Real :=
  ∑ i : Fin 2, ∫ w, norm (sphericalObjectiveGradient O a pole lambda p
    (X.measure 0 t) (X.measure 1 t) teacher teacher i w)^2 ∂X.measure i t

@[simp] theorem PotentialCharacteristicFlow.transport_initial
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial) :
    X.transport 0 = productAntipodalTransportSq pole (initial 0) (initial 1) := by
  simp only [PotentialCharacteristicFlow.transport,X.initial_law]

/-- A helper restriction after caps have been PROVED. Its hypothesis is discharged
in source_global_estimates, and is not the hypothesis of a confinement theorem. -/
noncomputable def PotentialCharacteristicFlow.restrictCaps
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    (r T : Real) (hT : 0 ≤ T)
    (hcaps : ∀ i t, 0 ≤ t → TwoCapClass pole r (X.measure i t)) :
    SphericalCharacteristicSolution O a pole r lambda p teacher initial T where
  time_nonneg := hT
  measure := X.measure
  characteristic := X.characteristic
  map_law := by intro i t ht; rfl
  measurable_space := fun i t ht => X.measurable_space i t ht.1
  continuous_space := fun i t ht => X.continuous_space i t ht.1
  continuous_time := fun i w hw => (X.continuous_time i w hw).mono (fun _ ht => ht.1)
  initial_map := X.initial_map
  cap := fun i t ht => hcaps i t ht.1
  ode := by
    intro i w hw t ht
    have hd := X.ode i w hw t ht.1
    change HasDerivAt (fun s => (X.characteristic i s w).val)
      (-X.field t ht.1 i (X.characteristic i t w)) t at hd
    rw [X.field_eq_source_on_caps t ht.1 r (fun j => hcaps j t ht.1.le)
      i _ (X.characteristic_mem_support i t ht.1.le w hw)] at hd
    exact hd

/-- Conclusions about actual laws, not an input certificate. No derivative is
claimed at time zero; all nonnegative times enter the decay and monotonicity. -/
structure PotentialGlobalEstimates
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial) : Prop where
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

/-- Reuse interval calculus with the independently proved branch. Finite
uniqueness is absent. The time horizon t+1 puts an arbitrary positive t in
the INTERIOR whenever an ordinary derivative is needed. -/
theorem PotentialCharacteristicFlow.global_estimates_of_caps
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (r : Real) (hcaps : ∀ i t, 0 ≤ t → TwoCapClass pole r (X.measure i t))
    (hb : ∀ t : Real, 0 ≤ t → X.measure 1 t = reflectedMeasure (X.measure 0 t))
    (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (hsmall0 : sourceRadialConstant d O a teacher*
      (productAntipodalTransportSq pole (initial 0) (initial 1))^((4-p)/2) ≤ lambda/2) :
    PotentialGlobalEstimates X := by
  let Y := fun (U : Real) (hU : 0 ≤ U) => X.restrictCaps r U hU hcaps
  have hbranch (U : Real) (hU : 0 ≤ U) : ∀ t ∈ Icc (0 : Real) U,
      (Y U hU).measure 1 t = reflectedMeasure ((Y U hU).measure 0 t) :=
    fun t ht => hb t ht.1
  have hanti : AntitoneOn X.transport (Ici (0 : Real)) := by
    intro s hs t ht hst
    exact ((Y t ht).transport_persists_of_branch hO (hbranch t ht) hl hp hp4 hsmall0).1
      ⟨hs,hst⟩ ⟨ht,le_rfl⟩ hst
  have hdec : ∀ t : Real, 0 ≤ t →
      0 ≤ X.transport t ∧
      X.transport t ≤ powerDecayProfile lambda ((p-2)/2) (X.transport 0) t ∧
      powerDecayProfile lambda ((p-2)/2) (X.transport 0) t ≤ X.transport 0 := by
    intro t ht
    have hh := ((Y t ht).transport_decay_of_branch hO (hbranch t ht) hl hp hp4 hsmall0).2.2
      t ⟨ht,le_rfl⟩
    have he : (Y t ht).transport t = X.transport t := rfl
    simpa only [he, X.transport_initial] using hh
  refine ⟨hanti,?_,hdec,?_,?_,?_,?_,?_⟩
  · intro s hs t ht hst
    exact (Y t ht).objective_antitoneOn hp ⟨hs,hst⟩ ⟨ht,le_rfl⟩ hst
  · intro i t ht
    exact (Y t ht).gradientEnergy_integrable i t ⟨ht,le_rfl⟩
  · intro t ht
    exact (Y (t+1) (by linarith)).objective_hasDerivAt hp t ⟨ht,by linarith⟩
  · intro t ht
    exact (Y (t+1) (by linarith)).transport_differential_of_branch
      hO (hbranch (t+1) (by linarith)) hl hp hp4 hsmall0 t ⟨ht,by linarith⟩
  · intro t ht
    exact ((Y (t+1) (by linarith)).energy_differential_of_branch
      hO (hbranch (t+1) (by linarith)) hl hp hp4 hsmall0 t ⟨ht,by linarith⟩).2
  · intro s t hs hst hz i
    have ht : 0 ≤ t := hs.trans hst
    have hzero : X.transport t = 0 := le_antisymm (by simpa only [hz] using hanti hs ht hst)
      (hdec t ht).1
    exact (Y t ht).zero_transport_laws t ⟨ht,le_rfl⟩ hzero i

/-- The global data, uniqueness and INITIAL source conditions supply all inputs.
The representation remains explicit; no claim of equivalence to every source
WGF is made. Cap membership and all estimates below are outputs. -/
theorem PotentialCharacteristicFlow.source_global_estimates
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hu : PotentialCharacteristicLawUnique O a pole lambda p teacher initial)
    (hi : initial 1 = reflectedMeasure (initial 0))
    (r : Real) (hc : ∀ i, TwoCapClass pole r (initial i))
    (hl : 0 < lambda) (hp : 2 < p) (hp3 : p < 3)
    (zstar : Real) (hzstar : 0 < zstar)
    (hrad : sourceRadialConstant d O a teacher*zstar^((4-p)/2) ≤ lambda/2)
    (hforce : (sourceFittingConstant d O a teacher/lambda)*zstar^((3-p)/2) ≤ r/2)
    (hinit : productAntipodalTransportSq pole (initial 0) (initial 1) ≤ zstar) :
    (∀ i t, 0 ≤ t → TwoCapClass pole r (X.measure i t)) ∧ PotentialGlobalEstimates X := by
  have hconf := X.source_confinement hO hu hi r hc hl hp hp3 zstar hzstar hrad hforce hinit
  have hcaps := hconf.2.2.1
  letI := X.initial_probability 0
  letI := X.initial_probability 1
  have hZ0 : 0 ≤ productAntipodalTransportSq pole (initial 0) (initial 1) :=
    add_nonneg (sphericalWassersteinSq_nonneg _ _) (sphericalWassersteinSq_nonneg _ _)
  have hm := source_basin_initial_margins O a teacher lambda p r zstar
    (productAntipodalTransportSq pole (initial 0) (initial 1)) hl hp3 hZ0 hinit hrad hforce
  exact ⟨hcaps,X.global_estimates_of_caps hO r hcaps
    (X.antibranch_of_global_unique hO hu hi) hl hp (by linarith) hm.1⟩

end PaperFormalization.MatrixFactorization
