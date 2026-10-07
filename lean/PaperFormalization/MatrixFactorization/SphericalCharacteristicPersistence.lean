import PaperFormalization.MatrixFactorization.SphericalCharacteristicContinuity
import PaperFormalization.MatrixFactorization.CoarseRadialOuterMargin
import PaperFormalization.MatrixFactorization.ScalarPowerDecay

/-! # MF15: actual mean-distance persistence and decay on a given cap interval

The literal MF14 transport derivative is reused, and
branch membership is derived from the existing source uniqueness premise.
Only the initial coarse squared-distance bound is supplied. Current-time
smallness is proved, not assumed for all times. The cap interval remains the
existing interval hypothesis: this file does not assert support confinement
or identify the coarse basin with the printed sharp basin.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}

/-- Abbreviation of the actual all-coupling product squared angular distance. -/
noncomputable def SphericalCharacteristicSolution.transport
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (t : Real) : Real := productAntipodalTransportSq pole (X.measure 0 t) (X.measure 1 t)

@[simp] theorem SphericalCharacteristicSolution.transport_initial
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T) :
    X.transport 0 = productAntipodalTransportSq pole (initial 0) (initial 1) := by
  simp only [SphericalCharacteristicSolution.transport,X.initial_law]

/-- The larger outer region gives the nonincrease needed to rule out first exit. -/
theorem SphericalCharacteristicSolution.transport_outer_nonpos
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (t : Real) (ht : t ∈ Ioo 0 T)
    (hsmall : X.transport t ≤ radialOuterRadius lambda p (fittingCurvatureConstant d O a/64)) :
    deriv X.transport t ≤ 0 := by
  have htc : t ∈ Icc (0 : Real) T := ⟨ht.1.le,ht.2.le⟩
  have hb := spherical_characteristic_antibranch_invariant hO X hunique hinitial t htc
  have hsmall' : productAntipodalTransportSq pole (X.measure 0 t)
      (reflectedMeasure (X.measure 0 t)) ≤ radialOuterRadius lambda p (fittingCurvatureConstant d O a/64) := by
    simpa only [SphericalCharacteristicSolution.transport,hb] using hsmall
  have hn := antisymmetric_radial_pairing_outer_nonneg O a hO pole radius lambda p
    hl hp hp4 (X.measure 0 t) (X.cap 0 t htc) teacher hsmall'
  change deriv (fun s => productAntipodalTransportSq pole (X.measure 0 s) (X.measure 1 s)) t ≤ 0
  rw [(X.productTransport_hasDerivAt hp t ht).deriv]
  simp only [Fin.sum_univ_two,hb]
  change -2*antisymmetricRadialObjectivePairing O a pole lambda p (X.measure 0 t) teacher ≤ 0
  linarith

/-- The initial CLOSED coarse radius persists, and the actual transport is
nonincreasing on the entire original closed cap interval. -/
theorem SphericalCharacteristicSolution.transport_persists
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (hsmall0 : productAntipodalTransportSq pole (initial 0) (initial 1) ≤
      coarseRadialRadius lambda p (fittingCurvatureConstant d O a/64)) :
    AntitoneOn X.transport (Icc 0 T) ∧
    ∀ t ∈ Icc 0 T, 0 ≤ X.transport t ∧
      X.transport t ≤ productAntipodalTransportSq pole (initial 0) (initial 1) ∧
      X.transport t ≤ coarseRadialRadius lambda p (fittingCurvatureConstant d O a/64) := by
  have hC : 0 ≤ fittingCurvatureConstant d O a/64 :=
    div_nonneg (fittingCurvatureConstant_nonneg d O a) (by norm_num)
  have hi : X.transport 0 < radialOuterRadius lambda p (fittingCurvatureConstant d O a/64) := by
    rw [X.transport_initial]
    exact hsmall0.trans_lt (coarseRadialRadius_lt_outer lambda p _ hl hC hp4)
  have hbar := scalar_cap_barrier (f := X.transport) X.time_nonneg X.productTransport_continuousOn
    (fun t ht => (X.productTransport_hasDerivAt hp t ht).differentiableAt) hi
    (fun t ht hs => X.transport_outer_nonpos hO hunique hinitial hl hp hp4 t ht hs.le)
  refine ⟨hbar.2,?_⟩
  intro t ht
  have hle := hbar.2 ⟨le_rfl,X.time_nonneg⟩ ht ht.1
  rw [X.transport_initial] at hle
  exact ⟨X.productTransport_nonneg t ht,hle,hle.trans hsmall0⟩

/-- Exact printed decay PROFILE for the actual trajectory, from initial data
alone on the stated cap interval. The sufficient initial RADIUS remains coarse. -/
theorem SphericalCharacteristicSolution.transport_decay
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (hsmall0 : productAntipodalTransportSq pole (initial 0) (initial 1) ≤
      coarseRadialRadius lambda p (fittingCurvatureConstant d O a/64)) :
    AntitoneOn X.transport (Icc 0 T) ∧
    (∀ t ∈ Ioo 0 T, deriv X.transport t ≤ -lambda*(X.transport t)^(p/2)) ∧
    ∀ t ∈ Icc 0 T,
      0 ≤ X.transport t ∧
      X.transport t ≤ powerDecayProfile lambda ((p-2)/2)
        (productAntipodalTransportSq pole (initial 0) (initial 1)) t ∧
      powerDecayProfile lambda ((p-2)/2)
        (productAntipodalTransportSq pole (initial 0) (initial 1)) t ≤
          productAntipodalTransportSq pole (initial 0) (initial 1) := by
  have hs := X.transport_persists hO hunique hinitial hl hp hp4 hsmall0
  have hineq : ∀ t ∈ Ioo (0 : Real) T,
      deriv X.transport t ≤ -lambda*(X.transport t)^(p/2) := by
    intro t ht
    exact X.radial_transport_deriv_le hO hunique hinitial hl hp hp4 t ht
      (hs.2 t ⟨ht.1.le,ht.2.le⟩).2.2
  have ha : 0 < (p-2)/2 := by linarith
  have hdec := scalar_power_decay (f := X.transport) X.time_nonneg hl.le ha X.productTransport_continuousOn
    (fun t ht => (X.productTransport_hasDerivAt hp t ht).differentiableAt)
    X.productTransport_nonneg (by
      have he : (p-2)/2+1 = p/2 := by ring
      simpa only [he] using hineq)
  refine ⟨hs.1,hineq,?_⟩
  intro t ht
  have h0 := X.productTransport_nonneg 0 ⟨le_rfl,X.time_nonneg⟩
  change 0 ≤ X.transport 0 at h0
  rw [X.transport_initial] at h0
  refine ⟨(hs.2 t ht).1,?_,powerDecayProfile_le_initial hl.le ha h0 ht.1⟩
  simpa only [X.transport_initial] using hdec.2 t ht

/-- Zero hitting stays zero on the remaining part of the same cap interval. -/
theorem SphericalCharacteristicSolution.transport_zero_persists
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (hsmall0 : productAntipodalTransportSq pole (initial 0) (initial 1) ≤
      coarseRadialRadius lambda p (fittingCurvatureConstant d O a/64))
    (s t : Real) (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T)
    (hst : s ≤ t) (hz : X.transport s = 0) : X.transport t = 0 :=
  scalar_zero_persists X.productTransport_nonneg
    (X.transport_persists hO hunique hinitial hl hp hp4 hsmall0).1 hs ht hst hz

end PaperFormalization.MatrixFactorization
