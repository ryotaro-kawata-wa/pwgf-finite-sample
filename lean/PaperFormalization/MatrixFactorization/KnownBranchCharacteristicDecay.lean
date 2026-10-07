import PaperFormalization.MatrixFactorization.KnownBranchCharacteristicBounds
import PaperFormalization.MatrixFactorization.SourceCharacteristicPersistence

/-! # MF23: initial-only estimates without a finite uniqueness premise

Execution records: `MF23_VALIDATION.md`.

These adapters reuse the verified scalar barrier and
power-decay theorems. The endpoint for the global represented trajectory
supplies the branch identity by global reflection and uniqueness. No current
smallness condition is assumed. Closed initial equality, zero hitting,
nonintegral exponents and T=0 are retained.
-/
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}

theorem SphericalCharacteristicSolution.transport_persists_of_branch
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hb : ∀ t ∈ Icc (0 : Real) T, X.measure 1 t = reflectedMeasure (X.measure 0 t))
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
  have hper := scalar_source_initial_margin (f := X.transport) X.time_nonneg hl
    (sourceBranchConstants_nonneg d O a teacher).1 (by linarith : 1 < p/2) (by linarith : p/2 < 2)
    X.productTransport_continuousOn
    (fun t ht => (X.productTransport_hasDerivAt hp t ht).differentiableAt)
    X.productTransport_nonneg
    (fun t ht => X.transport_remainder_of_branch hO hb hp t ht) hinit
  refine ⟨hper.1,?_⟩
  intro t ht
  exact ⟨X.productTransport_nonneg t ht,
    by simpa only [X.transport_initial] using hper.2.1 t ht,
    by simpa only [he] using hper.2.2.1 t ht⟩

theorem SphericalCharacteristicSolution.transport_differential_of_branch
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hb : ∀ t ∈ Icc (0 : Real) T, X.measure 1 t = reflectedMeasure (X.measure 0 t))
    (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (hsmall0 : sourceRadialConstant d O a teacher*
      (productAntipodalTransportSq pole (initial 0) (initial 1))^((4-p)/2) ≤ lambda/2)
    (t : Real) (ht : t ∈ Ioo 0 T) :
    deriv X.transport t ≤ -lambda*(X.transport t)^(p/2) := by
  have hs := (X.transport_persists_of_branch hO hb hl hp hp4 hsmall0).2 t ⟨ht.1.le,ht.2.le⟩
  have he : 2-p/2 = (4-p)/2 := by ring
  have hm : sourceRadialConstant d O a teacher*(X.transport t)^(2-p/2) ≤ lambda/2 := by
    simpa only [he] using hs.2.2
  have ha := source_power_error_absorbed hs.1 (by linarith : 0 < p/2)
    (by linarith : p/2 < 2) hm
  have hi := X.transport_remainder_of_branch hO hb hp t ht
  nlinarith

/-- Exact decay on the same finite restriction; no family of unrelated solutions. -/
theorem SphericalCharacteristicSolution.transport_decay_of_branch
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hb : ∀ t ∈ Icc (0 : Real) T, X.measure 1 t = reflectedMeasure (X.measure 0 t))
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
  have hs := X.transport_persists_of_branch hO hb hl hp hp4 hsmall0
  have hi := X.transport_differential_of_branch hO hb hl hp hp4 hsmall0
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

/-- The actual energy chain rule is reused, not replaced by a supplied inequality. -/
theorem SphericalCharacteristicSolution.energy_differential_of_branch
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hb : ∀ t ∈ Icc (0 : Real) T, X.measure 1 t = reflectedMeasure (X.measure 0 t))
    (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (hsmall0 : sourceRadialConstant d O a teacher*
      (productAntipodalTransportSq pole (initial 0) (initial 1))^((4-p)/2) ≤ lambda/2)
    (t : Real) (ht : t ∈ Ioo 0 T) :
    HasDerivAt X.objective (-X.gradientEnergy t) t ∧
    deriv X.objective t ≤ -(lambda^2/4)*(X.transport t)^(p-1) := by
  have htc : t ∈ Icc (0 : Real) T := ⟨ht.1.le,ht.2.le⟩
  have hs := (X.transport_persists_of_branch hO hb hl hp hp4 hsmall0).2 t htc
  have hg := X.gradientEnergy_source_of_branch hO hb hl hp hp4 t htc hs.2.2
  refine ⟨X.objective_hasDerivAt hp t ht,?_⟩
  rw [(X.objective_hasDerivAt hp t ht).deriv]
  simpa only [neg_mul] using neg_le_neg hg

end PaperFormalization.MatrixFactorization
