import PaperFormalization.MatrixFactorization.PotentialCharacteristicMomentLimits
import PaperFormalization.MatrixFactorization.AntipodalPotentialBoundary
import PaperFormalization.MatrixFactorization.SphericalTransportPerturbation

/-! MF23 boundary checks. Execution records: `MF23_VALIDATION.md`.
The final checks construct conclusions from the explicit represented flow,
not from a supplied finite uniqueness or all-time cap hypothesis. -/
open MeasureTheory Set Filter
open scoped Topology
open PaperFormalization.MatrixFactorization
set_option autoImplicit false

variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h}
  {pole : UnitSphere d} {lambda p : Real}
  {teacher : Measure (UnitSphere d)} {initial : Fin 2 → Measure (UnitSphere d)}

-- 01: the angular distance has the correct zero case.
example (w : UnitSphere d) : sphericalDistance w w = 0 := sphericalDistance_self w

-- 02: the speed input is global, not conditioned on a cap.
example {mu : Measure (UnitSphere d)} (G : AntipodalGradientData pole mu)
    (w : UnitSphere d) (hw : w ∈ mu.support) : norm (G.gradient w) ≤ Real.pi :=
  G.norm_le_pi hw

-- 03: the classical equatorial cusp is not silently assumed differentiable.
example (w : UnitSphere d) (hw : sphericalDistance w pole = Real.pi/2) :
    ¬ (∃ g, HasSpherePotentialGradient (antipodalPotential pole 0) w g) :=
  antipodalPotential_zero_no_gradient_at_equator pole w hw

-- 04: onCaps is an actual representation of the local assigned gradient.
example (r : Real) (mu : Measure (UnitSphere d)) (hc : TwoCapClass pole r mu)
    (w : UnitSphere d) (hw : w ∈ mu.support) :
    (AntipodalGradientData.onCaps pole r mu hc).gradient w = assignedGradient pole w := rfl

-- 05: bounded angular transport uses arbitrary probability laws.
example (mu nu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    0 ≤ productAntipodalTransportSq pole mu nu ∧
    productAntipodalTransportSq pole mu mu ≤ 2*Real.pi^2 := by
  exact ⟨(productAntipodalTransportSq_global_bounds pole mu nu).1,
    (productAntipodalTransportSq_global_bounds pole mu mu).2⟩

section Flow
variable (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
variable [IsProbabilityMeasure teacher] (hl : 0 < lambda) (hp : 2 < p)
variable (hO : ∀ n ∈ O, Odd n)
variable (hu : PotentialCharacteristicLawUnique O a pole lambda p teacher initial)
variable (hi : initial 1 = reflectedMeasure (initial 0))
variable (H : PotentialGlobalEstimates X)

-- 06: initial laws, not merely their finite moments.
example (i : Fin 2) : X.measure i 0 = initial i := X.initial_law i

-- 07: the first common time remains positive when the speed is zero.
example (r : Real) (hc : ∀ i, TwoCapClass pole r (initial i)) :
    0 < potentialInitialCapTime d O a pole r lambda p initial :=
  potentialInitialCapTime_pos O a pole r lambda p initial hc

-- 08: supported original labels stay in the current closed support.
example (i : Fin 2) (t : Real) (ht : 0 ≤ t) (w : UnitSphere d)
    (hw : w ∈ (initial i).support) :
    X.characteristic i t w ∈ (X.measure i t).support :=
  X.characteristic_mem_support i t ht w hw

-- 09: no cap premise is needed for the represented field bound.
example (i : Fin 2) (t : Real) (ht : 0 < t) (w : UnitSphere d)
    (hw : w ∈ (X.measure i t).support) :
    norm (X.field t ht i w) ≤ potentialSpeedBound d O a lambda p :=
  X.field_norm_le hp t ht i w hw

-- 10: supported global path uniqueness implies global law uniqueness only.
example (hu' : PotentialCharacteristicPathUnique O a pole lambda p teacher initial) :
    PotentialCharacteristicLawUnique O a pole lambda p teacher initial := hu'.law_unique

-- 11: the branch is obtained from a transformation of the whole global flow.
example (t : Real) (ht : 0 ≤ t) :
    X.measure 1 t = reflectedMeasure (X.measure 0 t) :=
  X.antibranch_of_global_unique hO hu hi t ht

-- 12: decay includes zero initial transport.
example : Tendsto X.transport atTop (𝓝 0) := H.transport_limit hl hp

-- 13: the distance is the square root of the sum of squared costs.
example : Tendsto (fun t => Real.sqrt (X.transport t)) atTop (𝓝 0) :=
  H.productDistance_limit hl hp

-- 14: either marginal converges to the original target.
example (i : Fin 2) :
    Tendsto (fun t => sphericalWassersteinSq (X.measure i t) (antipodalMeasure pole))
      atTop (𝓝 0) := H.marginalTransport_limit hl hp i

-- 15: ordinary derivatives are requested at positive time, not at the endpoint zero.
example : HasDerivAt X.objective (-X.gradientEnergy 1) 1 :=
  H.energy_derivative 1 (by norm_num)

-- 16: zero hitting gives the actual two laws, not a zero fitting value.
example (t : Real) (ht : 0 ≤ t) (hz : X.transport 0 = 0) (i : Fin 2) :
    X.measure i t = antipodalMeasure pole := H.zero_laws 0 t le_rfl ht hz i

-- 17: degree zero has zero moment DIFFERENCE, not zero moment.
example (mu nu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (I : Fin 0 → Fin d) : norm (rawMoment mu 0 I-rawMoment nu 0 I) ≤ 0 := by
  simpa using rawMoment_coordinate_transport_bound mu nu I

-- 18: the transport bound holds for every raw order.
example (mu nu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (n : Nat) (I : Fin n → Fin d) :
    norm (rawMoment mu n I-rawMoment nu n I) ≤
      (n : Real)*Real.sqrt (sphericalWassersteinSq mu nu) :=
  rawMoment_coordinate_transport_bound mu nu I

-- 19: the tensor test's Lipschitz property is proved, not supplied to the model.
example (n : Nat) (I : Fin n → Fin d) (w y : UnitSphere d) :
    norm (tensorPower n w.val I-tensorPower n y.val I) ≤
      (n : Real)*sphericalDistance w y := tensorCoordinate_spherical_lipschitz I w y

-- 20: even/zeroth moments converge to their actual target moment.
example (i : Fin 2) (n : Nat) :
    Tendsto (fun t => rawMoment (X.measure i t) n) atTop (𝓝 (rawMoment (antipodalMeasure pole) n)) :=
  H.rawMoment_limit hl hp i n

-- 21: an explicit nontrivial odd order has zero target.
example (i : Fin 2) : Tendsto (fun t => rawMoment (X.measure i t) 3) atTop (𝓝 0) :=
  H.odd_rawMoment_limit hl hp i 3 (by decide)

-- 22: the antisymmetric zeroth moment also has zero limit.
example : Tendsto (fun t => antisymmetricMoment (X.measure 0 t) (X.measure 1 t) 0)
    atTop (𝓝 0) := H.antisymmetricMoment_limit hl hp 0

-- 23: exact symmetric odd-moment cancellation is a global uniqueness consequence.
example (t : Real) (ht : 0 ≤ t) (n : Nat) (hn : Odd n) :
    symmetricMoment (X.measure 0 t) (X.measure 1 t) n = 0 :=
  X.symmetric_odd_moment_zero hO hu hi t ht n hn

-- 24: the zero-Lipschitz-constant case has no division.
example (c : Real) (i : Fin 2) :
    Tendsto (fun t => ∫ _w : UnitSphere d, c ∂X.measure i t) atTop (𝓝 c) := by
  have hh := H.lipschitz_test_limit hl hp (fun _w : UnitSphere d => c) continuous_const
    0 le_rfl (by intro w y; simp) i
  simpa using hh

variable (r : Real) (hc : ∀ i, TwoCapClass pole r (initial i))
variable (hp3 : p < 3) (zstar : Real) (hzstar : 0 < zstar)
variable (hrad : sourceRadialConstant d O a teacher*zstar^((4-p)/2) ≤ lambda/2)
variable (hforce : (sourceFittingConstant d O a teacher/lambda)*zstar^((3-p)/2) ≤ r/2)
variable (hinit : productAntipodalTransportSq pole (initial 0) (initial 1) ≤ zstar)

-- 25: actual current cap membership is an output of the full initial-data call.
example (i : Fin 2) (t : Real) (ht : 0 ≤ t) : TwoCapClass pole r (X.measure i t) :=
  (X.source_global_estimates hO hu hi r hc hl hp hp3 zstar hzstar hrad hforce hinit).1 i t ht

-- 26: the terminal theorem supplies limits without a supplied estimate certificate.
example :
    Tendsto X.transport atTop (𝓝 0) ∧
    (∀ i n, Odd n → Tendsto (fun t => rawMoment (X.measure i t) n) atTop (𝓝 0)) := by
  rcases represented_global_attraction X hO hu hi r hc hl hp hp3 zstar hzstar hrad hforce hinit with
    ⟨hB,hcaps,hs,hEst,hZ,hD,hM,hS,hA⟩
  exact ⟨hZ,hM⟩
end Flow

#check represented_global_attraction
#check PotentialCharacteristicFlow.source_confinement
#check PotentialCharacteristicFlow.source_global_estimates
#check antipodalPotential_zero_no_gradient_at_equator
