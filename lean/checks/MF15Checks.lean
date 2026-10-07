import PaperFormalization.MatrixFactorization.SphericalCharacteristicDecayClosure

/-! MF15 boundary diagnostics. Execution evidence is stored in verification receipts.
Scalar tests include zero initial value, signed parameters in mere identities,
zero horizon, real noninteger powers, and a closed initial basin. Source tests
retain the actual characteristic type and never construct a globally confined
solution by assuming the desired conclusion as an extra field.
-/
open MeasureTheory Set Filter
open PaperFormalization.MatrixFactorization
open scoped Topology
set_option autoImplicit false

-- 01: zero initial transport, no inverse power at zero.
example (l q t : Real) : powerDecayProfile l q 0 t = 0 := by simp
-- 02: time zero, before imposing a dynamical exponent range.
example (l q z : Real) : powerDecayProfile l q z 0 = z := by simp
-- 03: zero dissipation coefficient is a constant comparison profile.
example (q z t : Real) : powerDecayProfile 0 q z t = z := by simp [powerDecayProfile]
-- 04: the rational exponent identity is not restricted to integer p.
example (l p z t : Real) :
    powerDecayProfile l ((p-2)/2) z t =
      z/(1+(l*(p-2)/2)*z^((p-2)/2)*t)^(2/(p-2)) :=
  powerDecayProfile_source_form l p z t
-- 05: a positive noninteger exponent, nonnegative comparison value.
example (l z t : Real) (hl : 0 ≤ l) (hz : 0 ≤ z) (ht : 0 ≤ t) :
    0 ≤ powerDecayProfile l (1/4) z t := powerDecayProfile_nonneg hl (by norm_num) hz ht
-- 06: the same exponent, decay relative to initial value.
example (l z t : Real) (hl : 0 ≤ l) (hz : 0 ≤ z) (ht : 0 ≤ t) :
    powerDecayProfile l (1/4) z t ≤ z := powerDecayProfile_le_initial hl (by norm_num) hz ht
-- 07: negative powers only under strictly positive initial value.
example (l q z t : Real) (hl : 0 ≤ l) (hq : 0 < q) (hz : 0 < z) (ht : 0 ≤ t) :
    powerDecayProfile l q z t = (z^(-q)+l*q*t)^(-(1/q)) :=
  powerDecayProfile_eq_inverse_power hl hq hz ht
-- 08: the outer margin exists when the fitting bound is zero.
example (l p : Real) (hl : 0 < l) : 0 < radialOuterRadius l p 0 :=
  radialOuterRadius_pos l p 0 hl (by norm_num)
-- 09: original closed radius fits strictly inside the auxiliary radius.
example (l C : Real) (hl : 0 < l) (hC : 0 ≤ C) :
    coarseRadialRadius l (5/2) C < radialOuterRadius l (5/2) C :=
  coarseRadialRadius_lt_outer l (5/2) C hl hC (by norm_num)
-- 10: absorption includes zero transport.
example (l C : Real) (hl : 0 < l) (hC : 0 ≤ C) :
    C*(0 : Real)^2 ≤ l*(0 : Real)^(((5 : Real)/2)/2) :=
  radial_outer_error_absorbed l (5/2) C 0 hl (by norm_num) (by norm_num) hC le_rfl
    (radialOuterRadius_pos l (5/2) C hl hC).le
-- 11: an initially zero scalar solution stays zero on a zero-length interval.
example : AntitoneOn (fun _ : Real => (0 : Real)) (Icc 0 0) := by
  intro s hs t ht hst
  exact le_rfl
-- 12: the power-decay theorem itself is callable on a zero-length interval.
example : ∀ t ∈ Icc (0 : Real) 0,
    (0 : Real) ≤ powerDecayProfile 1 (1/4) 0 t := by
  have H := scalar_power_decay (f := fun _ : Real => (0 : Real))
    (T := 0) (lambda := 1) (alpha := 1/4) le_rfl (by norm_num) (by norm_num)
    continuousOn_const (fun t ht => differentiableAt_const 0)
    (fun t ht => le_rfl) (by intro t ht; norm_num)
  exact H.2
-- 13: the first-exit lemma needs no time-zero derivative.
example : (∀ t ∈ Icc (0 : Real) 1, (0 : Real) < 1) ∧
    AntitoneOn (fun _ : Real => (0 : Real)) (Icc 0 1) := by
  exact scalar_cap_barrier (f := fun _ : Real => (0 : Real)) (T := 1) (R := 1)
    (by norm_num) continuousOn_const (fun t ht => differentiableAt_const 0)
    (by norm_num) (by intro t ht hs; simp)
-- 14: zero hitting needs no inverse-power expression or no-hitting assumption.
example (f : Real → Real) (T s t : Real)
    (hn : ∀ u ∈ Icc 0 T, 0 ≤ f u) (ha : AntitoneOn f (Icc 0 T))
    (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t) (hz : f s = 0) :
    f t = 0 := scalar_zero_persists hn ha hs ht hst hz

section ActualSource
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}
variable (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
-- 15: initial probability is derived from source fields.
example (i : Fin 2) : IsProbabilityMeasure (initial i) := X.initial_probability i
-- 16: original law normalization, not a new transport surrogate.
example : X.transport 0 = productAntipodalTransportSq pole (initial 0) (initial 1) :=
  X.transport_initial
-- 17: continuity includes both endpoints.
example : ContinuousOn X.transport (Icc 0 T) := X.productTransport_continuousOn
-- 18: zero product cost implies both actual marginal laws equal the target.
example (t : Real) (ht : t ∈ Icc 0 T) (hz : X.transport t = 0) :
    ∀ i : Fin 2, X.measure i t = antipodalMeasure pole := X.zero_transport_laws t ht hz

variable [IsProbabilityMeasure teacher] (hp : 2 < p)
-- 19: speed integrability without globally continuous objective gradient.
example (i : Fin 2) (t : Real) (ht : t ∈ Icc 0 T) :
    Integrable (fun w => norm (X.velocity i t w)) (X.measure i t) :=
  X.velocity_norm_integrable hp i t ht
-- 20: actual-law mean derivative, not an EXP-ray derivative.
example (i : Fin 2) (z : Weight d) (t : Real) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => X.feature i s z) (X.featureSlope i t z) t :=
  X.feature_hasDerivAt hp i z t ht
-- 21: the energy identity itself does not require branch membership.
example (t : Real) (ht : t ∈ Ioo 0 T) :
    HasDerivAt X.objective (-X.gradientEnergy t) t := X.objective_hasDerivAt hp t ht
-- 22: true squared-gradient integrability is an output.
example (i : Fin 2) (t : Real) (ht : t ∈ Icc 0 T) :
    Integrable (fun w => norm (sphericalObjectiveGradient O a pole lambda p
      (X.measure 0 t) (X.measure 1 t) teacher teacher i w)^2) (X.measure i t) :=
  X.gradientEnergy_integrable i t ht
-- 23: closed-time objective monotonicity also needs no branch assumption.
example : AntitoneOn X.objective (Icc 0 T) := X.objective_antitoneOn hp

variable (hO : ∀ n ∈ O, Odd n)
  (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
  (hinitial : initial 1 = reflectedMeasure (initial 0)) (hl : 0 < lambda) (hp4 : p < 4)
  (hs0 : productAntipodalTransportSq pole (initial 0) (initial 1) ≤
    coarseRadialRadius lambda p (fittingCurvatureConstant d O a/64))
-- 24: positive-time smallness is derived from the closed initial bound.
example (t : Real) (ht : t ∈ Icc 0 T) :
    X.transport t ≤ coarseRadialRadius lambda p (fittingCurvatureConstant d O a/64) :=
  ((X.transport_persists hO hunique hinitial hl hp hp4 hs0).2 t ht).2.2
-- 25: quantitative actual energy decay uses initial data only.
example (t : Real) (ht : t ∈ Ioo 0 T) :
    deriv X.objective t ≤ -(lambda^2/4)*(X.transport t)^(p-1) :=
  X.objective_deriv_le_from_initial hO hunique hinitial hl hp hp4 hs0 t ht
-- 26: the complete endpoint preserves source hypotheses and original field.
example : AntitoneOn X.objective (Icc 0 T) ∧ AntitoneOn X.transport (Icc 0 T) := by
  have H := spherical_characteristic_cap_interval_dissipation X hO hunique hinitial hl hp hp4 hs0
  exact ⟨H.2.1,H.2.2.1⟩
end ActualSource
