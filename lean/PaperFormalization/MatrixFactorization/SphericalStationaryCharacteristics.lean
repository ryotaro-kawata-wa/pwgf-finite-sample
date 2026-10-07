import PaperFormalization.MatrixFactorization.SphericalCharacteristicSymmetry

/-! # The actual stationary antipodal characteristic solution

The constant particle maps solve the literal full-field equation. Given the
source uniqueness hypothesis, zero initial antipodal transport therefore keeps
the original law at the target. No existence result for nonzero-distance
initial laws or claim about teacher stationarity is made here.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def antipodalCharacteristicSolution {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (pole : UnitSphere d)
    (radius lambda p T : Real) (hr : 0 < radius) (hrpi : radius < Real.pi/2)
    (hp : 2 < p) (hT : 0 ≤ T) (teacher : Measure (UnitSphere d)) :
    SphericalCharacteristicSolution O a pole radius lambda p teacher (fun _ => antipodalMeasure pole) T where
  time_nonneg := hT
  measure := fun _ _ => antipodalMeasure pole
  characteristic := fun _ _ w => w
  map_law := by intros; exact Measure.map_id.symm
  measurable_space := by intros; exact measurable_id
  continuous_space := by intros; exact continuous_id.continuousOn
  continuous_time := by intros; exact continuous_const.continuousOn
  initial_map := by intros; rfl
  cap := by intros; exact antipodalMeasure_twoCap pole hr hrpi
  ode := by
    intro i w hw t ht
    simpa only [sphericalObjectiveGradient_antipodal O a hO pole lambda p hp,neg_zero] using
      hasDerivAt_const t w.val

/-- Actual characteristic uniqueness selects the constructed stationary target law. -/
theorem spherical_characteristic_antipodal_stationary {d h : Nat} {O : Finset Nat}
    {a : Nat → Weight h} (hO : ∀ n, n ∈ O → Odd n) {pole : UnitSphere d}
    {radius lambda p : Real} (hp : 2 < p) {teacher : Measure (UnitSphere d)} {T : Real}
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher (fun _ => antipodalMeasure pole) T)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher (fun _ => antipodalMeasure pole) T) :
    ∀ i t, t ∈ Icc (0 : Real) T → X.measure i t = antipodalMeasure pole := by
  have hc := X.cap 0 0 ⟨le_rfl,X.time_nonneg⟩
  exact hunique X (antipodalCharacteristicSolution O a hO pole radius lambda p T
    hc.radius_pos hc.radius_lt hp X.time_nonneg teacher)

/-- Zero actual initial transport identifies the original laws, then uniqueness
keeps them equal to the genuine antipodal target throughout the interval. -/
theorem spherical_characteristic_zero_transport_stationary {d h : Nat} {O : Finset Nat}
    {a : Nat → Weight h} (hO : ∀ n, n ∈ O → Odd n) {pole : UnitSphere d}
    {radius lambda p : Real} (hp : 2 < p) {teacher : Measure (UnitSphere d)}
    {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hZ : productAntipodalTransportSq pole (initial 0) (initial 1) = 0) :
    ∀ i t, t ∈ Icc (0 : Real) T → X.measure i t = antipodalMeasure pole := by
  have hc (i : Fin 2) : TwoCapClass pole radius (initial i) := by
    rw [← X.initial_law i]
    exact X.cap i 0 ⟨le_rfl,X.time_nonneg⟩
  letI : IsProbabilityMeasure (initial 0) := (hc 0).probability
  letI : IsProbabilityMeasure (initial 1) := (hc 1).probability
  have h0 := sphericalWassersteinSq_nonneg (initial 0) (antipodalMeasure pole)
  have h1 := sphericalWassersteinSq_nonneg (initial 1) (antipodalMeasure pole)
  have hsum : sphericalWassersteinSq (initial 0) (antipodalMeasure pole)+
      sphericalWassersteinSq (initial 1) (antipodalMeasure pole) = 0 := hZ
  have hi : ∀ i : Fin 2, initial i = antipodalMeasure pole := by
    intro i
    apply zeroTransport_eq_antipodal pole radius (initial i) (hc i)
    fin_cases i
    · change sphericalWassersteinSq (initial 0) (antipodalMeasure pole) = 0
      linarith
    · change sphericalWassersteinSq (initial 1) (antipodalMeasure pole) = 0
      linarith
  let Y := antipodalCharacteristicSolution O a hO pole radius lambda p T
    (hc 0).radius_pos (hc 0).radius_lt hp X.time_nonneg teacher
  intro i t ht
  exact characteristic_law_unique_of_initial_eq hunique X Y (funext (fun j => (hi j).symm)) i t ht

end PaperFormalization.MatrixFactorization
