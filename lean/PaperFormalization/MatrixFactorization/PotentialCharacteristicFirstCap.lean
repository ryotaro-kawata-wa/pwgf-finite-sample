import PaperFormalization.MatrixFactorization.PotentialCharacteristicRegularity
import PaperFormalization.MatrixFactorization.ExactSupportRadius
import PaperFormalization.MatrixFactorization.ContinuousCapAssignment

/-! # MF23: a noncircular first common cap interval for represented flows

Execution records: `MF23_VALIDATION.md`.

The initial strict radius is the original compact support
maximum. The cap-free speed estimate gives one positive time for ALL supported
labels. Exact current half masses and the complete closed-support condition
are subsequently derived from MF18, and the true local field is identified
through dual contact. No first cap interval or local uniqueness is a premise.
The classical optimal-dual representation remains explicit in the flow type.
-/
open MeasureTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def potentialInitialCapTime (d : Nat) {h : Nat} (O : Finset Nat)
    (a : Nat -> Weight h) (pole : UnitSphere d) (r lambda p : Real)
    (initial : Fin 2 -> Measure (UnitSphere d)) : Real :=
  (r-productSphericalSupportRadius pole initial) /
    (Real.pi*(potentialSpeedBound d O a lambda p+1))

theorem potentialInitialCapTime_pos {d h : Nat} (O : Finset Nat)
    (a : Nat -> Weight h) (pole : UnitSphere d) (r lambda p : Real)
    (initial : Fin 2 -> Measure (UnitSphere d))
    (hc : forall i, TwoCapClass pole r (initial i)) :
    0 < potentialInitialCapTime d O a pole r lambda p initial := by
  have hR := productSphericalSupportRadius_cap_properties pole r initial hc
  have hM := potentialSpeedBound_nonneg d O a lambda p
  exact div_pos (sub_pos.mpr hR.2.1) (mul_pos Real.pi_pos (by linarith))

variable {d h : Nat} {O : Finset Nat} {a : Nat -> Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 -> Measure (UnitSphere d)}

/-- The current full cap class follows from a supported good prefix.
This restriction lemma is conditional; the next lemma supplies its first prefix. -/
theorem PotentialCharacteristicFlow.cap_on_prefix
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    (r T : Real) (hT : 0 <= T) (hc : forall i, TwoCapClass pole r (initial i))
    (hin : forall i w, w ∈ (initial i).support -> ∀ t ∈ Icc (0 : Real) T,
      X.characteristic i t w ∈ sphericalCap pole r ∪ sphericalCap (reflect pole) r)
    (i : Fin 2) (t : Real) (ht : t ∈ Icc (0 : Real) T) :
    TwoCapClass pole r (X.measure i t) := by
  exact (hc i).map_of_continuous_paths (X.characteristic i) T hT
    (X.initial_map i)
    (fun w hw => (X.continuous_time i w hw).mono (fun _ hs => hs.1))
    (hin i) t ht (X.measurable_space i t ht.1) (X.continuous_space i t ht.1)

/-- An explicit common initial cap interval, derived without knowing the
current law is a cap law. Zero speed is harmless because the denominator uses M+1. -/
theorem PotentialCharacteristicFlow.first_cap_interval
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hp : 2 < p)
    (r : Real) (hc : forall i, TwoCapClass pole r (initial i)) :
    let tau := potentialInitialCapTime d O a pole r lambda p initial
    0 < tau ∧
    (forall i w, w ∈ (initial i).support -> ∀ t ∈ Icc (0 : Real) tau,
      X.characteristic i t w ∈ sphericalCap pole r ∪ sphericalCap (reflect pole) r) := by
  let R := productSphericalSupportRadius pole initial
  let M := potentialSpeedBound d O a lambda p
  have hR := productSphericalSupportRadius_cap_properties pole r initial hc
  have hM : 0 <= M := potentialSpeedBound_nonneg d O a lambda p
  refine ⟨(potentialInitialCapTime_pos O a pole r lambda p initial hc), ?_⟩
  intro i w hw t ht
  have ht' : t <= (r-R)/(Real.pi*(M+1)) := ht.2
  have htime : t*(Real.pi*(M+1)) <= r-R :=
    (le_div_iff₀ (mul_pos Real.pi_pos (by linarith))).mp ht'
  have hdisp := X.angular_displacement_le hp i w hw t ht.1
  have htri := assignedPole_distance_triangle pole (X.characteristic i t w) w
  have hlabel := hR.2.2.1 i w hw
  have hpt : 0 <= Real.pi*t := mul_nonneg Real.pi_pos.le ht.1
  have hrnow : sphericalDistance (X.characteristic i t w)
      (assignedPole pole (X.characteristic i t w)) < r := by
    change sphericalDistance w (assignedPole pole w) <= R at hlabel
    change sphericalDistance (X.characteristic i t w) w <= (Real.pi/2)*M*t at hdisp
    have hRr : R < r := hR.2.1
    nlinarith
  rcases assignedPole_mem pole (X.characteristic i t w) with hplus | hminus
  . exact Or.inl (by simpa only [sphericalCap, mem_setOf_eq, hplus] using hrnow)
  . exact Or.inr (by simpa only [sphericalCap, mem_setOf_eq, hminus] using hrnow)

/-- Restriction preserves literal laws and maps and proves the local ODE field
identity from actual dual optimality. Finite-interval uniqueness is NOT asserted. -/
noncomputable def PotentialCharacteristicFlow.toCapInterval
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    (r T : Real) (hT : 0 <= T) (hc : forall i, TwoCapClass pole r (initial i))
    (hin : forall i w, w ∈ (initial i).support -> ∀ t ∈ Icc (0 : Real) T,
      X.characteristic i t w ∈ sphericalCap pole r ∪ sphericalCap (reflect pole) r) :
    SphericalCharacteristicSolution O a pole r lambda p teacher initial T where
  time_nonneg := hT
  measure := X.measure
  characteristic := X.characteristic
  map_law := by intro i t ht; rfl
  measurable_space := fun i t ht => X.measurable_space i t ht.1
  continuous_space := fun i t ht => X.continuous_space i t ht.1
  continuous_time := fun i w hw =>
    (X.continuous_time i w hw).mono (fun _ ht => ht.1)
  initial_map := X.initial_map
  cap := X.cap_on_prefix r T hT hc hin
  ode := by
    intro i w hw t ht
    have hd := X.ode i w hw t ht.1
    change HasDerivAt (fun s => (X.characteristic i s w).val)
      (-X.field t ht.1 i (X.characteristic i t w)) t at hd
    rw [X.field_eq_source_on_caps t ht.1 r
      (fun j => X.cap_on_prefix r T hT hc hin j t ⟨ht.1.le, ht.2.le⟩)
      i _ (X.characteristic_mem_support i t ht.1.le w hw)] at hd
    exact hd

/-- Concrete nonempty first restriction with exactly the source's cap law,
without a supplied current cap certificate, speed estimate, or field identity. -/
noncomputable def PotentialCharacteristicFlow.initialCapRestriction
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hp : 2 < p)
    (r : Real) (hc : forall i, TwoCapClass pole r (initial i)) :
    SphericalCharacteristicSolution O a pole r lambda p teacher initial
      (potentialInitialCapTime d O a pole r lambda p initial) :=
  X.toCapInterval r _ (X.first_cap_interval hp r hc).1.le hc
    (X.first_cap_interval hp r hc).2

@[simp] theorem PotentialCharacteristicFlow.initialCapRestriction_measure
    (X : PotentialCharacteristicFlow O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hp : 2 < p)
    (r : Real) (hc : forall i, TwoCapClass pole r (initial i)) (i : Fin 2) (t : Real) :
    (X.initialCapRestriction hp r hc).measure i t = X.measure i t := rfl

end PaperFormalization.MatrixFactorization
