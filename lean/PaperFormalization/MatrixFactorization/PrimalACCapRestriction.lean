import PaperFormalization.MatrixFactorization.PrimalACCanonicalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # MF26: from the original primal AC trajectory to its classical cap restriction

Verification status and conditional scope: see `MF26_VALIDATION.md`. The canonical supported ODE is proved by time FTC AFTER
lifting the integral equation to all supported labels. The constructor below
keeps the original maps and pushed laws definitionally unchanged. It does not
assume local uniqueness, all-time cap confinement, a dual representation, or a
new continuity/ODE certificate. The manuscript-to-AC and global-symmetry
obligations remain separate from this analytic bridge.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)}

/-- Every supported label solves the canonical classical ODE at every interior
time. Only endpoint/integral equalities, not pointwise values of X.gradient,
are upgraded from AE statements. -/
theorem PrimalACCharacteristicData.canonical_ode_on_prefix
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r T : Real) (hT : 0 ≤ T)
    (hc : ∀ i t, t ∈ Icc (0 : Real) T → TwoCapClass pole r (X.measure i t))
    (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (initial i).support)
    (t : Real) (ht : t ∈ Ioo (0 : Real) T) :
    HasDerivAt (fun u => (X.characteristic i u w).val)
      (-X.canonicalPullback i t w) t := by
  have hcont := X.canonicalPullback_continuousOn_time hl hp r T hT hc i w hw
  have hcont' := hcont.mono (show Ioo (0 : Real) T ⊆ Icc (0 : Real) T from Ioo_subset_Icc_self)
  have hm := hcont'.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioo t ht
  have hct := hcont.continuousAt (Icc_mem_nhds ht.1 ht.2)
  have hint := X.canonicalPullback_intervalIntegrable hl hp r T hT hc i w hw
    0 t ⟨le_rfl,hT⟩ ⟨ht.1.le,ht.2.le⟩
  have hder := intervalIntegral.integral_hasDerivAt_right hint hm hct
  have hd : HasDerivAt
      (fun u => (X.characteristic i 0 w).val - ∫ v in 0..u, X.canonicalPullback i v w)
      (-X.canonicalPullback i t w) t := by
    exact hder.const_sub (X.characteristic i 0 w).val
  apply hd.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with u hu
  have he := (X.canonical_integral_equation_supported hl hp r T hT hc i
    0 u ⟨le_rfl,hT⟩ hu w hw).2
  calc
    (X.characteristic i u w).val =
        -(∫ v in 0..u, X.canonicalPullback i v w) + (X.characteristic i 0 w).val :=
      sub_eq_iff_eq_add.mp he
    _ = (X.characteristic i 0 w).val - ∫ v in 0..u, X.canonicalPullback i v w := by abel

/-- A proved cap prefix yields the EXISTING record, with no changed state or
characteristic maps and no extra regularity supplied by the caller. -/
noncomputable def PrimalACCharacteristicData.toSphericalCapInterval
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r T : Real) (hT : 0 ≤ T)
    (hc : ∀ i t, t ∈ Icc (0 : Real) T → TwoCapClass pole r (X.measure i t)) :
    SphericalCharacteristicSolution O a pole r lambda p teacher initial T where
  time_nonneg := hT
  measure := X.measure
  characteristic := X.characteristic
  map_law := by intro i t ht; rfl
  measurable_space := fun i t _ => X.measurable_space i t
  continuous_space := fun i t ht => X.continuous_space i t ht.1
  continuous_time := fun i w hw =>
    (X.supported_time_continuity hl hp i w hw).mono (fun t ht => ht.1)
  initial_map := X.initial_map
  cap := hc
  ode := X.canonical_ode_on_prefix hl hp r T hT hc

@[simp] theorem PrimalACCharacteristicData.toSphericalCapInterval_measure
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r T : Real) (hT : 0 ≤ T)
    (hc : ∀ i t, t ∈ Icc (0 : Real) T → TwoCapClass pole r (X.measure i t)) :
    (X.toSphericalCapInterval hl hp r T hT hc).measure = X.measure := rfl

@[simp] theorem PrimalACCharacteristicData.toSphericalCapInterval_characteristic
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r T : Real) (hT : 0 ≤ T)
    (hc : ∀ i t, t ∈ Icc (0 : Real) T → TwoCapClass pole r (X.measure i t)) :
    (X.toSphericalCapInterval hl hp r T hT hc).characteristic = X.characteristic := rfl

/-- A supported good prefix suffices: current closed supports and exact half
masses are derived by MF25/MF18 before invoking the preceding constructor. -/
noncomputable def PrimalACCharacteristicData.classicalRestrictionOfGoodPrefix
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r T : Real) (hT : 0 ≤ T) (hc : ∀ i, TwoCapClass pole r (initial i))
    (hin : ∀ i w, w ∈ (initial i).support → ∀ t ∈ Icc (0 : Real) T,
      X.characteristic i t w ∈ sphericalCap pole r ∪ sphericalCap (reflect pole) r) :
    SphericalCharacteristicSolution O a pole r lambda p teacher initial T :=
  X.toSphericalCapInterval hl hp r T hT (X.cap_on_prefix hl hp r T hT hc hin)

/-- The first positive restriction needs only the ORIGINAL initial cap laws. -/
noncomputable def PrimalACCharacteristicData.initialSphericalCapInterval
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r : Real) (hc : ∀ i, TwoCapClass pole r (initial i)) :
    SphericalCharacteristicSolution O a pole r lambda p teacher initial
      (primalInitialCapTime d O a pole r lambda p initial) :=
  X.toSphericalCapInterval hl hp r _ (X.first_cap_laws hl hp r hc).1.le
    (X.first_cap_laws hl hp r hc).2

@[simp] theorem PrimalACCharacteristicData.initialSphericalCapInterval_measure
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r : Real) (hc : ∀ i, TwoCapClass pole r (initial i)) :
    (X.initialSphericalCapInterval hl hp r hc).measure = X.measure := rfl

@[simp] theorem PrimalACCharacteristicData.initialSphericalCapInterval_characteristic
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r : Real) (hc : ∀ i, TwoCapClass pole r (initial i)) :
    (X.initialSphericalCapInterval hl hp r hc).characteristic = X.characteristic := rfl

/-- End-to-end initial-prefix bridge for the unchanged primal AC class.
The original maps solve the canonical supported ODE because they are the
maps of the constructed existing record. All actual signed integrals are
retained as conclusions. This does NOT establish the manuscript-to-AC
representation or any global uniqueness/confinement theorem. -/
theorem primal_ac_classical_first_cap
    (X : PrimalACCharacteristicData O a pole lambda p teacher initial)
    [IsProbabilityMeasure teacher] (hl : 0 ≤ lambda) (hp : 2 < p)
    (r : Real) (hc : ∀ i, TwoCapClass pole r (initial i)) :
    let tau := primalInitialCapTime d O a pole r lambda p initial
    0 < tau ∧
    ∃ Y : SphericalCharacteristicSolution O a pole r lambda p teacher initial tau,
      Y.measure = X.measure ∧ Y.characteristic = X.characteristic ∧
      ∀ i s t, s ∈ Icc (0 : Real) tau → t ∈ Icc (0 : Real) tau →
        ∀ w ∈ (initial i).support,
          IntervalIntegrable (fun u => X.canonicalPullback i u w) volume s t ∧
          (X.characteristic i t w).val - (X.characteristic i s w).val =
            -(∫ u in s..t, X.canonicalPullback i u w) := by
  have hfirst := X.first_cap_laws hl hp r hc
  refine ⟨hfirst.1,X.initialSphericalCapInterval hl hp r hc,rfl,rfl,?_⟩
  intro i s t hs ht w hw
  exact X.canonical_integral_equation_supported hl hp r _ hfirst.1.le hfirst.2 i s t hs ht w hw

end PaperFormalization.MatrixFactorization
