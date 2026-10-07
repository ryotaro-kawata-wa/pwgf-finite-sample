import PaperFormalization.MatrixFactorization.SphericalObjectiveGradient
import PaperFormalization.MatrixFactorization.SphericalCapSymmetry

/-! # Actual characteristic solutions on a fixed cap interval

A characteristic solution consists of original spherical particle maps and
their pushed laws. Its ODE uses the actual first-variation field. The ODE is
required only for initial support points and interior times. Continuous maps
carry the entire original support into the current support, which derives the
cap restriction needed by reflection covariance. No existence theorem is
claimed by this representation.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- A continuous spherical map carries each support point into its pushed support. -/
theorem sphere_map_mem_support {d : Nat} (mu : Measure (UnitSphere d))
    (f : UnitSphere d → UnitSphere d) (hf : Continuous f)
    {w : UnitSphere d} (hw : w ∈ mu.support) : f w ∈ (mu.map f).support := by
  rw [Measure.support_eq_forall_isOpen] at hw ⊢
  intro U hU hopen
  rw [Measure.map_apply hf.measurable hopen.measurableSet]
  exact hw (f ⁻¹' U) hU (hopen.preimage hf)

/-- Compactness retains the exact closed support image. -/
theorem sphere_support_map_eq {d : Nat} (mu : Measure (UnitSphere d))
    (f : UnitSphere d → UnitSphere d) (hf : Continuous f) :
    (mu.map f).support = f '' mu.support := by
  apply Subset.antisymm (sphere_support_map_subset mu f hf)
  rintro _ ⟨w,hw,rfl⟩
  exact sphere_map_mem_support mu f hf hw

theorem reflectedMeasure_mem_support {d : Nat} (mu : Measure (UnitSphere d))
    (w : UnitSphere d) : w ∈ (reflectedMeasure mu).support ↔ reflect w ∈ mu.support := by
  rw [reflectedMeasure, sphere_support_map_eq mu reflect (reflect_continuous d)]
  constructor
  · rintro ⟨y,hy,rfl⟩
    simpa only [reflect_reflect] using hy
  · intro hw
    exact ⟨reflect w,hw,reflect_reflect w⟩

/-- Support-only spatial continuity suffices; no continuity is assumed at
unsupported points where the assigned-pole formula may have a tie. -/
theorem sphere_map_mem_support_of_continuousOn {d : Nat} (mu : Measure (UnitSphere d))
    (f : UnitSphere d → UnitSphere d) (hf : Measurable f) (hc : ContinuousOn f mu.support)
    {w : UnitSphere d} (hw : w ∈ mu.support) : f w ∈ (mu.map f).support := by
  rw [Measure.support_eq_forall_isOpen]
  intro U hfw hopen
  rw [Measure.map_apply hf hopen.measurableSet]
  have hpre : f ⁻¹' U ∈ 𝓝[mu.support] w := (hc w hw).preimage_mem_nhdsWithin (hopen.mem_nhds hfw)
  obtain ⟨V,hV,hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpre
  have hpos := (Measure.mem_support_iff_forall w).mp hw V hV
  apply hpos.trans_le (measure_mono_ae ?_)
  filter_upwards [Measure.support_mem_ae (μ := mu)] with y hy
  intro hyV
  exact hsub ⟨hyV,hy⟩

/-- A source characteristic solution on a compact time interval. -/
structure SphericalCharacteristicSolution {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (radius lambda p : Real)
    (teacher : Measure (UnitSphere d)) (initial : Fin 2 → Measure (UnitSphere d)) (T : Real) where
  time_nonneg : 0 ≤ T
  measure : Fin 2 → Real → Measure (UnitSphere d)
  characteristic : Fin 2 → Real → UnitSphere d → UnitSphere d
  map_law : ∀ i t, t ∈ Icc (0 : Real) T → measure i t = (initial i).map (characteristic i t)
  measurable_space : ∀ i t, t ∈ Icc (0 : Real) T → Measurable (characteristic i t)
  continuous_space : ∀ i t, t ∈ Icc (0 : Real) T →
    ContinuousOn (characteristic i t) (initial i).support
  continuous_time : ∀ i w, w ∈ (initial i).support →
    ContinuousOn (fun t => characteristic i t w) (Icc (0 : Real) T)
  initial_map : ∀ i w, w ∈ (initial i).support → characteristic i 0 w = w
  cap : ∀ i t, t ∈ Icc (0 : Real) T → TwoCapClass pole radius (measure i t)
  ode : ∀ i w, w ∈ (initial i).support → ∀ t, t ∈ Ioo (0 : Real) T →
    HasDerivAt (fun s => (characteristic i s w).val)
      (-sphericalObjectiveGradient O a pole lambda p (measure 0 t) (measure 1 t)
        teacher teacher i (characteristic i t w)) t

variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}

/-- The original closed support is transported pointwise, not merely almost everywhere. -/
theorem SphericalCharacteristicSolution.characteristic_mem_support (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (i : Fin 2) (t : Real) (ht : t ∈ Icc (0 : Real) T)
    (w : UnitSphere d) (hw : w ∈ (initial i).support) :
    X.characteristic i t w ∈ (X.measure i t).support := by
  rw [X.map_law i t ht]
  exact sphere_map_mem_support_of_continuousOn (initial i) (X.characteristic i t)
    (X.measurable_space i t ht) (X.continuous_space i t ht) hw

theorem SphericalCharacteristicSolution.characteristic_mem_caps (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (i : Fin 2) (t : Real) (ht : t ∈ Icc (0 : Real) T)
    (w : UnitSphere d) (hw : w ∈ (initial i).support) :
    X.characteristic i t w ∈ sphericalCap pole radius ∪ sphericalCap (reflect pole) radius :=
  (X.cap i t ht).support_subset (X.characteristic_mem_support i t ht w hw)

/-- Initial identity only on the original support already gives the exact initial law. -/
theorem SphericalCharacteristicSolution.initial_law (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (i : Fin 2) : X.measure i 0 = initial i := by
  rw [X.map_law i 0 ⟨le_rfl,X.time_nonneg⟩]
  calc
    _ = (initial i).map id := by
      apply Measure.map_congr
      filter_upwards [Measure.support_mem_ae (μ := initial i)] with w hw
      exact X.initial_map i w hw
    _ = initial i := Measure.map_id


/-- Uniqueness of the pushed laws within this actual characteristic class.
Full uniqueness of characteristic solutions implies this property. -/
def SphericalCharacteristicLawUnique {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (radius lambda p : Real)
    (teacher : Measure (UnitSphere d)) (initial : Fin 2 → Measure (UnitSphere d)) (T : Real) : Prop :=
  ∀ X Y : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T,
    ∀ i t, t ∈ Icc (0 : Real) T → X.measure i t = Y.measure i t

/-- The source uniqueness property for actual supported characteristics;
values of a measurable representative outside the support are immaterial. -/
def SphericalCharacteristicPathUnique {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (radius lambda p : Real)
    (teacher : Measure (UnitSphere d)) (initial : Fin 2 → Measure (UnitSphere d)) (T : Real) : Prop :=
  ∀ X Y : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T,
    ∀ i t, t ∈ Icc (0 : Real) T → ∀ w, w ∈ (initial i).support →
      X.characteristic i t w = Y.characteristic i t w

/-- Uniqueness of the original characteristics supplies the weaker law
uniqueness used by the branch conclusions. -/
theorem SphericalCharacteristicPathUnique.law_unique {d h : Nat} {O : Finset Nat}
    {a : Nat → Weight h} {pole : UnitSphere d} {radius lambda p : Real}
    {teacher : Measure (UnitSphere d)} {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}
    (hunique : SphericalCharacteristicPathUnique O a pole radius lambda p teacher initial T) :
    SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T := by
  intro X Y i t ht
  rw [X.map_law i t ht,Y.map_law i t ht]
  apply Measure.map_congr
  filter_upwards [Measure.support_mem_ae (μ := initial i)] with w hw
  exact hunique X Y i t ht w hw

end PaperFormalization.MatrixFactorization
