import PaperFormalization.MatrixFactorization.CharacteristicPointwiseRadial

/-! # Uniform angular radius bounds on the original and pushed supports

The original closed support is compact and lies in strict open caps. This
provides a common strict radius before a trajectory is considered. A bound
on the original support then passes to the closed support of any measurable
pushforward, without requiring global continuity of the transport map.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Compactness turns original strict cap membership into a uniform strict
radius bound. This existential bound is not designated as an exact supremum. -/
theorem TwoCapClass.exists_support_radius_lt {d : Nat} {pole : UnitSphere d}
    {radius : Real} {mu : Measure (UnitSphere d)} (hcap : TwoCapClass pole radius mu) :
    ∃ R0 : Real, 0 ≤ R0 ∧ R0 < radius ∧
      ∀ w ∈ mu.support, sphericalPoleRadius pole w ≤ R0 := by
  letI : IsProbabilityMeasure mu := hcap.probability
  have hc : IsCompact mu.support := (Measure.isClosed_support (μ := mu)).isCompact
  have hn : mu.support.Nonempty := Measure.nonempty_support (IsProbabilityMeasure.ne_zero mu)
  obtain ⟨w, hw, hmax⟩ := hc.exists_isMaxOn hn (sphericalPoleRadius_continuous pole).continuousOn
  refine ⟨sphericalPoleRadius pole w, sphericalPoleRadius_nonneg pole w, ?_, ?_⟩
  · exact assignedPole_distance_lt_cap pole radius hcap.radius_lt (hcap.support_subset hw)
  · intro y hy
    exact hmax hy

/-- Both original marginals admit one nonnegative bound strictly inside the
source cap radius. Each original probability/support condition is retained. -/
theorem twoCap_common_support_radius_lt {d : Nat} (pole : UnitSphere d) (radius : Real)
    (mu : Fin 2 → Measure (UnitSphere d)) (hcap : ∀ i, TwoCapClass pole radius (mu i)) :
    ∃ R0 : Real, 0 ≤ R0 ∧ R0 < radius ∧
      ∀ (i : Fin 2) w, w ∈ (mu i).support → sphericalPoleRadius pole w ≤ R0 := by
  obtain ⟨R0, hR0, hR0r, hb0⟩ := (hcap 0).exists_support_radius_lt
  obtain ⟨R1, hR1, hR1r, hb1⟩ := (hcap 1).exists_support_radius_lt
  refine ⟨max R0 R1, hR0.trans (le_max_left _ _), max_lt hR0r hR1r, ?_⟩
  intro i w hw
  fin_cases i
  · exact (hb0 w hw).trans (le_max_left _ _)
  · exact (hb1 w hw).trans (le_max_right _ _)

/-- An original-support radius bound passes to the entire closed support of
a measurable pushforward. Continuity of the map is not an input. -/
theorem sphericalPoleRadius_support_map_le {d : Nat} (pole : UnitSphere d)
    (mu : Measure (UnitSphere d)) (f : UnitSphere d → UnitSphere d)
    (hf : Measurable f) (R : Real)
    (hb : ∀ w ∈ mu.support, sphericalPoleRadius pole (f w) ≤ R) :
    (mu.map f).support ⊆ {w | sphericalPoleRadius pole w ≤ R} := by
  have hc : IsClosed {w : UnitSphere d | sphericalPoleRadius pole w ≤ R} :=
    isClosed_le (sphericalPoleRadius_continuous pole) continuous_const
  apply Measure.support_subset_of_isClosed hc
  apply (ae_map_iff hf.aemeasurable hc.measurableSet).2
  filter_upwards [Measure.support_mem_ae (μ := mu)] with w hw
  exact hb w hw

variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}

/-- The original initial laws have a shared strict support radius, derived
from the existing exact initial law and closed-support cap conditions. -/
theorem SphericalCharacteristicSolution.initial_support_radius_lt
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T) :
    ∃ R0 : Real, 0 ≤ R0 ∧ R0 < radius ∧
      ∀ (i : Fin 2) w, w ∈ (initial i).support → sphericalPoleRadius pole w ≤ R0 := by
  apply twoCap_common_support_radius_lt pole radius initial
  intro i
  rw [← X.initial_law i]
  exact X.cap i 0 ⟨le_rfl, X.time_nonneg⟩

/-- A proved particle bound controls every point of the actual current closed
support; no unsupported particle or globally continuous extension is used. -/
theorem SphericalCharacteristicSolution.support_radius_le
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    (i : Fin 2) (t : Real) (ht : t ∈ Icc 0 T) (R : Real)
    (hb : ∀ w ∈ (initial i).support, sphericalPoleRadius pole (X.characteristic i t w) ≤ R) :
    (X.measure i t).support ⊆ {w | sphericalPoleRadius pole w ≤ R} := by
  rw [X.map_law i t ht]
  exact sphericalPoleRadius_support_map_le pole (initial i) (X.characteristic i t)
    (X.measurable_space i t ht) R hb

end PaperFormalization.MatrixFactorization
