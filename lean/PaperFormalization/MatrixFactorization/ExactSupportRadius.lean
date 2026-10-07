import PaperFormalization.MatrixFactorization.SphericalSupportRadius

/-! # The exact source supremum of the original support radii

The definitions use the actual supremum and the maximum of the two marginal
suprema. Compactness and probability supply attainment; strictness follows
from the original closed support lying in the open caps. These radii are not
replacements by arbitrary existential upper bounds.
-/
open MeasureTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The exact supremum of the angular assigned-pole radius on a marginal's closed support. -/
noncomputable def sphericalSupportRadius {d : Nat} (pole : UnitSphere d)
    (mu : Measure (UnitSphere d)) : Real :=
  sSup (sphericalPoleRadius pole '' mu.support)

/-- The source product support radius is the maximum of the two exact marginal suprema. -/
noncomputable def productSphericalSupportRadius {d : Nat} (pole : UnitSphere d)
    (mu : Fin 2 → Measure (UnitSphere d)) : Real :=
  max (sphericalSupportRadius pole (mu 0)) (sphericalSupportRadius pole (mu 1))

/-- The literal support supremum is a least upper bound for every original probability. -/
theorem sphericalSupportRadius_isLUB {d : Nat} (pole : UnitSphere d)
    (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] :
    IsLUB (sphericalPoleRadius pole '' mu.support) (sphericalSupportRadius pole mu) := by
  have hc : IsCompact (sphericalPoleRadius pole '' mu.support) :=
    (Measure.isClosed_support (μ := mu)).isCompact.image (sphericalPoleRadius_continuous pole)
  have hn : (sphericalPoleRadius pole '' mu.support).Nonempty :=
    (Measure.nonempty_support (IsProbabilityMeasure.ne_zero mu)).image _
  exact hc.isLUB_sSup hn

/-- Compactness makes the actual supremum attained at an original supported point. -/
theorem sphericalSupportRadius_attained {d : Nat} (pole : UnitSphere d)
    (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] :
    ∃ w ∈ mu.support, sphericalPoleRadius pole w = sphericalSupportRadius pole mu := by
  have hc : IsCompact (sphericalPoleRadius pole '' mu.support) :=
    (Measure.isClosed_support (μ := mu)).isCompact.image (sphericalPoleRadius_continuous pole)
  have hn : (sphericalPoleRadius pole '' mu.support).Nonempty :=
    (Measure.nonempty_support (IsProbabilityMeasure.ne_zero mu)).image _
  exact hc.sSup_mem hn

/-- The exact marginal radius is nonnegative, strictly inside the original cap,
and bounds precisely the same constants as all original support points. -/
theorem sphericalSupportRadius_cap_properties {d : Nat} (pole : UnitSphere d)
    (r : Real) (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu) :
    0 ≤ sphericalSupportRadius pole mu ∧ sphericalSupportRadius pole mu < r ∧
    (∀ w ∈ mu.support, sphericalPoleRadius pole w ≤ sphericalSupportRadius pole mu) ∧
    (∀ R : Real, sphericalSupportRadius pole mu ≤ R ↔
      ∀ w ∈ mu.support, sphericalPoleRadius pole w ≤ R) := by
  letI : IsProbabilityMeasure mu := hcap.probability
  obtain ⟨w,hw,he⟩ := sphericalSupportRadius_attained pole mu
  have hl := sphericalSupportRadius_isLUB pole mu
  refine ⟨he ▸ sphericalPoleRadius_nonneg pole w, ?_, ?_, ?_⟩
  · rw [← he]
    exact assignedPole_distance_lt_cap pole r hcap.radius_lt (hcap.support_subset hw)
  · intro y hy
    exact hl.1 (mem_image_of_mem _ hy)
  · intro R
    constructor
    · intro hb y hy
      exact (hl.1 (mem_image_of_mem _ hy)).trans hb
    · intro hb
      apply hl.2
      rintro _ ⟨y,hy,rfl⟩
      exact hb y hy

/-- The product maximum is also attained by a supported point in one actual marginal. -/
theorem productSphericalSupportRadius_attained {d : Nat} (pole : UnitSphere d)
    (r : Real) (mu : Fin 2 → Measure (UnitSphere d))
    (hcap : ∀ i, TwoCapClass pole r (mu i)) :
    ∃ (i : Fin 2) (w : UnitSphere d), w ∈ (mu i).support ∧
      sphericalPoleRadius pole w = productSphericalSupportRadius pole mu := by
  letI : IsProbabilityMeasure (mu 0) := (hcap 0).probability
  letI : IsProbabilityMeasure (mu 1) := (hcap 1).probability
  rcases le_total (sphericalSupportRadius pole (mu 0)) (sphericalSupportRadius pole (mu 1)) with h | h
  · obtain ⟨w,hw,he⟩ := sphericalSupportRadius_attained pole (mu 1)
    exact ⟨1,w,hw,by simpa only [productSphericalSupportRadius,max_eq_right h] using he⟩
  · obtain ⟨w,hw,he⟩ := sphericalSupportRadius_attained pole (mu 0)
    exact ⟨0,w,hw,by simpa only [productSphericalSupportRadius,max_eq_left h] using he⟩

/-- Both exact marginal suprema give the literal source R0, its strict initial
margin, and its least-upper-bound characterization across both supports. -/
theorem productSphericalSupportRadius_cap_properties {d : Nat} (pole : UnitSphere d)
    (r : Real) (mu : Fin 2 → Measure (UnitSphere d))
    (hcap : ∀ i, TwoCapClass pole r (mu i)) :
    0 ≤ productSphericalSupportRadius pole mu ∧ productSphericalSupportRadius pole mu < r ∧
    (∀ (i : Fin 2) w, w ∈ (mu i).support →
      sphericalPoleRadius pole w ≤ productSphericalSupportRadius pole mu) ∧
    (∀ R : Real, productSphericalSupportRadius pole mu ≤ R ↔
      ∀ (i : Fin 2) w, w ∈ (mu i).support → sphericalPoleRadius pole w ≤ R) := by
  have h0 := sphericalSupportRadius_cap_properties pole r (mu 0) (hcap 0)
  have h1 := sphericalSupportRadius_cap_properties pole r (mu 1) (hcap 1)
  have hb (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (mu i).support) :
      sphericalPoleRadius pole w ≤ productSphericalSupportRadius pole mu := by
    fin_cases i
    · exact (h0.2.2.1 w hw).trans (le_max_left _ _)
    · exact (h1.2.2.1 w hw).trans (le_max_right _ _)
  refine ⟨h0.1.trans (le_max_left _ _),max_lt h0.2.1 h1.2.1,hb,?_⟩
  intro R
  constructor
  · intro hR i w hw
    exact (hb i w hw).trans hR
  · intro hR
    exact max_le ((h0.2.2.2 R).mpr (hR 0)) ((h1.2.2.2 R).mpr (hR 1))

/-- The actual initial laws of the existing characteristic solution have the
exact source maximum radius, including its attainment and strict cap margin. -/
theorem SphericalCharacteristicSolution.initial_exact_support_radius {d h : Nat}
    {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
    {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
    {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T) :
    0 ≤ productSphericalSupportRadius pole initial ∧
    productSphericalSupportRadius pole initial < radius ∧
    (∀ (i : Fin 2) w, w ∈ (initial i).support →
      sphericalPoleRadius pole w ≤ productSphericalSupportRadius pole initial) ∧
    (∃ (i : Fin 2) (w : UnitSphere d), w ∈ (initial i).support ∧
      sphericalPoleRadius pole w = productSphericalSupportRadius pole initial) := by
  have hcap (i : Fin 2) : TwoCapClass pole radius (initial i) := by
    rw [← X.initial_law i]
    exact X.cap i 0 ⟨le_rfl,X.time_nonneg⟩
  have hb := productSphericalSupportRadius_cap_properties pole radius initial hcap
  exact ⟨hb.1,hb.2.1,hb.2.2.1,productSphericalSupportRadius_attained pole radius initial hcap⟩

end PaperFormalization.MatrixFactorization
