import PaperFormalization.MatrixFactorization.CompactRadiusContinuity
import PaperFormalization.MatrixFactorization.ExactSupportRadius
import PaperFormalization.MatrixFactorization.ScalarCapContinuation
import PaperFormalization.MatrixFactorization.ContinuousCapAssignment

/-! # Exact supported maximum-radius bounds and a conditional continuation adapter

These lemmas concern general original probability supports and spherical maps.
Continuity is explicit where compact attainment or continuation needs it. No
cap-free WGF representation, regularity theorem, or existence result is assumed
to have been established by these topological statements.
-/
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Angular boundedness supplies the least-upper-bound equivalence even for
arbitrary maps with no continuity or measurability assumption. -/
theorem supportedFlowRadius_le_iff {d : Nat} (pole : UnitSphere d)
    (initial : Fin 2 → Measure (UnitSphere d)) (hprob : ∀ i, IsProbabilityMeasure (initial i))
    (Phi : Fin 2 → Real → UnitSphere d → UnitSphere d) (t R : Real) :
    supportedFlowRadius pole initial Phi t ≤ R ↔
      ∀ (i : Fin 2) w, w ∈ (initial i).support → sphericalPoleRadius pole (Phi i t w) ≤ R := by
  have hl (i : Fin 2) : IsLUB
      ((fun w => sphericalPoleRadius pole (Phi i t w)) '' (initial i).support)
      (sSup ((fun w => sphericalPoleRadius pole (Phi i t w)) '' (initial i).support)) := by
    letI : IsProbabilityMeasure (initial i) := hprob i
    refine isLUB_csSup ((Measure.nonempty_support (IsProbabilityMeasure.ne_zero (initial i))).image _) ?_
    refine ⟨Real.pi,?_⟩
    rintro _ ⟨w,hw,rfl⟩
    exact sphericalDistance_le_pi _ _
  have hm (i : Fin 2) :
      sSup ((fun w => sphericalPoleRadius pole (Phi i t w)) '' (initial i).support) ≤
        supportedFlowRadius pole initial Phi t := by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  constructor
  · intro hb i w hw
    exact ((hl i).1 (mem_image_of_mem _ hw)).trans ((hm i).trans hb)
  · intro hb
    apply max_le
    · apply (hl 0).2
      rintro _ ⟨w,hw,rfl⟩
      exact hb 0 w hw
    · apply (hl 1).2
      rintro _ ⟨w,hw,rfl⟩
      exact hb 1 w hw

/-- Strict pointwise bounds become a strict exact maximum bound by compact
attainment; continuity is required only on the original closed supports. -/
theorem supportedFlowRadius_lt_iff {d : Nat} (pole : UnitSphere d)
    (initial : Fin 2 → Measure (UnitSphere d)) (hprob : ∀ i, IsProbabilityMeasure (initial i))
    (Phi : Fin 2 → Real → UnitSphere d → UnitSphere d) (t : Real)
    (hspace : ∀ i, ContinuousOn (Phi i t) (initial i).support) (cap : Real) :
    supportedFlowRadius pole initial Phi t < cap ↔
      ∀ (i : Fin 2) w, w ∈ (initial i).support → sphericalPoleRadius pole (Phi i t w) < cap := by
  have he (i : Fin 2) :
      sSup ((fun w => sphericalPoleRadius pole (Phi i t w)) '' (initial i).support) < cap ↔
        ∀ w ∈ (initial i).support, sphericalPoleRadius pole (Phi i t w) < cap := by
    letI : IsProbabilityMeasure (initial i) := hprob i
    exact (Measure.isClosed_support (μ := initial i)).isCompact.sSup_lt_iff_of_continuous
      (Measure.nonempty_support (IsProbabilityMeasure.ne_zero (initial i)))
      ((sphericalPoleRadius_continuous pole).comp_continuousOn (hspace i)) cap
  change max _ _ < cap ↔ _
  rw [max_lt_iff, he 0, he 1]
  constructor
  · rintro ⟨h0,h1⟩ i w hw
    fin_cases i
    · exact h0 w hw
    · exact h1 w hw
  · intro h
    exact ⟨h 0,h 1⟩

/-- The initial supported maximum is literally the source product support
supremum when the maps initially equal the identity on original supports. -/
theorem supportedFlowRadius_zero {d : Nat} (pole : UnitSphere d)
    (initial : Fin 2 → Measure (UnitSphere d))
    (Phi : Fin 2 → Real → UnitSphere d → UnitSphere d)
    (hid : ∀ i w, w ∈ (initial i).support → Phi i 0 w = w) :
    supportedFlowRadius pole initial Phi 0 = productSphericalSupportRadius pole initial := by
  have he (i : Fin 2) :
      (fun w => sphericalPoleRadius pole (Phi i 0 w)) '' (initial i).support =
        sphericalPoleRadius pole '' (initial i).support := by
    apply image_congr
    intro w hw
    rw [hid i w hw]
  simp only [supportedFlowRadius,productSphericalSupportRadius,sphericalSupportRadius,he]

/-- A proved uniform improvement on every good prefix gives all-time support
bounds for general supported jointly continuous maps. This is a conditional
topological adapter, not a statement that an actual global WGF has these inputs. -/
theorem supportedFlowRadius_continuation {d : Nat} (pole : UnitSphere d)
    (initial : Fin 2 → Measure (UnitSphere d)) (hprob : ∀ i, IsProbabilityMeasure (initial i))
    (Phi : Fin 2 → Real → UnitSphere d → UnitSphere d)
    (hjoint : ∀ i, ContinuousOn (fun tw : Real × UnitSphere d => Phi i tw.1 tw.2)
      ((Ici (0 : Real)) ×ˢ (initial i).support))
    (hid : ∀ i w, w ∈ (initial i).support → Phi i 0 w = w)
    (cap B : Real) (hinit : productSphericalSupportRadius pole initial < cap) (hB : B < cap)
    (hprefix : ∀ T : Real, 0 ≤ T →
      (∀ i w, w ∈ (initial i).support → ∀ t ∈ Icc (0 : Real) T,
        sphericalPoleRadius pole (Phi i t w) < cap) →
      ∀ i w, w ∈ (initial i).support → ∀ t ∈ Icc (0 : Real) T,
        sphericalPoleRadius pole (Phi i t w) ≤ B) :
    (∀ t : Real, 0 ≤ t → supportedFlowRadius pole initial Phi t < cap) ∧
    (∀ t : Real, 0 ≤ t → supportedFlowRadius pole initial Phi t ≤ B) ∧
    (∀ i w, w ∈ (initial i).support → ∀ t : Real, 0 ≤ t →
      sphericalPoleRadius pole (Phi i t w) ≤ B) := by
  have hspace (t : Real) (ht : 0 ≤ t) (i : Fin 2) :
      ContinuousOn (Phi i t) (initial i).support := by
    exact (hjoint i).comp (continuous_const.prodMk continuous_id).continuousOn
      (fun w hw => ⟨ht,hw⟩)
  have hzero : supportedFlowRadius pole initial Phi 0 < cap := by
    rw [supportedFlowRadius_zero pole initial Phi hid]
    exact hinit
  have hcont := scalar_cap_continuation
    (supportedFlowRadius_continuousOn pole initial Phi (Ici 0) hjoint) hzero hB
    (fun T hT hgood => by
      have hinside : ∀ i w, w ∈ (initial i).support → ∀ t ∈ Icc (0 : Real) T,
          sphericalPoleRadius pole (Phi i t w) < cap := by
        intro i w hw t ht
        exact (supportedFlowRadius_lt_iff pole initial hprob Phi t (hspace t ht.1) cap).mp
          (hgood t ht) i w hw
      intro t ht
      apply (supportedFlowRadius_le_iff pole initial hprob Phi t B).mpr
      intro i w hw
      exact hprefix T hT hinside i w hw t ht)
  exact ⟨hcont.1,hcont.2,fun i w hw t ht =>
    (supportedFlowRadius_le_iff pole initial hprob Phi t B).mp (hcont.2 t ht) i w hw⟩

/-- Measurable pushforwards inherit the complete closed-support bound from
the preceding conditional continuation, with no continuity outside the support. -/
theorem supportedFlowRadius_continuation_map_support {d : Nat} (pole : UnitSphere d)
    (initial : Fin 2 → Measure (UnitSphere d)) (hprob : ∀ i, IsProbabilityMeasure (initial i))
    (Phi : Fin 2 → Real → UnitSphere d → UnitSphere d)
    (hjoint : ∀ i, ContinuousOn (fun tw : Real × UnitSphere d => Phi i tw.1 tw.2)
      ((Ici (0 : Real)) ×ˢ (initial i).support))
    (hid : ∀ i w, w ∈ (initial i).support → Phi i 0 w = w)
    (hm : ∀ (i : Fin 2) (t : Real), 0 ≤ t → Measurable (Phi i t))
    (cap B : Real) (hinit : productSphericalSupportRadius pole initial < cap) (hB : B < cap)
    (hprefix : ∀ T : Real, 0 ≤ T →
      (∀ i w, w ∈ (initial i).support → ∀ t ∈ Icc (0 : Real) T,
        sphericalPoleRadius pole (Phi i t w) < cap) →
      ∀ i w, w ∈ (initial i).support → ∀ t ∈ Icc (0 : Real) T,
        sphericalPoleRadius pole (Phi i t w) ≤ B) :
    ∀ (i : Fin 2) (t : Real), 0 ≤ t →
      ((initial i).map (Phi i t)).support ⊆ {w | sphericalPoleRadius pole w ≤ B} := by
  have hp := (supportedFlowRadius_continuation pole initial hprob Phi hjoint hid cap B hinit hB hprefix).2.2
  intro i t ht
  exact sphericalPoleRadius_support_map_le pole (initial i) (Phi i t) (hm i t ht) B
    (fun w hw => hp i w hw t ht)

/-- Original cap probabilities, supported joint continuity, and the proved
prefix improvement give the complete pushed cap classes at every time,
including both exact half masses. These remain explicit abstract map inputs. -/
theorem supportedFlowRadius_continuation_map_caps {d : Nat} (pole : UnitSphere d)
    (r : Real) (initial : Fin 2 → Measure (UnitSphere d))
    (hcap : ∀ i, TwoCapClass pole r (initial i))
    (Phi : Fin 2 → Real → UnitSphere d → UnitSphere d)
    (hjoint : ∀ i, ContinuousOn (fun tw : Real × UnitSphere d => Phi i tw.1 tw.2)
      ((Ici (0 : Real)) ×ˢ (initial i).support))
    (hid : ∀ i w, w ∈ (initial i).support → Phi i 0 w = w)
    (hm : ∀ (i : Fin 2) (t : Real), 0 ≤ t → Measurable (Phi i t))
    (B : Real) (hB : B < r)
    (hprefix : ∀ T : Real, 0 ≤ T →
      (∀ i w, w ∈ (initial i).support → ∀ t ∈ Icc (0 : Real) T,
        sphericalPoleRadius pole (Phi i t w) < r) →
      ∀ i w, w ∈ (initial i).support → ∀ t ∈ Icc (0 : Real) T,
        sphericalPoleRadius pole (Phi i t w) ≤ B) :
    ∀ (i : Fin 2) (t : Real), 0 ≤ t → TwoCapClass pole r ((initial i).map (Phi i t)) := by
  have hp := (supportedFlowRadius_continuation pole initial (fun i => (hcap i).probability)
    Phi hjoint hid r B (productSphericalSupportRadius_cap_properties pole r initial hcap).2.1
      hB hprefix).2.2
  intro i t ht
  refine (hcap i).map_of_continuous_paths (Phi i) t ht (hid i) ?_ ?_ t ⟨ht,le_rfl⟩ (hm i t ht) ?_
  · intro w hw
    exact (hjoint i).comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs.1,hw⟩)
  · intro w hw s hs
    have hb := (hp i w hw s hs.1).trans_lt hB
    rcases assignedPole_mem pole (Phi i s w) with hpos | hneg
    · left
      simpa only [sphericalPoleRadius,sphericalCap,Set.mem_setOf_eq,hpos] using hb
    · right
      simpa only [sphericalPoleRadius,sphericalCap,Set.mem_setOf_eq,hneg] using hb
  · exact (hjoint i).comp (continuous_const.prodMk continuous_id).continuousOn
      (fun w hw => ⟨ht,hw⟩)

end PaperFormalization.MatrixFactorization
